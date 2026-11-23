import DynExpr.Simplify.HeapOps

/-!
Mirror of `simplify_tree!` and `combine_children!` (src/Simplify.jl:131-149)
for plain `Node` trees (`preserve_sharing = false`, src/Node.jl:343), whose
`tree_mapreduce` (src/base.jl:77-158) is an uncached post-order traversal.
Aliased subtrees are allowed: an aliased node is visited once per occurrence.
-/

namespace DynExpr.Simplify

open DynExpr

/-- `get_children(tree, Val(d))` (src/Node.jl:204-207): the first `d` active
children; poison slots raise `UndefRefError`. -/
def childrenOf (c : Cell T) : Jl (List Addr) :=
  if c.children.length < c.degree then throw .undefRefError
  else pure (c.children.take c.degree)

/-- `combine_children!(operators, p, c...)` (src/Simplify.jl:131-142).
The temporary node built by `constructorof(N)(T; val=...)` at line 126 is
unreachable after `set_node!` copies its fields (src/Node.jl:490-503), so it
is not allocated in the model. `set_node!` sets `degree = 0`,
`constant = true` and `val`; `op` and `feature` keep stale values. -/
def combineChildren [JlValue T] (o : OpEnum T) (g : Graph T) (p : Addr)
    (cs : List Addr) : Jl (Graph T) := do
  let cells ← cs.mapM g.read
  if !(cells.all cellConst) then return g
  let vals ← cs.mapM (valOf g)
  if !(vals.all JlValue.valid) then return g
  let pc ← g.read p
  -- `operators[degree][p.op]`: out-of-range degree or index is a `BoundsError`.
  let f ← match o.lookup cs.length pc.op with
    | some f => pure f
    | none => throw .boundsError
  let out := f vals
  if !(JlValue.valid out) then return g
  g.write p { pc with degree := 0, constant := true, val := some out, children := [] }

/-- `simplify_tree!(tree, operators)` (src/Simplify.jl:145-149) via
`tree_mapreduce(identity, combine_children!, tree)` without sharing
(src/base.jl:123-158): leaves map to themselves, branches recurse into the
children read before recursion from left to right, then call
`combine_children!` with the branch itself and the child results (each child
result is the child object, since `combine_children!` returns `p`). The
returned root is the input root. `fuel` bounds recursion depth; exhausting it
is a model artifact, never reached for inputs that unfold within `fuel`. -/
def simplifyTree [JlValue T] (o : OpEnum T) : Nat → Graph T → Addr → Jl (Addr × Graph T)
  | 0, _, _ => throw (.errorException "model recursion fuel exhausted")
  | fuel + 1, g, a => do
    let c ← g.read a
    if c.degree = 0 then return (a, g)
    let cs ← childrenOf c
    let (rs, g) ← cs.foldlM (fun (acc : List Addr × Graph T) ch => do
      let (r, g') ← simplifyTree o fuel acc.2 ch
      pure (acc.1 ++ [r], g')) ([], g)
    let g ← combineChildren o g a rs
    return (a, g)

/-- Constant value of a constant leaf. -/
def leafVal? : Tree T → Option T
  | .const v => some v
  | _ => none

/-- The folded value `combine_children!` would store for children `cs`
(src/Simplify.jl:134-138), if any. -/
def foldValue [JlValue T] (o : OpEnum T) (op : Nat) (cs : List (Tree T)) : Option T := do
  let vals ← cs.mapM leafVal?
  if !(vals.all JlValue.valid) then none
  let f ← o.lookup cs.length op
  let out := f vals
  if JlValue.valid out then some out else none

mutual
  /-- Specification: bottom-up constant folding of every branch whose
  children are valid constants and whose result is valid. -/
  def simplifyPure [JlValue T] (o : OpEnum T) : Tree T → Tree T
    | .const v => .const v
    | .feature i => .feature i
    | .branch op cs =>
      let cs' := simplifyForestPure o cs
      match foldValue o op cs' with
      | some v => .const v
      | none => .branch op cs'
  /-- Children of `simplifyPure`, left to right. -/
  def simplifyForestPure [JlValue T] (o : OpEnum T) : List (Tree T) → List (Tree T)
    | [] => []
    | c :: cs => simplifyPure o c :: simplifyForestPure o cs
end

mutual
  /-- A constant leaf with value `v` occurs in the tree. -/
  def HasConst (v : T) : Tree T → Prop
    | .const w => w = v
    | .feature _ => False
    | .branch _ cs => HasConstForest v cs
  /-- A constant leaf with value `v` occurs in one of the trees. -/
  def HasConstForest (v : T) : List (Tree T) → Prop
    | [] => False
    | c :: cs => HasConst v c ∨ HasConstForest v cs
end

mutual
  /-- A branch whose children are valid constants with a valid result occurs. -/
  def HasFoldable [JlValue T] (o : OpEnum T) : Tree T → Prop
    | .const _ | .feature _ => False
    | .branch op cs => (foldValue o op cs).isSome ∨ HasFoldableForest o cs
  /-- A foldable branch occurs in one of the trees. -/
  def HasFoldableForest [JlValue T] (o : OpEnum T) : List (Tree T) → Prop
    | [] => False
    | c :: cs => HasFoldable o c ∨ HasFoldableForest o cs
end

/-! ## Properties -/

/-- Mirror agrees with the specification: on any graph that unfolds within
`fuel` to a well-formed tree `t` (aliased subtrees allowed), `simplify_tree!`
succeeds, returns the same root, and the mutated graph unfolds to
`simplifyPure o t`. -/
def simplify_matches_spec : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some (simplifyPure o t)

/-- `simplify_tree!` preserves the denotation for every feature binding, with
arbitrary total operators, including on aliased `Node` trees. -/
def simplify_preserves_denote : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g' t', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some t' ∧ ∀ x, t'.denote o x = t.denote o x

/-- The result is well-formed for the same operator enum (valid operator
indices, degrees and features) and no deeper than the input. -/
def simplify_wf : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g' t', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some t' ∧ t'.WF D o.nops nf ∧ t'.depth ≤ t.depth

/-- No foldable branch remains: every branch whose children are all valid
constants and whose operator result is valid has been folded. -/
def simplify_fully_folds : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g' t', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some t' ∧ ¬ HasFoldable o t'

/-- Invalid values (NaN, Inf) are never produced by folding: every constant in
the result is valid or already occurred as a constant in the input. -/
def simplify_no_invalid_fold : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g' t', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some t' ∧
      ∀ v, HasConst v t' → JlValue.valid v = true ∨ HasConst v t

/-- Idempotence: simplifying the simplified graph again leaves its unfolded
tree unchanged. -/
def simplify_idempotent : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf →
    ∃ g' g'' t', simplifyTree o fuel g root = .ok (root, g') ∧
      g'.unfold fuel root = some t' ∧
      simplifyTree o fuel g' root = .ok (root, g'') ∧ g''.unfold fuel root = some t'

/-- `simplify_tree!` never creates node sharing: on an alias-free input the
mutated graph is still alias-free from the root. -/
def simplify_preserves_noalias : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (root : Addr)
    (t : Tree T), g.unfold fuel root = some t → t.WF D o.nops nf → Graph.NoAlias g root →
    ∃ g', simplifyTree o fuel g root = .ok (root, g') ∧ Graph.NoAlias g' root

end DynExpr.Simplify
