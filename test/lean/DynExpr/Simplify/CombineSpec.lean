import DynExpr.Simplify.Combine
import DynExpr.Simplify.Concrete

/-!
Pure specification of `combine_operators!` (src/Simplify.jl:32-126) on unshared
trees, and the property statements about the heap mirror `combineOps`.
-/

namespace DynExpr.Simplify

open DynExpr

/-- Operator counts per degree of a `CEnum` (unary, binary). -/
def CEnum.nops (o : CEnum T) (d : Nat) : Nat :=
  if d = 1 then o.una.length else if d = 2 then o.bin.length else 0

/-- Constant value of a constant leaf. -/
def cval? : Tree T → Option T
  | .const v => some v
  | _ => none

/-- `is_node_constant` on pure trees (src/NodeUtils.jl:36). -/
def isC (t : Tree T) : Bool := (cval? t).isSome

variable [Add T] [Mul T] [Sub T]

/-- Commutative block on pure trees (src/Simplify.jl:54-79); `l`, `r` are the
already combined children of a node with operator index `op`. -/
def commPure (op : Nat) (b : BinOp T) (l r : Tree T) : Tree T :=
  let (l, r) := if isC l then (r, l) else (l, r)
  match cval? r, l with
  | some k, .branch op2 [a, c] =>
    if op2 = op then
      match cval? a, cval? c with
      | some va, _ => .branch op2 [.const (b.eval va k), c]
      | none, some vc => .branch op2 [a, .const (b.eval vc k)]
      | none, none => .branch op [l, r]
    else .branch op [l, r]
  | _, _ => .branch op [l, r]

/-- Subtraction block on pure trees (src/Simplify.jl:85-123). -/
def subPure (op : Nat) (l r : Tree T) : Tree T :=
  match cval? l with
  | some vl =>
    match r with
    | .branch op2 [r1, r2] =>
      if op = op2 then
        match cval? r1, cval? r2 with
        | some v1, _ => .branch op [r2, .const (v1 - vl)]
        | none, some v2 => .branch op [.const (vl + v2), r1]
        | none, none => .branch op [l, r]
      else .branch op [l, r]
    | _ => .branch op [l, r]
  | none =>
    match cval? r, l with
    | some vr, .branch op2 [l1, l2] =>
      if op = op2 then
        match cval? l1, cval? l2 with
        | some v1, _ => .branch op [.const (v1 - vr), l2]
        | none, some v2 => .branch op [l1, .const (vr + v2)]
        | none, none => .branch op [l, r]
      else .branch op [l, r]
    | _, _ => .branch op [l, r]

/-- Local rewrite at a binary node with combined children (src/Simplify.jl:51-125). -/
def rewritePure (o : CEnum T) (op : Nat) (l r : Tree T) : Tree T :=
  let tlc := isC l || isC r
  if op = 0 then .branch op [l, r]
  else match o.bin[op - 1]? with
    | none => .branch op [l, r]
    | some b =>
      if b.isComm && tlc then commPure op b l r
      else if b.isSub && tlc then subPure op l r
      else .branch op [l, r]

/-- Specification of `combine_operators!` on unshared trees (src/Simplify.jl:32-126). -/
def combinePure (o : CEnum T) : Tree T → Tree T
  | .const v => .const v
  | .feature i => .feature i
  | .branch op [c] => .branch op [combinePure o c]
  | .branch op [c1, c2] => rewritePure o op (combinePure o c1) (combinePure o c2)
  | .branch op cs => .branch op cs

/-- The commutative block would replace the subtree root (`tree = below`,
src/Simplify.jl:68,73) at a binary node with combined children `l`, `r`. -/
def commReplacesAt (o : CEnum T) (op : Nat) (l r : Tree T) : Bool :=
  if op = 0 then false
  else match o.bin[op - 1]? with
    | none => false
    | some b =>
      if b.isComm && (isC l || isC r) then
        let (l, r) := if isC l then (r, l) else (l, r)
        match cval? r, l with
        | some _, .branch op2 [a, c] => op2 == op && (isC a || isC c)
        | _, _ => false
      else false

/-- `combine_operators!` replaces the root of the input tree: the root is a
`+`/`*` node with a constant operand whose other operand (after combining)
is the same operator with a constant child. This is decided by the input. -/
def commReplaces (o : CEnum T) : Tree T → Bool
  | .branch op [c1, c2] => commReplacesAt o op (combinePure o c1) (combinePure o c2)
  | _ => false

/-! ## Properties -/

/-- Mirror agrees with the specification on unshared inputs: for a graph with
no aliasing that unfolds within `fuel` to a well-formed binary tree,
`combine_operators!` succeeds and the returned root unfolds to `combinePure`. -/
def combine_matches_spec : Prop :=
  ∀ (T : Type) [Add T] [Mul T] [Sub T] (o : CEnum T) (nf fuel : Nat) (g : Graph T)
    (root : Addr) (t : Tree T),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    ∃ r g', combineOps o fuel g root = .ok (r, g') ∧
      g'.unfold fuel r = some (combinePure o t)

/-- Commutative-ring laws of `+`, `*`, `-` used by the rewrites. -/
structure RingLaws (T : Type) [Add T] [Mul T] [Sub T] [Neg T] : Prop where
  add_assoc : ∀ a b c : T, a + b + c = a + (b + c)
  add_comm : ∀ a b : T, a + b = b + a
  mul_assoc : ∀ a b c : T, a * b * c = a * (b * c)
  mul_comm : ∀ a b : T, a * b = b * a
  sub_eq : ∀ a b : T, a - b = a + -b
  neg_add : ∀ a b : T, -(a + b) = -a + -b
  neg_neg : ∀ a : T, - -a = a

/-- On unshared inputs, `combine_operators!` preserves the denotation whenever
`+`, `*`, `-` satisfy the commutative-ring laws; other operators are arbitrary. -/
def combine_preserves_denote_ring : Prop :=
  ∀ (T : Type) [Add T] [Mul T] [Sub T] [Neg T] [Inhabited T], RingLaws T →
    ∀ (o : CEnum T) (nf fuel : Nat) (g : Graph T) (root : Addr) (t : Tree T),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    ∃ r g' t', combineOps o fuel g root = .ok (r, g') ∧ g'.unfold fuel r = some t' ∧
      ∀ x, t'.denote o.toOpEnum x = t.denote o.toOpEnum x

/-- Default value used only for wrong-arity operator calls in `CEnum.toOpEnum`. -/
instance instInhabitedJFSimplify : Inhabited JF := ⟨.nan⟩

/-- On unshared Float64-like inputs, `combine_operators!` preserves the value at
every binding, including NaN and infinite constants and intermediates. -/
def combine_preserves_denote_jf : Prop :=
  ∀ (o : CEnum JF) (nf fuel : Nat) (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    ∃ r g' t', combineOps o fuel g root = .ok (r, g') ∧ g'.unfold fuel r = some t' ∧
      ∀ x, t'.denote o.toOpEnum x = t.denote o.toOpEnum x

/-- On unshared inputs the result is well-formed for the same enum (valid
operator indices) and has no more nodes than the input. -/
def combine_wf : Prop :=
  ∀ (T : Type) [Add T] [Mul T] [Sub T] (o : CEnum T) (nf fuel : Nat) (g : Graph T)
    (root : Addr) (t : Tree T),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    ∃ r g' t', combineOps o fuel g root = .ok (r, g') ∧ g'.unfold fuel r = some t' ∧
      t'.WF 2 o.nops nf ∧ t'.size ≤ t.size

/-- `combine_operators!` never creates node sharing: on an alias-free input the
returned tree is alias-free. -/
def combine_result_noalias : Prop :=
  ∀ (T : Type) [Add T] [Mul T] [Sub T] (o : CEnum T) (nf fuel : Nat) (g : Graph T)
    (root : Addr) (t : Tree T),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    ∃ r g', combineOps o fuel g root = .ok (r, g') ∧ Graph.NoAlias g' r

/-- On unshared Float64-like inputs whose root is not replaced by the
commutative block, the object passed to `combine_operators!` keeps its value
(the returned root is then the input root). -/
def combine_input_unchanged_unless_replaced : Prop :=
  ∀ (o : CEnum JF) (nf fuel : Nat) (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold fuel root = some t → t.WF 2 o.nops nf → Graph.NoAlias g root →
    commReplaces o t = false →
    ∃ r g' t0, combineOps o fuel g root = .ok (r, g') ∧ g'.unfold fuel root = some t0 ∧
      ∀ x, t0.denote o.toOpEnum x = t.denote o.toOpEnum x

end DynExpr.Simplify
