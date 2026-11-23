import DynExpr.NoAlias.Operators

/-!
Node creation by `parse_expression` (`src/Parse.jl:379-607`) and by the
`Expression` operator methods of `@declare_expression_operator`
(`src/ExpressionAlgebra.jl:13-82`), on the NodeBase heap.
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

/-! ## `parse_expression` -/

/-- The parts of a Julia expression that decide which node objects the parser
creates (`src/Parse.jl:379-607`): a call of an operator found in
`operators[degree]` (lines 430-455; a broadcast call `f.(args...)` is first
rewritten to a call of the operator named `f.`, lines 389-394), a chained
`+`/`-`/`*` call with more than two arguments
(lines 458-510), a variable name (lines 585-600), a literal or
`eval_module` value (lines 412, 589, 604), or a pre-built node of the requested
node type, which `parse_leaf` returns unchanged since `convert(node_type, ex)`
is the identity on its own type (lines 602-603, `src/base.jl:538-540`; a node
of another type is converted to a fresh copy, which is not modelled here).
Calls of `evaluate_on` functions (lines 513-529) run user code and are not
modelled. -/
inductive PExpr (T : Type) where
  | call (op : Nat) (args : List (PExpr T))
  | chain (op : Nat) (args : List (PExpr T))
  | sym (feature : Nat)
  | lit (v : T)
  | node (a : Addr)

mutual
  /-- `_parse_expression` (`src/Parse.jl:379-565`) and `parse_leaf`
  (`src/Parse.jl:568-607`); `N` is the requested node type. Children are
  parsed left to right inside the tuple passed to `N(; op, children)`. -/
  def parseE (D : Nat) : PExpr T → SGraph T → Jl (Addr × SGraph T)
    | .call op args, g => do
      let (cs, g1) ← parseArgs D args g
      ctor g1 D false { op := some op, children := some cs }
    | .chain op (a1 :: a2 :: rest), g => do
      let (c1, g1) ← parseE D a1 g
      let (c2, g2) ← parseE D a2 g1
      let (inner, g3) ← ctor g2 D false { op := some op, children := some [c1, c2] }
      parseChain D op inner rest g3
    | .chain _ _, _ => throw (.argumentError "chained call needs more than two arguments")
    | .sym i, g => ctor g D false { feature := some i }
    | .lit v, g => ctor g D false { val := some v }
    | .node a, g => pure (a, g)
  /-- `map(arg -> _parse_expression(arg, ...), (args[2:end]...,))`. -/
  def parseArgs (D : Nat) : List (PExpr T) → SGraph T → Jl (List Addr × SGraph T)
    | [], g => pure ([], g)
    | e :: es, g => do
      let (c, g1) ← parseE D e g
      let (cs, g2) ← parseArgs D es g1
      pure (c :: cs, g2)
  /-- The loop `for arg in args[4:end]` of `src/Parse.jl:492-510`. -/
  def parseChain (D : Nat) (op : Nat) : Addr → List (PExpr T) → SGraph T → Jl (Addr × SGraph T)
    | inner, [], g => pure (inner, g)
    | inner, e :: es, g => do
      let (c, g1) ← parseE D e g
      let (n, g2) ← ctor g1 D false { op := some op, children := some [inner, c] }
      parseChain D op n es g2
end

mutual
  /-- Pre-built nodes occurring in the expression, in order. -/
  def leaves : PExpr T → List Addr
    | .call _ args => leavesL args
    | .chain _ args => leavesL args
    | .sym _ => []
    | .lit _ => []
    | .node a => [a]
  def leavesL : List (PExpr T) → List Addr
    | [] => []
    | e :: es => leaves e ++ leavesL es
end

mutual
  /-- Expressions the parser turns into nodes without error: every operator
  index fits `UInt8` (`src/Node.jl:407`), a call has at most `D` arguments,
  a chained call has at least two arguments and `D ≥ 2`, and every variable
  index fits `UInt16` (`src/Node.jl:399`). -/
  def PExpr.Valid (D : Nat) : PExpr T → Prop
    | .call op args => op ≤ 255 ∧ args.length ≤ D ∧ PExpr.ValidL D args
    | .chain op args => op ≤ 255 ∧ 2 ≤ D ∧ 2 ≤ args.length ∧ PExpr.ValidL D args
    | .sym i => i ≤ 65535
    | .lit _ => True
    | .node _ => True
  /-- Every expression of the list is valid. -/
  def PExpr.ValidL (D : Nat) : List (PExpr T) → Prop
    | [] => True
    | e :: es => e.Valid D ∧ PExpr.ValidL D es
end

theorem trees_sub {g : Graph T} {l l' : List Addr} (h : Trees g l') (hs : ∀ a ∈ l, a ∈ l') :
    Trees g l := fun b hb => h b (hs b hb)

mutual
  theorem parseE_ok (D : Nat) : ∀ (e : PExpr T) (g : SGraph T),
      e.Valid D → Trees g.view (leaves e) → PairDisj g.view (leaves e) →
      ∃ r g', parseE D e g = .ok (r, g') ∧ Built g g' (leaves e) r
    | .call op args, g, hv, ht, hp => by
      simp only [PExpr.Valid] at hv
      obtain ⟨hop, hlen, hva⟩ := hv
      obtain ⟨cs, g1, h1, hcl, hi⟩ := parseArgs_ok D args g g [] [] hva (inv_nil g)
        (by simpa [leaves] using ht) (by simpa [leaves] using hp)
      simp only [List.nil_append] at hi
      obtain ⟨⟨n, g'⟩, hc⟩ := ctor_op_ok g1 D false op cs hop (by omega)
      refine ⟨n, g', ?_, by simpa [leaves] using built_ctor_inv hi rfl hc⟩
      simp only [parseE, h1, bind, Except.bind]
      exact hc
    | .chain op (a1 :: a2 :: rest), g, hv, ht, hp => by
      simp only [PExpr.Valid, PExpr.ValidL] at hv
      obtain ⟨hop, hD, -, hv1, hv2, hvr⟩ := hv
      have hl : leaves (.chain op (a1 :: a2 :: rest) : PExpr T) =
          leaves a1 ++ leaves a2 ++ leavesL rest := by simp [leaves, leavesL]
      rw [hl] at ht hp ⊢
      have hpa := pairDisj_append hp
      have hpb := pairDisj_append hpa.1
      have hta := trees_append.mp ht
      have htb := trees_append.mp hta.1
      obtain ⟨c1, g1, h1, b1⟩ := parseE_ok D a1 g hv1 htb.1 hpb.1
      have i1 : Inv g g1 (leaves a1) [c1] := by
        simpa using inv_step (inv_nil g) b1 htb.1 (fun _ h => absurd h List.not_mem_nil)
      obtain ⟨c2, g2, h2, b2⟩ := parseE_ok D a2 g1 hv2 (trees_ext i1.ext htb.2)
        (pairDisj_ext i1.ext htb.2 hpb.2.1)
      have i2 := inv_step i1 b2 htb.2 hpb.2.2
      obtain ⟨⟨inner, g3⟩, h3⟩ := ctor_op_ok g2 D false op [c1, c2] hop (by simpa using hD)
      have b3 : Built g g3 (leaves a1 ++ leaves a2) inner := built_ctor_inv i2 rfl h3
      obtain ⟨r, g', hr, br⟩ :=
        parseChain_ok D op rest g g3 (leaves a1 ++ leaves a2) inner hop hD hvr b3 ht hp
      refine ⟨r, g', ?_, br⟩
      simp only [parseE, h1, h2, h3, bind, Except.bind]
      exact hr
    | .chain _ [], _, hv, _, _ => by
      simp [PExpr.Valid] at hv
    | .chain _ [_], _, hv, _, _ => by
      simp [PExpr.Valid] at hv
    | .sym i, g, hv, _, _ => by
      simp only [PExpr.Valid] at hv
      obtain ⟨⟨n, g'⟩, hc⟩ := ctor_feature_ok g D false i hv
      exact ⟨n, g', hc, (ctor_built (kw := { feature := some i }) (trees_nil _) (pairDisj_nil _) hc).2⟩
    | .lit v, g, _, _, _ => by
      obtain ⟨⟨n, g'⟩, hc⟩ := ctor_val_ok g D false v
      exact ⟨n, g', hc, built_val _ hc⟩
    | .node a, g, _, ht, _ => ⟨a, g, rfl, built_input ht⟩
  theorem parseArgs_ok (D : Nat) : ∀ (es : List (PExpr T)) (g0 h : SGraph T) (ins rs : List Addr),
      PExpr.ValidL D es → Inv g0 h ins rs → Trees g0.view (ins ++ leavesL es) →
      PairDisj g0.view (ins ++ leavesL es) →
      ∃ cs h', parseArgs D es h = .ok (cs, h') ∧ cs.length = es.length ∧
        Inv g0 h' (ins ++ leavesL es) (rs ++ cs)
    | [], g0, h, ins, rs, _, hi, _, _ => ⟨[], h, rfl, rfl, by simpa [leavesL] using hi⟩
    | e :: es, g0, h, ins, rs, hv, hi, ht, hp => by
      simp only [PExpr.ValidL] at hv
      obtain ⟨hve, hves⟩ := hv
      have hl : leavesL (e :: es) = leaves e ++ leavesL es := rfl
      rw [hl] at ht hp ⊢
      have hpa := pairDisj_append (l := ins) (l' := leaves e ++ leavesL es) hp
      have hta := trees_append.mp ht
      have hte := trees_append.mp hta.2
      have hpe := pairDisj_append hpa.2.1
      obtain ⟨c, h1, he, b⟩ := parseE_ok D e h hve (trees_ext hi.ext hte.1)
        (pairDisj_ext hi.ext hte.1 hpe.1)
      have i1 := inv_step hi b hte.1 (fun x hx y hy => hpa.2.2 x hx y (List.mem_append_left _ hy))
      obtain ⟨cs, h2, hes, hlen, i2⟩ := parseArgs_ok D es g0 h1 (ins ++ leaves e) (rs ++ [c]) hves
        i1 (by simpa using ht) (by simpa using hp)
      refine ⟨c :: cs, h2, ?_, by simp [hlen], by simpa using i2⟩
      simp only [parseArgs, he, hes, bind, Except.bind, pure, Except.pure]
  theorem parseChain_ok (D op : Nat) : ∀ (es : List (PExpr T)) (g0 h : SGraph T)
      (ins : List Addr) (inner : Addr), op ≤ 255 → 2 ≤ D → PExpr.ValidL D es →
      Built g0 h ins inner → Trees g0.view (ins ++ leavesL es) → PairDisj g0.view (ins ++ leavesL es) →
      ∃ r h', parseChain D op inner es h = .ok (r, h') ∧ Built g0 h' (ins ++ leavesL es) r
    | [], g0, h, ins, inner, _, _, _, hb, _, _ => ⟨inner, h, rfl, by simpa [leavesL] using hb⟩
    | e :: es, g0, h, ins, inner, hop, hD, hv, hb, ht, hp => by
      simp only [PExpr.ValidL] at hv
      obtain ⟨hve, hves⟩ := hv
      have hl : leavesL (e :: es) = leaves e ++ leavesL es := rfl
      rw [hl] at ht hp ⊢
      have hpa := pairDisj_append (l := ins) (l' := leaves e ++ leavesL es) hp
      have hta := trees_append.mp ht
      have hte := trees_append.mp hta.2
      have hpe := pairDisj_append hpa.2.1
      have i0 : Inv g0 h ins [inner] := by
        simpa using inv_step (inv_nil g0) hb hta.1 (fun _ h => absurd h List.not_mem_nil)
      obtain ⟨c, h1, he, b⟩ := parseE_ok D e h hve (trees_ext i0.ext hte.1)
        (pairDisj_ext i0.ext hte.1 hpe.1)
      have i1 := inv_step i0 b hte.1 (fun x hx y hy => hpa.2.2 x hx y (List.mem_append_left _ hy))
      obtain ⟨⟨n, h2⟩, hn⟩ := ctor_op_ok h1 D false op [inner, c] hop (by simpa using hD)
      have bn : Built g0 h2 (ins ++ leaves e) n := built_ctor_inv i1 rfl hn
      obtain ⟨r, h', hc, br⟩ := parseChain_ok D op es g0 h2 (ins ++ leaves e) n hop hD hves bn
        (by simpa using ht) (by simpa using hp)
      refine ⟨r, h', ?_, by simpa using br⟩
      simp only [parseChain, he, hn, bind, Except.bind]
      exact hc
end

/-- `parse_expression` succeeds on every valid expression and returns an
alias-free tree when the pre-built nodes embedded in the expression are
alias-free, distinct and pairwise disjoint: every variable and literal gets its
own new leaf, and every operator call a new branch. -/
def parse_expression_noalias : Prop :=
  ∀ (T : Type) (D : Nat) (e : PExpr T) (g : SGraph T),
    e.Valid D → Trees g.view (leaves e) → PairDisj g.view (leaves e) →
    ∃ r g', parseE D e g = .ok (r, g') ∧ Built g g' (leaves e) r

theorem parse_expression_noalias_holds : parse_expression_noalias :=
  fun _ D e g hv ht hp => parseE_ok D e g hv ht hp

example : (PExpr.call 1 [.sym 1, .lit (3 : Nat)]).Valid 2 ∧
    Trees (oneLeaf : SGraph Nat).view (leaves (PExpr.call 1 [.sym 1, .lit (3 : Nat)])) ∧
    PairDisj (oneLeaf : SGraph Nat).view (leaves (PExpr.call 1 [.sym 1, .lit (3 : Nat)])) :=
  ⟨by simp [PExpr.Valid, PExpr.ValidL], trees_nil _, pairDisj_nil _⟩

/-! ## `Expression` operator methods -/

/-- An argument of an `Expression` operator method: an expression, represented
by its tree root (`get_contents`), or a scalar. -/
inductive EArg (T : Type) where
  | expr (tree : Addr)
  | scalar (v : T)

/-- Trees of the expression arguments. -/
def exprTrees : List (EArg T) → List Addr
  | [] => []
  | .expr a :: rest => a :: exprTrees rest
  | .scalar _ :: rest => exprTrees rest

/-- `map(exprs) do ... end` then `map(get_contents, _exprs)`
(`src/ExpressionAlgebra.jl:16-23`): each scalar becomes a new constant leaf
`constructorof(N)(T; val=expr)`; each expression contributes its live tree.
The temporary `copy(example_expr)` whose contents are immediately replaced is
not modelled: none of its objects is reachable from the result. -/
def exprArgs (D : Nat) : List (EArg T) → SGraph T → Jl (List Addr × SGraph T)
  | [], g => pure ([], g)
  | .expr a :: rest, g => do
    let (cs, g1) ← exprArgs D rest g
    pure (a :: cs, g1)
  | .scalar v :: rest, g => do
    let (k, g1) ← ctor g D false { val := some v }
    let (cs, g2) ← exprArgs D rest g1
    pure (k :: cs, g2)

/-- `insert_operator_index(op, exprs, example_expr)` (`src/ExpressionAlgebra.jl:13-26`):
the new tree `constructorof(N)(; children=trees, op)`. -/
def insertOp (g : SGraph T) (D idx : Nat) (args : List (EArg T)) : Jl (Addr × SGraph T) := do
  let (cs, g1) ← exprArgs D args g
  ctor g1 D false { op := some idx, children := some cs }

/-- `insert_operator_index` with the degree-`d` index, or `MissingOperatorError`
(`src/ExpressionAlgebra.jl:68-86`): the chained inner call `op(args[1:(end - 1)]...)`
on a prefix that contains an expression, dispatched to the declared
`Expression` method of that arity. -/
def lookupInsert (g : SGraph T) (D : Nat) (lookup : Nat → Option Nat) (d : Nat)
    (args : List (EArg T)) : Jl (Addr × SGraph T) :=
  match lookup d with
  | some idx => insertOp g D idx args
  | none => throw (.errorException "MissingOperatorError")

/-- The scalar arguments of a call, in order. -/
def scalarArgs : List (EArg T) → List T
  | [] => []
  | .expr _ :: rest => scalarArgs rest
  | .scalar v :: rest => v :: scalarArgs rest

/-- `apply_operator(op, args...)` (`src/ExpressionAlgebra.jl:61-88`) as called by
the methods of `@declare_expression_operator` (lines 92-155). `lookup d` is the
index of `op` among the degree-`d` operators. A missing chainable `+`/`*` with
more than two arguments computes `inner = op(args[1:(end - 1)]...)` (line 77):
when that prefix holds only scalars, Julia's own scalar method `scalarOp`
gives a scalar; otherwise the expression method applies the operator to the
prefix. The result is then combined with the last argument by the binary
operator (line 78, with the second call unfolded). -/
def applyOp (g : SGraph T) (D : Nat) (lookup : Nat → Option Nat) (chainable : Bool)
    (scalarOp : List T → T) (args : List (EArg T)) : Jl (Addr × SGraph T) :=
  match lookup args.length with
  | some idx => insertOp g D idx args
  | none =>
    if chainable && args.length > 2 then
      (if exprTrees args.dropLast = [] then
          pure (EArg.scalar (scalarOp (scalarArgs args.dropLast)), g)
        else (lookupInsert g D lookup (args.length - 1) args.dropLast) >>= fun p =>
          pure (EArg.expr p.1, p.2)) >>= fun (q : EArg T × SGraph T) =>
        match lookup 2, args.getLast? with
        | some idx2, some last => insertOp q.2 D idx2 [q.1, last]
        | _, _ => throw (.errorException "MissingOperatorError")
    else throw (.errorException "MissingOperatorError")

theorem exprArgs_ok {D : Nat} : ∀ (args : List (EArg T)) (g0 h : SGraph T) (ins rs : List Addr),
    Inv g0 h ins rs → Trees g0.view (ins ++ exprTrees args) → PairDisj g0.view (ins ++ exprTrees args) →
    ∃ cs h', exprArgs D args h = .ok (cs, h') ∧ cs.length = args.length ∧
      Inv g0 h' (ins ++ exprTrees args) (rs ++ cs)
  | [], _, h, _, _, hi, _, _ => ⟨[], h, rfl, rfl, by simpa [exprTrees] using hi⟩
  | .expr a :: rest, g0, h, ins, rs, hi, ht, hp => by
    have hl : exprTrees (EArg.expr a :: rest) = a :: exprTrees rest := rfl
    rw [hl] at ht hp ⊢
    have hta : Trees g0.view [a] := fun x hx => ht x (by simp at hx; simp [hx])
    have hpa := pairDisj_append (l := ins) (l' := a :: exprTrees rest) hp
    have i1 := inv_step hi (built_input (trees_ext hi.ext hta)) hta
      (fun x hx y hy => hpa.2.2 x hx y (by simp at hy; simp [hy]))
    obtain ⟨cs, h1, hr, hlen, i2⟩ := exprArgs_ok (D := D) rest g0 h (ins ++ [a]) (rs ++ [a]) i1
      (by simpa using ht) (by simpa using hp)
    refine ⟨a :: cs, h1, ?_, by simp [hlen], by simpa using i2⟩
    simp only [exprArgs, hr, bind, Except.bind, pure, Except.pure]
  | .scalar v :: rest, g0, h, ins, rs, hi, ht, hp => by
    obtain ⟨⟨k, h1⟩, hk⟩ := ctor_val_ok h D false v
    have hl : exprTrees (EArg.scalar v :: rest) = exprTrees rest := rfl
    rw [hl] at ht hp ⊢
    have i1 := inv_step hi (built_val (ins := []) hk) (trees_nil _)
      (fun _ _ _ h => absurd h List.not_mem_nil)
    obtain ⟨cs, h2, hr, hlen, i2⟩ := exprArgs_ok (D := D) rest g0 h1 (ins ++ []) (rs ++ [k]) i1
      (by simpa using ht) (by simpa using hp)
    refine ⟨k :: cs, h2, ?_, by simp [hlen], by simpa using i2⟩
    simp only [exprArgs, hk, hr, bind, Except.bind, pure, Except.pure]

theorem insertOp_ok {g : SGraph T} {D idx : Nat} {args : List (EArg T)}
    (hidx : idx ≤ 255) (hlen : args.length ≤ D)
    (ht : Trees g.view (exprTrees args)) (hp : PairDisj g.view (exprTrees args)) :
    ∃ n g', insertOp g D idx args = .ok (n, g') ∧ Built g g' (exprTrees args) n := by
  obtain ⟨cs, g1, h1, hcl, hi⟩ := exprArgs_ok (D := D) args g g [] [] (inv_nil g)
    (by simpa using ht) (by simpa using hp)
  simp only [List.nil_append] at hi
  obtain ⟨⟨n, g'⟩, hc⟩ := ctor_op_ok g1 D false idx cs hidx (by omega)
  refine ⟨n, g', ?_, built_ctor_inv hi rfl hc⟩
  simp only [insertOp, h1, bind, Except.bind]
  exact hc

theorem applyOp_found {g : SGraph T} {D idx : Nat} {lookup : Nat → Option Nat} {chainable : Bool}
    {scalarOp : List T → T} {args : List (EArg T)} (hl : lookup args.length = some idx) :
    applyOp g D lookup chainable scalarOp args = insertOp g D idx args := by
  simp only [applyOp, hl]
theorem exprTrees_dropLast_append :
    ∀ (args : List (EArg T)) (last : EArg T), args.getLast? = some last →
      exprTrees args = exprTrees args.dropLast ++ exprTrees [last] := by
  intro args
  induction args with
  | nil => intro last h; cases h
  | cons a rest ih =>
    intro last h
    cases rest with
    | nil =>
      simp at h; subst h
      cases a <;> simp [exprTrees]
    | cons b rest' =>
      have h' : (b :: rest').getLast? = some last := by simpa using h
      have := ih last h'
      cases a <;> simp [exprTrees, List.dropLast_cons_cons, this]

/-- The operator `applyOp` looks up for a call with `k` arguments exists
(`src/ExpressionAlgebra.jl:64-79`): either it is found among the degree-`k`
operators, or it is a chainable `+`/`*` with more than two arguments found
among the degree-`(k - 1)` and the binary operators. Found indices fit `UInt8`
and the degrees used are at most `D`. -/
def OpAvailable (D : Nat) (lookup : Nat → Option Nat) (chainable : Bool) (k : Nat) : Prop :=
  (∃ idx, lookup k = some idx ∧ idx ≤ 255 ∧ k ≤ D) ∨
  (lookup k = none ∧ chainable = true ∧ 2 < k ∧ (∃ i1, lookup (k - 1) = some i1 ∧ i1 ≤ 255) ∧
    (∃ i2, lookup 2 = some i2 ∧ i2 ≤ 255) ∧ k - 1 ≤ D)

/-- The operator methods on `Expression`s (`@declare_expression_operator`,
`src/ExpressionAlgebra.jl:12-179`) succeed whenever the operator is available
and build an alias-free tree when the argument expressions' trees are
alias-free, distinct and pairwise disjoint; scalar arguments become new leaves.
The result contains the argument trees themselves (Julia ownership: no copy). -/
def expression_operator_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (lookup : Nat → Option Nat) (chainable : Bool)
    (scalarOp : List T → T) (args : List (EArg T)),
    OpAvailable D lookup chainable args.length →
    Trees g.view (exprTrees args) → PairDisj g.view (exprTrees args) →
    ∃ n g', applyOp g D lookup chainable scalarOp args = .ok (n, g') ∧
      Built g g' (exprTrees args) n

/-- The final binary call `apply_operator(op, inner, args[end])` of a chain,
from a state whose invariant covers the prefix trees. -/
private theorem chain_last {g g1 : SGraph T} {D i2 : Nat} {inner : EArg T} {last : EArg T}
    {pre : List Addr} (hi2 : i2 ≤ 255) (hD : 2 ≤ D)
    (i1 : Inv g g1 pre (exprTrees [inner])) (hta : Trees g.view (exprTrees [last]))
    (hpa : ∀ x ∈ pre, ∀ y ∈ exprTrees [last], Disjoint g.view x y) :
    ∃ n g', insertOp g1 D i2 [inner, last] = .ok (n, g') ∧ Built g g' (pre ++ exprTrees [last]) n := by
  have hD' : [inner, last].length ≤ D := by simp; omega
  cases last with
  | expr a =>
    have hta1 : Trees g.view [a] := by simpa [exprTrees] using hta
    have i2' := inv_step i1 (built_input (trees_ext i1.ext hta1)) hta1
      (fun x hx y hy => hpa x hx y (by simpa [exprTrees] using hy))
    obtain ⟨n, g', h, b2⟩ := insertOp_ok (args := [inner, .expr a]) hi2 hD'
      (by cases inner <;> simpa [exprTrees] using i2'.trees)
      (by cases inner <;> simpa [exprTrees] using i2'.disj)
    exact ⟨n, g', h, by
      cases inner <;> simpa [exprTrees] using built_of_inv i2' (by simpa [exprTrees] using b2)⟩
  | scalar v =>
    obtain ⟨n, g', h, b2⟩ := insertOp_ok (args := [inner, .scalar v]) hi2 hD'
      (by cases inner <;> simpa [exprTrees] using i1.trees)
      (by cases inner <;> simpa [exprTrees] using i1.disj)
    exact ⟨n, g', h, by
      cases inner <;> simpa [exprTrees] using built_of_inv i1 (by simpa [exprTrees] using b2)⟩

theorem expression_operator_noalias_holds : expression_operator_noalias := by
  intro T g D lookup chainable scalarOp args hop ht hp
  rcases hop with ⟨idx, hl, hidx, hlen⟩ | ⟨hnone, hch, h2, ⟨i1, hl1, hi1⟩, ⟨i2, hl2, hi2⟩, hlen1⟩
  · obtain ⟨n, g', h, hb⟩ := insertOp_ok hidx hlen ht hp
    exact ⟨n, g', by rw [applyOp_found hl]; exact h, hb⟩
  · obtain ⟨last, hlast⟩ : ∃ last, args.getLast? = some last := by
      cases hg : args.getLast? with
      | none => rw [List.getLast?_eq_none_iff] at hg; subst hg; simp at h2
      | some last => exact ⟨last, rfl⟩
    have hsplit := exprTrees_dropLast_append args last hlast
    rw [hsplit] at ht hp
    have hpa := pairDisj_append hp
    have hta := trees_append.mp ht
    have hD : 2 ≤ D := by omega
    by_cases hpre : exprTrees args.dropLast = []
    · have happ : applyOp g D lookup chainable scalarOp args =
          insertOp g D i2 [.scalar (scalarOp (scalarArgs args.dropLast)), last] := by
        simp [applyOp, hnone, hch, h2, hpre, hl2, hlast, bind, Except.bind, pure, Except.pure]
      rw [happ, hsplit, hpre]
      have i0 : Inv g g [] (exprTrees [EArg.scalar (T := T) (scalarOp (scalarArgs args.dropLast))]) := by
        simpa [exprTrees] using inv_nil g
      simpa using chain_last hi2 hD i0 hta.2 (fun _ h => absurd h List.not_mem_nil)
    · obtain ⟨inner, g1, h1, b1⟩ := insertOp_ok (g := g) (D := D) (args := args.dropLast) hi1
        (by simpa using hlen1) hta.1 hpa.1
      have i1 : Inv g g1 (exprTrees args.dropLast) (exprTrees [EArg.expr (T := T) inner]) := by
        simpa [exprTrees] using inv_step (inv_nil g) b1 hta.1 (fun _ h => absurd h List.not_mem_nil)
      have happ : applyOp g D lookup chainable scalarOp args = insertOp g1 D i2 [.expr inner, last] := by
        simp [applyOp, hnone, hch, h2, hpre, lookupInsert, hl1, h1, hl2, hlast, bind, Except.bind,
          pure, Except.pure]
      rw [happ, hsplit]
      exact chain_last hi2 hD i1 hta.2 hpa.2.2

example : OpAvailable 2 (fun _ => some 1) false ([EArg.expr 0, .scalar (3 : Nat)]).length ∧
    Trees (oneLeaf : SGraph Nat).view (exprTrees [EArg.expr 0, .scalar (3 : Nat)]) ∧
    PairDisj (oneLeaf : SGraph Nat).view (exprTrees [EArg.expr 0, .scalar (3 : Nat)]) := by
  have ht : Trees (oneLeaf : SGraph Nat).view [0] := fun b hb => by
    simp at hb; subst hb; exact oneLeaf_tree
  exact ⟨Or.inl ⟨1, rfl, by decide, by decide⟩, ht, trees_single ht⟩

/-- Exposure (Julia ownership, not a copy): an `Expression` operator applied
to two expressions, when the binary operator is available, returns a new node
whose children are the two expressions' live trees
(`src/ExpressionAlgebra.jl:22-23`). -/
def expression_operator_stores_trees : Prop :=
  ∀ (T : Type) (g : SGraph T) (D idx : Nat) (lookup : Nat → Option Nat) (chainable : Bool)
    (scalarOp : List T → T) (a b : Addr),
    lookup 2 = some idx → idx ≤ 255 → 2 ≤ D →
    ∃ n g', applyOp g D lookup chainable scalarOp [.expr a, .expr b] = .ok (n, g') ∧
      kids g'.view n = some [a, b]

theorem expression_operator_stores_trees_holds : expression_operator_stores_trees := by
  intro T g D idx lookup chainable scalarOp a b hl hidx hD
  have hl' : lookup [EArg.expr (T := T) a, .expr b].length = some idx := hl
  obtain ⟨⟨n, g'⟩, hc⟩ := ctor_op_ok g D false idx [a, b] hidx (by simpa using hD)
  refine ⟨n, g', ?_, ?_⟩
  · rw [applyOp_found hl']
    simp only [insertOp, exprArgs, bind, Except.bind, pure, Except.pure]
    exact hc
  · obtain ⟨hn, -, -, c', hc', hact⟩ := ctor_ok hc
    rcases hact with ⟨hop, _⟩ | hkid
    · cases hop
    · rw [view_kids, hn, hc']; simp [hkid, ctorKids]

example : (fun _ : Nat => some 1) 2 = some 1 ∧ 1 ≤ 255 ∧ 2 ≤ 2 := ⟨rfl, by decide, by decide⟩

end DynExpr.NoAlias
