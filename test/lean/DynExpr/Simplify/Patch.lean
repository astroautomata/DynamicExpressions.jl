import DynExpr.Simplify.SimplifyTree
import DynExpr.Simplify.CombineSpec

/-!
Model of `src/PatchMethods.jl`: `combine_operators!` and `simplify_tree!` on
`Expression` and `ParametricExpression`, which apply the tree-level function
to `get_contents(ex)` with `get_operators(ex, operators)` and rebuild the
wrapper with `with_contents` (src/Expression.jl:214-216, 252-256;
src/ParametricExpression.jl:199-203).
-/

namespace DynExpr.Simplify

open DynExpr

/-- Wrapper type: `Expression` (tree of `Node{T,2}`) or `ParametricExpression`
(tree of `ParametricNode{T,2}`). -/
inductive ExKind where
  | expression
  | parametric
  deriving DecidableEq, Repr

/-- An expression wrapper: its contents (root object) and its metadata
operators; `other` stands for the remaining metadata fields. -/
structure Ex (T M : Type) where
  kind : ExKind
  tree : Addr
  operators : CEnum T
  other : M

variable {T M : Type} [Add T] [Mul T] [Sub T]

/-- `combine_operators!(ex, operators=nothing)` (src/PatchMethods.jl:11-18).
Both `Node{T,2}` contents (`Expression`) and `ParametricNode{T,2}`
contents (`ParametricExpression`) reach the same tree method
(src/Simplify.jl:32-126), so the rewrite does not depend on `ex.kind`. -/
def patchCombine (ex : Ex T M) (operators : Option (CEnum T)) (fuel : Nat) (g : Graph T) :
    Jl (Ex T M × Graph T) := do
  let (r, g) ← combineOps (operators.getD ex.operators) fuel g ex.tree
  pure ({ ex with tree := r }, g)

/-- The deprecated `combine_operators(ex)` and `combine_operators(ex, operators)`
(src/Simplify.jl:128-129): `Base.@deprecate` forwards them to
`combine_operators!(ex)` and `combine_operators!(ex, operators)`; the
deprecation warning is not modelled. -/
def patchCombineDeprecated (ex : Ex T M) (operators : Option (CEnum T)) (fuel : Nat)
    (g : Graph T) : Jl (Ex T M × Graph T) :=
  patchCombine ex operators fuel g

/-- `simplify_tree!(ex, operators=nothing)` (src/PatchMethods.jl:19-24). Both
`Node` and `ParametricNode` contents use the generic `simplify_tree!`; a
parameter leaf is a non-constant leaf. -/
def patchSimplify [JlValue T] [Inhabited T] (ex : Ex T M) (operators : Option (CEnum T))
    (fuel : Nat) (g : Graph T) : Jl (Ex T M × Graph T) := do
  let (r, g) ← simplifyTree (operators.getD ex.operators).toOpEnum fuel g ex.tree
  pure ({ ex with tree := r }, g)

/-! ## Properties -/

/-- For an `Expression` with alias-free, well-formed contents, the wrapper
succeeds, keeps the kind and all metadata (including the stored operators when
explicit operators are passed), and its contents unfold to the
`combine_operators!` specification for the resolved operators, alias-free. -/
def patch_combine_expression : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] (ex : Ex T M) (operators : Option (CEnum T))
    (nf fuel : Nat) (g : Graph T) (t : Tree T), ex.kind = .expression →
    g.unfold fuel ex.tree = some t → t.WF 2 (operators.getD ex.operators).nops nf →
    Graph.NoAlias g ex.tree →
    ∃ e g', patchCombine ex operators fuel g = .ok (e, g') ∧
      e.kind = ex.kind ∧ e.operators = ex.operators ∧ e.other = ex.other ∧
      g'.unfold fuel e.tree = some (combinePure (operators.getD ex.operators) t) ∧
      Graph.NoAlias g' e.tree

/-- For both wrappers, `simplify_tree!` succeeds on a well-formed contents tree,
equals the tree-level function with the resolved operators, and returns the
same contents root and all metadata. -/
def patch_simplify : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] [JlValue T] [Inhabited T] (ex : Ex T M)
    (operators : Option (CEnum T)) (D nf fuel : Nat) (g : Graph T) (t : Tree T),
    g.unfold fuel ex.tree = some t →
    t.WF D (operators.getD ex.operators).toOpEnum.nops nf →
    ∃ g', simplifyTree (operators.getD ex.operators).toOpEnum fuel g ex.tree = .ok (ex.tree, g') ∧
      patchSimplify ex operators fuel g = .ok (ex, g')

/-- `combine_operators!` on a `ParametricExpression` applies the same rewrites as
on an `Expression` with the same tree and operators (the wrapper is declared
for both types). -/
def patch_combine_parametric : Prop :=
  ∀ (ex : Ex JF Unit) (fuel : Nat) (g : Graph JF) (t : Tree JF),
    ex.kind = .parametric → g.unfold fuel ex.tree = some t →
    t.WF 2 ex.operators.nops 1 → Graph.NoAlias g ex.tree →
    ∃ e1 g1 e2 g2 t1, patchCombine ex none fuel g = .ok (e1, g1) ∧
      patchCombine { ex with kind := .expression } none fuel g = .ok (e2, g2) ∧
      g2.unfold fuel e2.tree = some t1 ∧ g1.unfold fuel e1.tree = some t1

/-- For a `ParametricExpression` with alias-free, well-formed contents, the
wrapper succeeds, keeps the kind and all metadata (including the stored
operators when explicit operators are passed), and its contents unfold to the
`combine_operators!` specification for the resolved operators, alias-free. -/
def patch_combine_parametric_spec : Prop :=
  ∀ (T M : Type) [Add T] [Mul T] [Sub T] (ex : Ex T M) (operators : Option (CEnum T))
    (nf fuel : Nat) (g : Graph T) (t : Tree T), ex.kind = .parametric →
    g.unfold fuel ex.tree = some t → t.WF 2 (operators.getD ex.operators).nops nf →
    Graph.NoAlias g ex.tree →
    ∃ e g', patchCombine ex operators fuel g = .ok (e, g') ∧
      e.kind = ex.kind ∧ e.operators = ex.operators ∧ e.other = ex.other ∧
      g'.unfold fuel e.tree = some (combinePure (operators.getD ex.operators) t) ∧
      Graph.NoAlias g' e.tree

/-- `combine_operators!` mutates its argument in place, as its `!` name says,
and the deprecated `combine_operators` forwards to it:
1. the deprecated tree and wrapper methods (src/Simplify.jl:128-129) return
   exactly what `combine_operators!` returns, heap included, on every input;
2. on alias-free well-formed inputs `combine_operators!` returns the combined
   tree and writes only to objects of the input tree;
3. the mutation is visible: on some input the object passed in afterwards
   denotes a different value, so callers must use the returned tree. -/
def combine_mutates_in_place : Prop :=
  (∀ (T M : Type) [Add T] [Mul T] [Sub T] (o : CEnum T) (fuel : Nat) (g : Graph T)
      (tree : Addr) (ex : Ex T M) (operators : Option (CEnum T)),
    combineOperatorsDeprecated o fuel g tree = combineOps o fuel g tree ∧
      patchCombineDeprecated ex operators fuel g = patchCombine ex operators fuel g) ∧
  (∀ (T : Type) [Add T] [Mul T] [Sub T] (o : CEnum T) (nf fuel : Nat) (g : Graph T)
      (tree : Addr) (t : Tree T),
    g.unfold fuel tree = some t → t.WF 2 o.nops nf → Graph.NoAlias g tree →
    ∃ r g', combineOps o fuel g tree = .ok (r, g') ∧
      g'.unfold fuel r = some (combinePure o t) ∧
      ∀ x, ¬ Graph.Reachable g tree x → g'.cells x = g.cells x) ∧
  (∃ (o : CEnum JF) (fuel : Nat) (g : Graph JF) (tree : Addr) (t : Tree JF) (r : Addr)
      (g' : Graph JF) (t0 : Tree JF) (x : Nat → Option JF),
    g.unfold fuel tree = some t ∧ t.WF 2 o.nops 1 ∧ Graph.NoAlias g tree ∧
      combineOps o fuel g tree = .ok (r, g') ∧ g'.unfold fuel tree = some t0 ∧
      t0.denote o.toOpEnum x ≠ t.denote o.toOpEnum x)

end DynExpr.Simplify
