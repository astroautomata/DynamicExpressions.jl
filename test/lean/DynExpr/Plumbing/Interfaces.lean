import DynExpr.NodeBase.TreeOps
import DynExpr.NodeBase.Heap
import DynExpr.Expressions.Wrapper

namespace DynExpr.Plumbing

/-- Observations exercised by `_check_tree_mapreduce` and `_check_equality`,
src/Interfaces.jl:249-250,284-289. The count traverses Julia's degree dispatch;
the `f_on_shared` callback added in PR #240 never fires on plain Node
(preserve_sharing = false). Equality recursively compares leaves and children.
Nat scalars have reflexive Julia equality. This property covers these checks,
not every mandatory check. -/
def builtinNodeChecks : Prop := ∀ D (t : Tree Nat),
  t.Representable → NodeBase.DegLe D t →
  NodeBase.countNodesT D t = t.size ∧
  NodeBase.eqT D (fun x y => decide (x = y)) t t = true

theorem builtinNodeChecks_proof : builtinNodeChecks := by
  intro D t hr hd
  refine ⟨(NodeBase.count_nodes_tree_holds Nat D t hd).1, ?_⟩
  exact (NodeBase.eq_tree_holds Nat D (fun x y => decide (x = y))
    (by intros; simp) t t hr hr hd hd).2 rfl

example : (Tree.branch 1 [Tree.const (1 : Nat), Tree.feature 1]).Representable ∧
    NodeBase.DegLe 2 (.branch 1 [.const (1 : Nat), .feature 1]) := by
  simp [Tree.Representable, NodeBase.DegLe]

/-- `get_contents`, `get_metadata`, `get_tree`, `with_contents`, `with_metadata`
checks in src/Interfaces.jl:70-103, against the public Expression mirrors.
Changing either input component changes its getter result while retaining the
other component. The metadata remains an arbitrary type, including heap handles.
This property covers reconstruction/getter checks for ordinary Expression. -/
def builtinExpressionChecks : Prop := ∀ (T M : Type)
    (ex : Expressions.Expression T M) (tree : Tree T) (metadata : M),
  Expressions.get_tree (Expressions.with_contents ex tree) = tree ∧
  Expressions.get_metadata (Expressions.with_contents ex tree) = Expressions.get_metadata ex ∧
  Expressions.get_contents (Expressions.with_metadata ex metadata) = Expressions.get_contents ex ∧
  Expressions.get_metadata (Expressions.with_metadata ex metadata) = metadata

theorem builtinExpressionChecks_proof : builtinExpressionChecks := by
  intro T M ex tree metadata
  have h := Expressions.components_proven T M ex tree metadata
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Assignment phase of `_check_set_node!`, src/Interfaces.jl:276-280.
Allocated initialized source/target objects and source-target separation are
input facts; success is a conclusion. `setNode` follows all leaf/branch paths,
including child-tuple copying and errors from uninitialized fields. -/
def assignmentCheck : Prop := ∀ (T : Type) (g : NodeBase.SGraph T)
    (D dst src : Nat) (old replacement : NodeBase.SCell T) (slots : List (Option Addr)),
  g.cells dst = some old → g.cells src = some replacement → slots.length = D →
  (replacement.degree = 0 → replacement.constant = true → replacement.val.isSome) →
  (replacement.degree ≠ 0 → replacement.slots = some slots) →
  (∀ a, Graph.Reachable g.view src a → a ≠ dst) →
  ∃ result, NodeBase.setNode g D dst src = .ok result ∧
    (∀ a, a ≠ dst → result.cells a = g.cells a) ∧
    ∀ fuel, result.view.unfold fuel dst = g.view.unfold fuel src

theorem assignmentCheck_proof : assignmentCheck := by
  intro T g D dst src old replacement slots hd hs hl hv hc hn
  obtain ⟨result, hset, hframe, _, _, htree⟩ :=
    NodeBase.set_node_holds T g D dst src old replacement slots hd hs hl hv hc hn
  exact ⟨result, hset, hframe, htree⟩

example : ∃ (g : NodeBase.SGraph Nat) (old replacement : NodeBase.SCell Nat),
    g.cells 0 = some old ∧ g.cells 1 = some replacement ∧
    replacement.degree = 0 ∧ replacement.constant = true ∧ replacement.val.isSome ∧
    (∀ a, Graph.Reachable g.view 1 a → a ≠ 0) := by
  let g : NodeBase.SGraph Nat :=
    ((Heap.empty.alloc { (NodeBase.blankCell : NodeBase.SCell Nat) with feature := 1 }).2.alloc
      { (NodeBase.blankCell : NodeBase.SCell Nat) with constant := true, val := some 3 }).2
  refine ⟨g, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro a ⟨p, hp⟩
  cases hp with
  | nil => decide
  | cons hc hi _ =>
    have hs : g.view.cells 1 =
      some (NodeBase.SCell.toCell { (NodeBase.blankCell : NodeBase.SCell Nat) with
        constant := true, val := some 3 }) := rfl
    rw [hs] at hc
    cases hc
    simp [NodeBase.SCell.toCell, NodeBase.SCell.active, NodeBase.blankCell] at hi

/-- Fixed optional registration exclusions, src/Interfaces.jl:211-215. -/
def parametricExclusions := ["count_constant_nodes", "index_constant_nodes", "has_constants"]
def parametricRegistration : Prop := parametricExclusions.length = 3 ∧
  ¬ "get_scalar_constants" ∈ parametricExclusions
theorem parametricRegistration_proof : parametricRegistration := by
  unfold parametricRegistration; decide

end DynExpr.Plumbing
