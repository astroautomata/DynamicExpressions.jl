import DynExpr.NodeBase.TreeOps

/-! Result type of `copy_node` (`src/base.jl:496-510`). -/

namespace DynExpr.NodeBase
open DynExpr

/-- `copy_node` on a well-formed plain `Node` returns a tree of the same type as
its input whenever every constant has a runtime type allowed by the declared
element type. -/
def copy_type : Prop :=
  ∀ (c : CType) (t : Tree Elt), c.kind = .node → 1 ≤ c.deg → DegLe c.deg t → t.Representable →
    (∀ vt ∈ constTypes t, isaElt vt c.elt) → copyType c t = .ok c

private theorem constTypes_go_mem {c : Tree Elt} {cs : List (Tree Elt)} (hc : c ∈ cs) {v : Elt}
    (hv : v ∈ constTypes c) : v ∈ constTypes.go cs := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [constTypes.go, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | h
    · exact Or.inl hv
    · exact Or.inr (ih h)

private theorem copyForest_same (c : CType) (cs : List (Tree Elt))
    (ih : ∀ t ∈ cs, copyType c t = .ok c) :
    copyType.copyForest c cs = .ok (cs.map (fun t => (c, maxNodeDeg t))) := by
  induction cs with
  | nil => rfl
  | cons t ts iht =>
    simp only [copyType.copyForest, ih t (by simp), iht (fun x hx => ih x (by simp [hx])),
      List.map_cons, bind, Except.bind, pure, Except.pure]

theorem copy_type_holds : copy_type := by
  intro c t hk hdeg hd hr hvt
  induction t using Tree.induction with
  | hc vt =>
    obtain ⟨k, e, d⟩ := c
    rfl
  | hf i =>
    obtain ⟨k, e, d⟩ := c
    rfl
  | hb o cs ih =>
    simp only [DegLe] at hd
    simp only [Tree.Representable] at hr
    have hcs : copyType.copyForest c cs = .ok (cs.map (fun t => (c, maxNodeDeg t))) :=
      copyForest_same c cs (fun t ht => ih t ht (hd.2 t ht) (hr.2 t ht)
        (fun v hv => hvt v (by simp only [constTypes]; exact constTypes_go_mem ht hv)))
    obtain ⟨k, e, d⟩ := c
    cases cs with
    | nil => simp at hr
    | cons t0 ts =>
      have hb := ctorBranchType_noelt k (some d) (⟨k, e, d⟩, maxNodeDeg t0)
        (ts.map (fun t => ((⟨k, e, d⟩ : CType), maxNodeDeg t))) d rfl
        (by simp only [List.length_map]; simpa using hd.1)
        (fun _ hx => by
          simp only [List.mem_cons, List.mem_map] at hx
          rcases hx with rfl | ⟨_, _, rfl⟩ <;> exact Or.inl (Nat.le_refl _))
      have hfold : ((ts.map (fun t => ((⟨k, e, d⟩ : CType), maxNodeDeg t))).map Prod.fst).foldl
          (fun x y => promoteElt x y.elt) e = e :=
        foldl_promote_same e _ (fun y hy => by
          simp only [List.map_map, List.mem_map, Function.comp_def] at hy
          obtain ⟨_, _, rfl⟩ := hy
          rfl)
      simp only [copyType, hcs, List.map_cons, bind, Except.bind, constructorOf]
      rw [hb, hfold]

/-- Companion of `copy_type` (implied by it since PR #243): with a concrete
element type (not the abstract `Real`), `copy_node` keeps the tree's type. -/
def copy_type_concrete : Prop :=
  ∀ (c : CType) (t : Tree Elt), c.kind = .node → 1 ≤ c.deg → DegLe c.deg t → t.Representable →
    (∀ vt ∈ constTypes t, isaElt vt c.elt) → c.elt ≠ .real → copyType c t = .ok c

theorem copy_type_concrete_holds : copy_type_concrete :=
  fun c t hk hdeg hd hr hvt _ => copy_type_holds c t hk hdeg hd hr hvt

example : DegLe 2 (Tree.feature 1 : Tree Elt) ∧ (Tree.feature 1 : Tree Elt).Representable ∧
    (∀ vt ∈ constTypes (Tree.feature 1), isaElt vt Elt.float64) := by
  simp [DegLe, Tree.Representable, constTypes]

end DynExpr.NodeBase
