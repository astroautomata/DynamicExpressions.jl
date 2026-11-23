import DynExpr.Simplify.Patch
import DynExpr.Simplify.CombineProofs
import DynExpr.NoAlias.Combine

/-!
`combine_operators!` (src/Simplify.jl:32-126) mutates its argument in place and
the deprecated `combine_operators` (src/Simplify.jl:128-129) forwards to it.
The visible mutation is shown on `(x1 + 1.0) + 2.0` with operators
`(+, -, *, /)`, as in `OperatorEnum(2 => (+, -, *, /))`.
-/

namespace DynExpr.Simplify

open DynExpr

/-- `OperatorEnum(1 => (), 2 => (+, -, *, /))`. -/
def opsPMTD : CEnum JF := ⟨[], [.plus, .minus, .times, .other JF.div]⟩

/-- Binding `x1 = 3`. -/
def bindX3 : Nat → Option JF := fun i => if i = 1 then some (.fin 3) else none

/-- Value at `bindX3` of the tree a combine result points at (with `fuel` 10). -/
def valueAfter (r : Jl (Addr × Graph JF)) (useRoot : Option Addr) : Option JF :=
  match r with
  | .ok (a, g) => (g.unfold 10 (useRoot.getD a)).bind (denS opsPMTD.toOpEnum bindX3)
  | .error _ => none

theorem value_of_result {r : Jl (Addr × Graph JF)} {useRoot : Option Addr} {v : JF}
    (hv : valueAfter r useRoot = some v) {a : Addr} {g : Graph JF} {t : Tree JF}
    (hr : r = .ok (a, g)) (hu : g.unfold 10 (useRoot.getD a) = some t) :
    t.denote opsPMTD.toOpEnum bindX3 = some v := by
  subst hr
  simp only [valueAfter, hu, Option.bind_some] at hv
  rw [← denS_eq]
  exact hv

/-- `(x1 + 1) + 2` as a tree. -/
def tPlus12 : Tree JF := .branch 1 [.branch 1 [.feature 1, .const (.fin 1)], .const (.fin 2)]

theorem combine_mutates_in_place_proof : combine_mutates_in_place := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro T _ _ _ o nf fuel g tree t hu hw hna
    obtain ⟨r, g', hc, hun⟩ := combine_matches_spec_proof T o nf fuel g tree t hu hw hna
    obtain ⟨r2, g2, hc2, -, -, hframe⟩ :=
      NoAlias.combine_operators_noalias_holds T o nf fuel g tree t hu hw hna
    rw [hc] at hc2
    cases hc2
    exact ⟨r, g', hc, hun, hframe⟩
  · let g := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).2
    let root := (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1
    have hu : g.unfold 10 root = some tPlus12 :=
      Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
        (by simp [tPlus12, Tree.depth])
    have hw : tPlus12.WF 2 opsPMTD.nops 1 := by
      simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD]
    have hna : Graph.NoAlias g root := Graph.noAlias_ofTree _ _
    obtain ⟨r, g', hc, -⟩ := combine_matches_spec_proof JF opsPMTD 1 10 g root tPlus12 hu hw hna
    have hafter : valueAfter (combineOps opsPMTD 10 g root) (some root) = some (.fin 8) := by
      decide +kernel
    have hbefore : denS opsPMTD.toOpEnum bindX3 tPlus12 = some (.fin 6) := by decide +kernel
    cases hu0 : g'.unfold 10 root with
    | none =>
      rw [hc] at hafter
      simp [valueAfter, hu0] at hafter
    | some t0 =>
      have h8 := value_of_result (useRoot := some root) hafter hc hu0
      refine ⟨opsPMTD, 10, g, root, tPlus12, r, g', t0, bindX3, hu, hw, hna, hc, hu0, ?_⟩
      rw [h8, ← denS_eq, hbefore]
      intro h
      cases h

/-- The hypotheses of the second clause are satisfiable (`(x1 + 1) + 2`). -/
example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.nops 1 ∧ Graph.NoAlias g root :=
  ⟨(Graph.ofTree (Heap.empty : Graph JF) tPlus12).2,
    (Graph.ofTree (Heap.empty : Graph JF) tPlus12).1, tPlus12,
    Graph.unfold_ofTree _ _ (by simp [tPlus12, Tree.Representable]) _
      (by simp [tPlus12, Tree.depth]),
    by simp [tPlus12, Tree.WF, CEnum.nops, opsPMTD], Graph.noAlias_ofTree _ _⟩

end DynExpr.Simplify
