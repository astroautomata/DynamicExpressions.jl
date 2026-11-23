import DynExpr.Simplify.Patch
import DynExpr.Simplify.SimplifyProofs
import DynExpr.Simplify.CombineProofs
import DynExpr.Simplify.CombineBang

/-! Proofs about the `src/PatchMethods.jl` wrappers. -/

namespace DynExpr.Simplify

open DynExpr

theorem patch_simplify_proof : patch_simplify := by
  intro T M _ _ _ _ _ ex operators D nf fuel g t hu hw
  obtain ⟨g', hs, _⟩ :=
    simplify_matches_spec_proof T (operators.getD ex.operators).toOpEnum D nf fuel g ex.tree t hu hw
  refine ⟨g', hs, ?_⟩
  simp [patchSimplify, hs, bind, Except.bind, pure, Except.pure]

/-- Either wrapper on alias-free, well-formed contents: the shared tree method
succeeds and the wrapper keeps all metadata. -/
private theorem patch_combine_any {T M : Type} [Add T] [Mul T] [Sub T] (ex : Ex T M)
    (operators : Option (CEnum T)) {nf fuel : Nat} {g : Graph T} {t : Tree T}
    (hu : g.unfold fuel ex.tree = some t) (hw : t.WF 2 (operators.getD ex.operators).nops nf)
    (hna : Graph.NoAlias g ex.tree) :
    ∃ e g', patchCombine ex operators fuel g = .ok (e, g') ∧
      e.kind = ex.kind ∧ e.operators = ex.operators ∧ e.other = ex.other ∧
      g'.unfold fuel e.tree = some (combinePure (operators.getD ex.operators) t) ∧
      Graph.NoAlias g' e.tree := by
  obtain ⟨r, g', hc, hu'⟩ :=
    combine_matches_spec_proof T (operators.getD ex.operators) nf fuel g ex.tree t hu hw hna
  obtain ⟨r2, g2, hc2, hna2⟩ :=
    combine_result_noalias_proof T (operators.getD ex.operators) nf fuel g ex.tree t hu hw hna
  rw [hc] at hc2
  cases hc2
  refine ⟨{ ex with tree := r }, g', ?_, rfl, rfl, rfl, hu', hna2⟩
  simp [patchCombine, hc, bind, Except.bind, pure, Except.pure]

theorem patch_combine_expression_proof : patch_combine_expression := by
  intro T M _ _ _ ex operators nf fuel g t _ hu hw hna
  exact patch_combine_any ex operators hu hw hna

theorem patch_combine_parametric_spec_proof : patch_combine_parametric_spec := by
  intro T M _ _ _ ex operators nf fuel g t _ hu hw hna
  exact patch_combine_any ex operators hu hw hna

/-- Both wrappers run the same tree method on the same contents, so they
return the same contents root in the same heap. -/
theorem patch_combine_parametric_proof : patch_combine_parametric := by
  intro ex fuel g t _ hu hw hna
  obtain ⟨r, g', hc, hu'⟩ :=
    combine_matches_spec_proof JF ex.operators 1 fuel g ex.tree t hu hw hna
  refine ⟨{ ex with tree := r }, g', { ex with kind := .expression, tree := r }, g', _,
    ?_, ?_, hu', hu'⟩ <;>
    simp [patchCombine, hc, bind, Except.bind, pure, Except.pure]

/-- `x1 + 1` with operators `(+, -, *, /)`. -/
private def tX1p1 : Tree JF := .branch 1 [.feature 1, .const (.fin 1)]

/-- The hypotheses of `patch_combine_expression`, `patch_combine_parametric` and
`patch_combine_parametric_spec` are satisfiable (`x1 + 1`). -/
example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.nops 1 ∧ Graph.NoAlias g root := by
  refine ⟨(Graph.ofTree (Heap.empty : Graph JF) tX1p1).2,
    (Graph.ofTree (Heap.empty : Graph JF) tX1p1).1, tX1p1, ?_, ?_, Graph.noAlias_ofTree _ _⟩
  · exact Graph.unfold_ofTree _ _ (by simp [tX1p1, Tree.Representable]) _
      (by simp [tX1p1, Tree.depth])
  · simp [tX1p1, Tree.WF, CEnum.nops, opsPMTD]

/-- The hypotheses of `patch_simplify` are satisfiable. -/
example : ∃ (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 opsPMTD.toOpEnum.nops 1 := by
  refine ⟨(Graph.ofTree (Heap.empty : Graph JF) tX1p1).2,
    (Graph.ofTree (Heap.empty : Graph JF) tX1p1).1, tX1p1, ?_, ?_⟩
  · exact Graph.unfold_ofTree _ _ (by simp [tX1p1, Tree.Representable]) _
      (by simp [tX1p1, Tree.depth])
  · simp [tX1p1, Tree.WF, OpEnum.nops, CEnum.toOpEnum, opsPMTD]

end DynExpr.Simplify
