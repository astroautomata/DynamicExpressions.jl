import DynExpr.Simplify.CombineProofs
import DynExpr.Simplify.JFLaws

/-! `combine_operators!` on the Float64-like scalar `JF`, including NaN and ±Inf. -/

namespace DynExpr.Simplify

open DynExpr

theorem combine_preserves_denote_jf_proof : combine_preserves_denote_jf := by
  intro o nf fuel g root t hu hw hna
  exact combine_preserves_denote_ring_proof JF jf_ringLaws o nf fuel g root t hu hw hna

/-- The hypotheses of the JF properties are satisfiable: `(x1 + 1) + 2`. -/
example : ∃ (o : CEnum JF) (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold 10 root = some t ∧ t.WF 2 o.nops 1 ∧ Graph.NoAlias g root := by
  let t : Tree JF := .branch 1 [.branch 1 [.feature 1, .const (.fin 1)], .const (.fin 2)]
  refine ⟨⟨[], [.plus]⟩, (Graph.ofTree (Heap.empty : Graph JF) t).2,
    (Graph.ofTree (Heap.empty : Graph JF) t).1, t, ?_, ?_, Graph.noAlias_ofTree _ _⟩
  · exact Graph.unfold_ofTree _ _ (by simp [t, Tree.Representable]) _ (by simp [t, Tree.depth])
  · simp [t, Tree.WF, CEnum.nops]

end DynExpr.Simplify
