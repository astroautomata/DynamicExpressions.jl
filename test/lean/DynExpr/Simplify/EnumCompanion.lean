import DynExpr.Simplify.EnumProofs

/-! Companion properties for the refuted enum construction entries. -/

namespace DynExpr.Simplify

open DynExpr

theorem enum_pairs_keep_all_operators_distinct_proof : enum_pairs_keep_all_operators_distinct := by
  intro p ps hpos hnd
  obtain ⟨ops, hops, _, hat, _⟩ := enum_pairs_layout_proof p ps hpos hnd
  exact ⟨ops, hops, fun q hq f hf => ⟨q.2, hat q hq, hf⟩⟩

/-- The hypotheses are satisfiable: `OperatorEnum(1 => (sin,), 2 => (+,))`. -/
example : DegreesPos ((1, [Fn.plain 0]) :: [(2, [Fn.plain 1])]) ∧
    (((1, [Fn.plain 0]) :: [(2, [Fn.plain 1])]).map Prod.fst).Nodup := by
  refine ⟨?_, by decide⟩
  intro q hq
  simp at hq
  rcases hq with rfl | rfl <;> decide

end DynExpr.Simplify
