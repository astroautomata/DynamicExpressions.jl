import DynExpr.NodeUtils.Nodes

namespace DynExpr.NodeUtils

/-- Counter accounting for src/NodeUtils.jl:191-202; the bound restricts the
initial UInt16 state, while constant-count overflow remains represented. -/
theorem indexCounterAccounting (t : Tree Nat) : ∀ i, i < 65536 →
    (indexConstants t i).2 < 65536 ∧
    (indexConstants t i).2 = (i + countConstantNodes t) % 65536 := by
  induction t using Tree.induction with
  | hc v =>
      intro i hi
      simp only [indexConstants, countConstantNodes]
      exact ⟨Nat.mod_lt _ (by decide),trivial⟩
  | hf f =>
      intro i hi
      simp [indexConstants, countConstantNodes, Nat.mod_eq_of_lt hi, hi]
  | hb op cs ih =>
      have walk : ∀ ts : List (Tree Nat),
          (∀ t ∈ ts, ∀ i, i < 65536 → (indexConstants t i).2 < 65536 ∧
            (indexConstants t i).2 = (i + countConstantNodes t) % 65536) →
          ∀ i, i < 65536 → (indexForest ts i).2 < 65536 ∧
            (indexForest ts i).2 = (i + (ts.map countConstantNodes).sum) % 65536 := by
        intro ts ht
        induction ts with
        | nil => intro i hi; simp [indexForest, Nat.mod_eq_of_lt hi, hi]
        | cons c cs iht =>
            intro i hi
            obtain ⟨hj,he⟩ := ht c (by simp) i hi
            obtain ⟨hk,hkEq⟩ := iht (fun t h => ht t (by simp [h])) _ hj
            simp only [indexForest, List.map_cons, List.sum_cons]
            refine ⟨hk, ?_⟩
            rw [hkEq, he]
            simp [Nat.add_assoc, Nat.mod_add_mod]
      intro i hi
      simpa [indexConstants, countConstantNodes] using walk cs ih i hi

end DynExpr.NodeUtils
