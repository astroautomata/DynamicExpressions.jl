import DynExpr.StringsParse.Companions
import DynExpr.StringsParse.GeneralDomain

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 400000

/-- A valid feature prints as its supplied name within the names vector and as
`x<i>` beyond it (src/Strings.jl:95-103). -/
theorem stringVariable_some (names : List String) {i : Nat} (hi : 1 ≤ i) :
    stringVariable i (some names) =
      if i ≤ names.length then names[i - 1]?.getD "" else "x" ++ toString i := by
  have hz : i ≠ 0 := by omega
  simp only [stringVariable, hz, ↓reduceIte]
  by_cases hl : i ≤ names.length
  · rw [if_pos hl, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [if_neg hl, List.getElem?_eq_none (by omega)]
    rfl

theorem fallback_inj {i j : Nat} (h : "x" ++ toString i = "x" ++ toString j) : i = j := by
  have hl := congrArg String.toList h
  simp only [String.toList_append] at hl
  have ht : (toString i).toList = (toString j).toList := List.append_cancel_left hl
  exact Nat.repr_injective (String.toList_inj.mp ht)

/-- Partial `variable_names` fall back to `x<i>` beyond the supplied names
(Q42). Supplied names print for indices within the names vector and `x<i>`
otherwise, and all valid features print distinctly when the supplied names are
unique and none spells the fallback of an index beyond them,
src/Strings.jl:95-103. -/
def FeaturesDistinct : Prop := ∀ (names : List String) (n i j : Nat),
  goodNames names = true → 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j →
  (∀ k, names.length < k → k ≤ n → ¬ ("x" ++ toString k) ∈ names) →
  stringVariable i (some names) =
      (if i ≤ names.length then names[i - 1]?.getD "" else "x" ++ toString i) ∧
    stringVariable i (some names) ≠ stringVariable j (some names)

theorem featuresDistinct : FeaturesDistinct := by
  intro names n i j hg hi hin hj hjn hij hfree
  have hnd : names.Nodup := by
    simp only [goodNames, Bool.and_eq_true, decide_eq_true_eq] at hg
    exact hg.1.2
  refine ⟨stringVariable_some names hi, fun he => hij ?_⟩
  by_cases hil : i ≤ names.length <;> by_cases hjl : j ≤ names.length
  · exact completeFeatureNames names i j hnd hi hil hj hjl he
  · rw [stringVariable_some names hi, stringVariable_some names hj, if_pos hil, if_neg hjl,
      List.getElem?_eq_getElem (by omega), Option.getD_some] at he
    exact absurd (he ▸ List.getElem_mem (by omega)) (hfree j (by omega) hjn)
  · rw [stringVariable_some names hi, stringVariable_some names hj, if_neg hil, if_pos hjl,
      List.getElem?_eq_getElem (by omega), Option.getD_some] at he
    exact absurd (he ▸ List.getElem_mem (by omega)) (hfree i (by omega) hin)
  · rw [stringVariable_some names hi, stringVariable_some names hj, if_neg hil, if_neg hjl] at he
    exact fallback_inj he

example : goodNames ["alpha"] = true ∧ (1 : Nat) ≤ 1 ∧ (1 : Nat) ≤ 2 ∧ (1 : Nat) ≤ 2 ∧
    (2 : Nat) ≤ 2 ∧ (1 : Nat) ≠ 2 ∧
    ∀ k, (["alpha"] : List String).length < k → k ≤ 2 → ¬ ("x" ++ toString k) ∈ ["alpha"] := by
  refine ⟨by decide +kernel, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro k hk hk2
  have : k = 2 := by simp at hk; omega
  subst this
  decide

/-- Every prebuilt node parses to the requested family with its tree unchanged
(`convert(node_type, ex)`, PR #232), src/Parse.jl:594-595. -/
def NodeTypeHonored : Prop := ∀ (cfg : ParseConfig) (source : String) (t : Tree Scalar),
  parseExpression cfg (.node source t) = .ok ⟨cfg.nodeType, t⟩

theorem nodeTypeHonored : NodeTypeHonored := by
  intro cfg source t
  unfold parseExpression normalize
  rfl

end DynExpr.StringsParse.General
