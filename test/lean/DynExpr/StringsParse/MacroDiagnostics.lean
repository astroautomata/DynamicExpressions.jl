import DynExpr.StringsParse.Properties

namespace DynExpr.StringsParse.Macro
set_option maxHeartbeats 200000

/-- The first rejected Symbol keyword lists exactly the non-deprecated keywords;
the omitted soft-deprecated operator-list keywords remain accepted,
src/Parse.jl:125-205. -/
def NondeprecatedDiagnostic : Prop := ∀ keys bad,
  keys.find? (fun key => !macroKeywords.contains key) = some bad →
  parseMacroKeywords keys =
    .error (.argumentError (macroKeywordDiagnostic bad
      ["operators", "variable_names", "node_type", "expression_type",
        "evaluate_on", "eval_module", "extra_metadata"])) ∧
  parseMacroKeywords ["binary_operators"] = .ok () ∧
  parseMacroKeywords ["unary_operators"] = .ok ()

theorem nondeprecatedDiagnostic : NondeprecatedDiagnostic := by
  intro keys bad h
  constructor
  · unfold parseMacroKeywords
    rw [h]
    rfl
  · decide +kernel

/-- Recognized keyword names and exactly one operator-source route,
src/Parse.jl:128-184,195-205. Interpolated values are supplied separately. -/
def ValidInput (keys : List String) : Prop :=
  (∀ key ∈ keys, key ∈ macroKeywords) ∧
  (keys.contains "operators" = true →
    keys.contains "binary_operators" = false ∧ keys.contains "unary_operators" = false) ∧
  (keys.contains "operators" = false →
    (keys.contains "binary_operators" || keys.contains "unary_operators") = true)

private theorem noInvalid (keys : List String) (h : ∀ key ∈ keys, key ∈ macroKeywords) :
    keys.find? (fun key => !macroKeywords.contains key) = none := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    have hk : macroKeywords.contains key = true := by simpa using h key (by simp)
    have ht : ∀ k ∈ keys, k ∈ macroKeywords := fun k hm => h k (by simp [hm])
    rw [List.find?_cons, hk]
    exact ih ht

/-- All recognized and consistent keyword lists pass macro validation,
src/Parse.jl:113-217. The invalid-name diagnostic trigger is excluded by input
names, with no success premise. -/
def ValidKeywords : Prop := ∀ keys, ValidInput keys → parseMacroKeywords keys = .ok ()

theorem validKeywords : ValidKeywords := by
  intro keys ⟨hn, hp, ha⟩
  unfold parseMacroKeywords
  rw [noInvalid keys hn]
  by_cases ho : keys.contains "operators" = true
  · obtain ⟨hb, hu⟩ := hp ho
    simp only [ho, hb, hu, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have hf : keys.contains "operators" = false := Bool.eq_false_iff.mpr ho
    have hs := ha hf
    simp only [hf, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl

example : ValidInput ["operators", "variable_names", "extra_metadata"] := by simp [ValidInput, macroKeywords]
example : ValidInput ["binary_operators", "unary_operators", "node_type"] := by simp [ValidInput, macroKeywords]

end DynExpr.StringsParse.Macro
