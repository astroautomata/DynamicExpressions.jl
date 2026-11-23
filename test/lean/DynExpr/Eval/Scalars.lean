import DynExpr.Eval.Core

/-!
The concrete scalar type for the evaluator properties: the shared IEEE-like
`JF` (exact finite arithmetic).
-/

namespace DynExpr.Eval

/-- `Float64` facts for the evaluator, with `JF` arithmetic. Uninitialised
storage is modelled as zero. -/
instance : JlScalar JF where
  valid := JF.valid
  zero := .fin 0
  one := .fin 1
  add := JF.add
  mul := JF.mul
  isNumber := true
  isFloat := true
  floatLike := true
  undef := .fin 0
  invalid? := some .nan

/-- Every array of finite `JF` values has a finite sum, and a non-finite
element makes the sum non-finite, so `is_valid_array` accepts exactly the
all-finite arrays. -/
theorem jf_foldl_valid (xs : List JF) (x : JF) :
    (xs.foldl JF.add x).valid = (x.valid && xs.all JF.valid) := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.all_cons, ih]
    cases x <;> cases y <;> simp [JF.add, JF.valid]

theorem jf_isValidArray (a : JVec JF) : isValidArray a = a.all JF.valid := by
  have hs : (jsum a).valid = a.all JF.valid := by
    rcases a with ⟨l⟩
    cases l with
    | nil => show (JF.fin 0).valid = _; simp [JF.valid]
    | cons x xs =>
      show (List.foldl JF.add x xs).valid = _
      rw [jf_foldl_valid]
      simp
  show (JF.valid (jsum a) || a.all JF.valid) = a.all JF.valid
  rw [hs, Bool.or_self]

end DynExpr.Eval
