import DynExpr.Eval.Props
import DynExpr.Eval.Scalars
import DynExpr.Eval.Lemmas

/-!
Proofs of the evaluator context, extension, callable-tree and adjoint
properties.
-/

namespace DynExpr.Eval

theorem evalContextExt_proof : evalContextExt := by
  intro T _ ext impl D o X t turbo early fused b
  refine ⟨rfl, rfl, ?_⟩
  intro hf hl
  simp [evalTreeArray, hf, hl]

theorem evalTurboNonNumeric_proof : evalTurboNonNumeric := by
  intro T _ ext impl D o X t early fused b hnum hfloat _
  have hf : JlScalar.isFloat (T := T) = false := by
    cases h : JlScalar.isFloat (T := T)
    · rfl
    · have := hfloat h; simp [this] at hnum
  simp [evalTreeArray, hf]

/-- A non-numeric element type (e.g. `Vector{Float64}`) satisfies the
eval-turbo-nonnumeric hypotheses. -/
private instance : JlScalar Unit where
  valid := fun _ => true
  zero := ()
  one := ()
  add := fun _ _ => ()
  mul := fun _ _ => ()
  isNumber := false
  isFloat := false
  floatLike := false
  undef := ()
  invalid? := none

example : isNum Unit = false ∧ (JlScalar.isFloat (T := Unit) = true → isNum Unit = true) :=
  ⟨rfl, fun h => h⟩

theorem evalAdjoint_proof : evalAdjoint := by
  intro T _ evalGrad t X o inv hinv
  refine ⟨?_, ?_, rfl⟩
  · intro y g h
    simp [adjointTree, gradEvaluator, h]
  · intro y g h
    refine ⟨⟨g.nrows, g.ncols, Array.replicate g.data.size inv, by simp [g.size_eq]⟩, ?_,
      rfl, rfl, ?_⟩
    · simp [adjointTree, gradEvaluator, h, setInvalidMat, hinv]
    · intro z hz
      simp at hz
      exact hz.2

theorem evalExtFallbacks_proof : evalExtFallbacks := by
  intro α β impl a
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The adjoint hypotheses are satisfiable: `Float64` has `invalid_value`. -/
example : JlScalar.invalid? (T := JF) = some .nan := rfl

end DynExpr.Eval
