import DynExpr.ParamStruct.ScalarLaws

namespace DynExpr.ParamStruct

/-- Exact-length scalar updates read back every supplied value. The sole excluded
length-mismatch trigger is measured by the getter, src/ParametricExpression.jl:270-285. -/
def ParametricExactLengthSafe : Prop := ∀ s result : ConstantState, ∀ old values,
  s.refs.Nodup → getConstants s = .ok old → values.length = old.length →
  setConstants s values = .ok result → getConstants result = .ok values

theorem parametricExactLengthSafe_proven : ParametricExactLengthSafe := by
  intro s result old values hn hg hlen hw
  exact setConstants_read_values s result values hn
    (hlen.trans (getConstants_length s old hg)) hw

/-- Nonempty classes pass validation whenever the specified length and upper
bound checks pass. Zero/negative values remain outside the gathering coordinate
preconditions; this theorem concerns exactly the validation function,
src/ParametricExpression.jl:385-386. -/
def NonemptyClassValidationSafe : Prop := ∀ ncols nclasses : Nat, ∀ classes : List Int,
  classes.length = ncols → classes ≠ [] →
  (∀ first rest, classes = first::rest → rest.foldl max first ≤ (nclasses : Int)) →
  checkClasses ncols nclasses classes = .ok ()

theorem nonemptyClassValidationSafe_proven : NonemptyClassValidationSafe := by
  intro ncols nclasses classes hlen hne hmax
  cases classes with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    have bound : ¬ (nclasses : Int) < rest.foldl max first :=
      Int.not_lt.mpr (hmax first rest rfl)
    simp [checkClasses,hlen,bound]

example : let s : ConstantState := ⟨Heap.empty,[],[.fin 1,.fin 2]⟩
    s.refs.Nodup ∧ getConstants s = .ok [.fin 1,.fin 2] ∧
    ([.fin 3,.fin 4] : List JF).length = ([.fin 1,.fin 2] : List JF).length ∧
    ∃ result, setConstants s [.fin 3,.fin 4] = .ok result := by
  exact ⟨by simp,rfl,rfl,⟨⟨Heap.empty,[],[.fin 3,.fin 4]⟩,rfl⟩⟩

example : ([1,2] : List Int).length = 2 ∧ ([1,2] : List Int) ≠ [] ∧
    (∀ first rest, ([1,2] : List Int) = first::rest → rest.foldl max first ≤ (2 : Int)) := by
  refine ⟨rfl,by decide,?_⟩
  intro first rest h
  cases h
  decide

end DynExpr.ParamStruct
