import DynExpr.Runtime.Array
import DynExpr.Runtime.Value

namespace DynExpr.NodeUtils

/-- src/Utils.jl:87-93, including the null flag independent of the payload. -/
structure Nullable (T : Type) where
  null : Bool
  value : T

def nullableGet (n : Nullable T) : Jl T :=
  if n.null then .error .undefRefError else .ok n.value

/-- src/Utils.jl:95-97 converts the payload even for null references. -/
def nullableConvert (f : A → B) (n : Nullable A) : Nullable B :=
  ⟨n.null, f n.value⟩

/-- src/Utils.jl:17-21; requested dense axis length is supplied explicitly. -/
def fillSimilar (v : T) (n : Nat) : JVec T := JVec.fill n v

/-- src/Utils.jl:99-101 for floating numeric arrays. -/
def setInvalid (out : JVec JF) : JVec JF := JVec.fill out.size .nan

/-- src/Utils.jl:76-85 stores the completion flag without recomputing validity. -/
structure ResultOk (T : Type) where
  x : T
  ok : Bool

structure ResultOk2 (A B : Type) where
  x : A
  dx : B
  ok : Bool

/-- src/Utils.jl:23-29, deprecated argument conflict remains an assertion. -/
def deprecateVarmap (names old : Option (List String)) : Jl (Option (List String)) :=
  match old with
  | none => .ok names
  | some m => if names.isSome then .error (.assertionError "Cannot pass both") else .ok (some m)

/-- src/Utils.jl:59 extracts tuple arity. -/
def countTuple (xs : List T) : Nat := xs.length

def NullableAccess : Prop := ∀ v : Nat,
  nullableGet ⟨false,v⟩ = .ok v ∧ nullableGet ⟨true,v⟩ = .error .undefRefError

theorem nullableAccess_proven : NullableAccess := by intro v; exact ⟨rfl,rfl⟩

def NullableConversion : Prop := ∀ (f : Nat → Nat) (n : Nullable Nat),
  nullableGet (nullableConvert f n) =
    match nullableGet n with
    | .ok value => .ok (f value)
    | .error error => .error error

theorem nullableConversion_proven : NullableConversion := by
  intro f n
  cases h : n.null <;> simp [nullableGet,nullableConvert,h]

def FilledShape : Prop := ∀ (v : Nat) n,
  (fillSimilar v n).size = n ∧ (fillSimilar v n).toList = List.replicate n v

theorem filledShape_proven : FilledShape := by
  intro v n; simp [fillSimilar, JVec.fill]

def InvalidFill : Prop := ∀ out : JVec JF,
  (setInvalid out).size = out.size ∧ (setInvalid out).toList.all JF.valid = false ∨ out.size = 0

theorem invalidFill_proven : InvalidFill := by
  intro out
  by_cases h : out.size = 0
  · exact Or.inr h
  · left
    cases hn : out.size with
    | zero => exact False.elim (h hn)
    | succ n => simp [setInvalid, JVec.fill, hn, List.replicate_succ, JF.valid]
def DeprecatedConflict : Prop := ∀ a b : List String,
  deprecateVarmap (some a) (some b) = .error (.assertionError "Cannot pass both")

theorem deprecatedConflict_proven : DeprecatedConflict := by intro a b; rfl

end DynExpr.NodeUtils
