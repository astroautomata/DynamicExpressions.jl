import DynExpr.NodeUtils.Utilities

namespace DynExpr.NodeUtils

/-- src/ValueInterface.jl:5: values with no numeric specialization are valid. -/
def isValidDefault (_ : T) : Bool := true

/-- src/ValueInterface.jl:6 specializes the scalar protocol for numbers. -/
def isValid (x : JF) : Bool := JF.valid x

/-- src/ValueInterface.jl:17 uses elementwise validity for nonfloating values. -/
def isValidArrayGeneric (valid : T → Bool) (xs : List T) : Bool := xs.all valid

/-- src/ValueInterface.jl:18-22 checks the validity of the sum first and falls
back to elementwise validity, for floating and complex floating arrays. The
exact-rational sum has the same nonfinite rules as JF. -/
def isValidArray (xs : List JF) : Bool := isValid (xs.foldl JF.add (.fin 0)) || xs.all isValid

/-- src/ValueInterface.jl:18-22 on a two-element Float16 array. Julia sums in
Float16. Round-to-nearest overflow begins at absolute exact sum 65520;
validity needs no model of the finite rounded mantissa. The inputs are exact
encodings of Float16 values, including its infinities and NaN. -/
def isValidArray16Pair (a b : JF) : Bool :=
  (match JF.add a b with
    | .fin q => decide ((-65520 : Rat) < q ∧ q < 65520)
    | _ => false) || (isValid a && isValid b)

/-- The floating type shapes accepted by src/ValueInterface.jl:14-15.
Floating precision does not affect the nonfinite component rules. -/
inductive FloatShape where
  | real
  | complex

def FloatShape.Value : FloatShape → Type
  | .real => JF
  | .complex => JF × JF

/-- src/ValueInterface.jl:14-15 constructs NaN, or complex (NaN, zero). -/
def invalidValue : (shape : FloatShape) → shape.Value
  | .real => .nan
  | .complex => (.nan, .fin 0)

/-- src/ValueInterface.jl:6; a complex number is finite exactly when both
components are finite. -/
def isValidFloat : (shape : FloatShape) → shape.Value → Bool
  | .real, v => isValid v
  | .complex, (re, im) => isValid re && isValid im

/-- src/ValueInterface.jl:33-38, one-based checked numeric packing. -/
def packScalar (xs : List T) (idx : Nat) (v : T) : Jl (Nat × List T) :=
  if 1 ≤ idx ∧ idx ≤ xs.length then .ok (idx + 1, xs.set (idx - 1) v)
  else .error .boundsError

/-- src/ValueInterface.jl:57-61, same-type numeric unpacking. -/
def unpackScalar (xs : List T) (idx : Nat) : Jl (Nat × T) :=
  if idx = 0 then .error .boundsError
  else match xs[idx - 1]? with
    | some v => .ok (idx + 1, v)
    | none => .error .boundsError

/-- src/ValueInterface.jl:25 returns the numeric type unchanged. -/
def getNumberType (T : Type) : Type := T

/-- src/ValueInterface.jl:74. -/
def scalarCount (_ : T) : Nat := 1

/-- src/ValueInterface.jl:42-44 and 59-61 reject missing composite methods. -/
def missingComposite (operation : String) : Jl T :=
  .error (.argumentError (operation ++ " not implemented"))

/-- Composite implementations supply arbitrary pack/unpack methods, matching
src/ValueInterface.jl:106-148; the interface tests their round trip. -/
structure ValueProtocol (T : Type) where
  count : T → Nat
  pack : List JF → Nat → T → Jl (Nat × List JF)
  unpack : List JF → Nat → T → Jl (Nat × T)

def ScalarRoundtrip : Prop := ∀ (xs : List JF) (idx : Nat) (v : JF),
  1 ≤ idx → idx ≤ xs.length →
  packScalar xs idx v = .ok (idx + 1, xs.set (idx - 1) v) ∧
  unpackScalar (xs.set (idx - 1) v) idx = .ok (idx + 1, v)

theorem scalarRoundtrip_proven : ScalarRoundtrip := by
  intro xs idx v hpos hbound
  have hlt : idx - 1 < xs.length := by omega
  have hne : idx ≠ 0 := by omega
  simp [packScalar, unpackScalar, hpos, hbound, hne, List.getElem?_set_self hlt]

example : 1 ≤ (1 : Nat) ∧ 1 ≤ ([JF.fin 0] : List JF).length := by decide

def ScalarCountOne : Prop := ∀ (buffer : List JF) (idx : Nat) (value : JF),
  1 ≤ idx → idx ≤ buffer.length →
    ∃ packed, packScalar buffer idx value = .ok (idx + scalarCount value,packed) ∧
      unpackScalar packed idx = .ok (idx + scalarCount value,value) ∧ packed.length = buffer.length

theorem scalarCountOne_proven : ScalarCountOne := by
  intro buffer idx value hpos hbound
  obtain ⟨hpack,hunpack⟩ := scalarRoundtrip_proven buffer idx value hpos hbound
  exact ⟨buffer.set (idx - 1) value,hpack,hunpack,by simp⟩

def InvalidScalar : Prop := ∀ shape : FloatShape,
  isValidFloat shape (invalidValue shape) = false

theorem invalidScalar_proven : InvalidScalar := by
  intro shape
  cases shape <;> rfl

def GenericValidity : Prop := ∀ (valid : Nat → Bool) xs,
  isValidArrayGeneric valid xs = true ↔ ∀ x ∈ xs, valid x = true

theorem genericValidity_proven : GenericValidity := by
  intro valid xs; simp [isValidArrayGeneric]

def NumericArrayElementwise : Prop := ∀ a b : JF,
  isValidArray16Pair a b = (isValid a && isValid b)

theorem numericArrayElementwise_proven : NumericArrayElementwise := by
  intro a b
  cases a <;> cases b <;> simp [isValidArray16Pair, isValid, JF.valid, JF.add]

/-- Float16 addition can overflow even when both input elements are finite. -/
def NoFloat16SumOverflow (a b : JF) : Prop :=
  match JF.add a b with
  | .fin q => (-65520 : Rat) < q ∧ q < 65520
  | _ => True

def NumericArrayElementwiseNoOverflow : Prop := ∀ a b : JF,
  NoFloat16SumOverflow a b →
  isValidArray16Pair a b = (isValid a && isValid b)

theorem numericArrayElementwiseNoOverflow_proven : NumericArrayElementwiseNoOverflow :=
  fun a b _ => numericArrayElementwise_proven a b

example : NoFloat16SumOverflow (.fin 1) (.fin 2) := by
  simp only [NoFloat16SumOverflow, JF.add] <;> decide +kernel

example : NoFloat16SumOverflow .nan .posInf := trivial

end DynExpr.NodeUtils
