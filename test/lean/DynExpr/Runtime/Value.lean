import Init.Data.Rat.Basic

namespace DynExpr

/-- Scalar validity protocol from src/ValueInterface.jl:5-6. -/
class JlValue (T : Type) where
  valid : T → Bool

/-- Exact rational finite values with the nonfinite values tested by
src/ValueInterface.jl:6,14. Arithmetic models IEEE special-value rules, with
unbounded exact finite arithmetic: no rounding, overflow, or signed zero.
The sole finite zero represents positive zero for division by zero. -/
inductive JF where
  | fin (value : Rat)
  | nan
  | posInf
  | negInf
  deriving DecidableEq, Repr

namespace JF

/-- Numeric validity (`isfinite` and exclusion of NaN), src/ValueInterface.jl:6. -/
def valid : JF → Bool
  | .fin _ => true
  | _ => false

/-- The numeric instance of src/ValueInterface.jl:6. -/
instance : JlValue JF := ⟨valid⟩

/-- Sign of values used by scalar operators in src/Simplify.jl:25-116.
NaN's sign is unused because arithmetic propagates NaN first. -/
private def negative : JF → Bool
  | .fin x => decide (x.num < 0)
  | .negInf => true
  | _ => false

/-- Signed infinity for scalar arithmetic in src/Simplify.jl:25-116. -/
private def infinity (negative : Bool) : JF :=
  if negative then .negInf else .posInf

/-- Unary minus as used in src/Simplify.jl:25-116. -/
def neg : JF → JF
  | .fin x => .fin (-x)
  | .nan => .nan
  | .posInf => .negInf
  | .negInf => .posInf

/-- Addition as used in src/Simplify.jl:25-116, propagating NaN and
returning NaN for opposite infinities. -/
def add : JF → JF → JF
  | .nan, _ | _, .nan => .nan
  | .fin x, .fin y => .fin (x + y)
  | .posInf, .negInf | .negInf, .posInf => .nan
  | .posInf, _ | _, .posInf => .posInf
  | .negInf, _ | _, .negInf => .negInf

/-- Subtraction as used in src/Simplify.jl:25-116; equal infinities
subtract to NaN. -/
def sub (x y : JF) : JF := add x (neg y)

/-- Multiplication as used in src/Simplify.jl:25-116. Zero times an
infinity is NaN; other infinite products use the product's sign. -/
def mul : JF → JF → JF
  | .nan, _ | _, .nan => .nan
  | .fin x, .fin y => .fin (x * y)
  | .fin x, y => if x = 0 then .nan else infinity (negative (.fin x) != negative y)
  | x, .fin y => if y = 0 then .nan else infinity (negative x != negative (.fin y))
  | x, y => infinity (negative x != negative y)

/-- Scalar division available to the operators of src/Evaluate.jl:280-310.
Zero divided by zero and infinity divided by infinity are NaN; nonzero
values divided by zero yield signed infinity. Finite values divided by
infinity yield the single finite zero. Nonzero finite division is exact. -/
def div : JF → JF → JF
  | .nan, _ | _, .nan => .nan
  | .fin x, .fin y =>
      if y = 0 then
        if x = 0 then .nan else infinity (negative (.fin x))
      else .fin (x / y)
  | .fin _, _ => .fin 0
  | x, .fin y => infinity (negative x != negative (.fin y))
  | _, _ => .nan

/-- Scalar negation used by src/Simplify.jl:25-116. -/
instance : Neg JF := ⟨neg⟩
/-- Scalar addition used by src/Simplify.jl:25-116. -/
instance : Add JF := ⟨add⟩
/-- Scalar subtraction used by src/Simplify.jl:25-116. -/
instance : Sub JF := ⟨sub⟩
/-- Scalar multiplication used by src/Simplify.jl:25-116. -/
instance : Mul JF := ⟨mul⟩
/-- Scalar division for src/Evaluate.jl:280-310. -/
instance : Div JF := ⟨div⟩

example : JlValue.valid (JF.fin 0) = true := rfl
example : JlValue.valid JF.nan = false := rfl
example : JlValue.valid JF.posInf = false := rfl
example : JlValue.valid JF.negInf = false := rfl
example : JF.fin 0 * JF.posInf = JF.nan := by decide
example : JF.negInf * JF.fin 0 = JF.nan := by decide
example : JF.posInf - JF.posInf = JF.nan := rfl
example : JF.negInf - JF.negInf = JF.nan := rfl
example : JF.fin 1 / JF.fin 0 = JF.posInf := by decide
example : JF.fin (-1) / JF.fin 0 = JF.negInf := by decide
example : JF.fin 0 / JF.fin 0 = JF.nan := by decide
example : JF.posInf / JF.negInf = JF.nan := rfl
example : JF.nan + JF.fin 1 = JF.nan := rfl
example : JF.fin 1 / JF.nan = JF.nan := rfl

end JF
end DynExpr
