import DynExpr.Eval.Props
import DynExpr.Eval.Scalars

/-!
Concrete evaluator regression cases and scalar fixtures also used by the
feature-cache model.
-/

namespace DynExpr.Eval.Ex
open DynExpr.Eval

/-- `inv(x) = one(x) / x`. -/
def inv1 : List JF → JF
  | [x] => JF.div (.fin 1) x
  | _ => .nan
/-- Unary `-`. -/
def neg1 : List JF → JF
  | [x] => JF.neg x
  | _ => .nan
/-- Binary `+`. -/
def add2 : List JF → JF
  | [x, y] => JF.add x y
  | _ => .nan
/-- Binary `/`. -/
def div2 : List JF → JF
  | [x, y] => JF.div x y
  | _ => .nan

/-- `OperatorEnum(1 => (inv, -), 2 => (+, /))`. -/
def ops : OpEnum JF := ⟨[[inv1, neg1], [add2, div2]]⟩

/-- Extensions are never called in these examples. -/
def noImpl {T : Type} : ExtImpl T := ⟨fun _ _ => .error .boundsError⟩

/-- `is_valid_array` on `JF` arrays holds exactly for all-finite arrays. -/
theorem jf_exact : ArrayValidExact JF := by
  intro a
  rw [jf_isValidArray, Array.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hx)
    exact h i hi
  · intro h i hi
    exact h _ (by simp)

/-- One sample with `x1 = 0`. -/
def XZero : JMat JF := ⟨1, 1, #[.fin 0], rfl⟩

/-- The constant tree `inv(inv(0.0))`, whose value is `0`. -/
def tConstInvInv : Tree JF := .branch 1 [.branch 1 [.const (.fin 0)]]

/-- The non-constant tree `x1 + inv(inv(0.0))`, whose value is `x1`. -/
def tXPlusConst : Tree JF := .branch 1 [.feature 1, tConstInvInv]

theorem tXPlusConst_wf : tXPlusConst.WF 2 ops.nops 1 := by
  simp [tXPlusConst, tConstInvInv, Tree.WF, OpEnum.nops, ops]

/-- Constant subtrees are evaluated without early exit when the flag is off. -/
example : obs (evalTreeArray {} noImpl 2 tXPlusConst XZero ops (plainCtx false false .none)) =
    .ok ([.fin 0], true) := by decide +kernel

/-- An invalid constant leaf is rejected (src/Evaluate.jl:1094). -/
example : obs (differentiableEvalTreeArray ops XZero (.const .nan)) = .ok ([.nan], false) := by
  decide +kernel

private def nonfinitePair : Tree JF :=
  .branch 1 [.branch 2 [.const (.fin 1), .const (.fin 0)], .feature 1]

/-- The fused branch reserves its first slot before checking the inner pair,
then reserves a second slot to return an incomplete result (src/Evaluate.jl:820-836). -/
example : evalTreeArray {} noImpl 2 nonfinitePair XZero ops (plainCtx true true (.mat XZero 0)) =
    .error .boundsError := by decide +kernel

example : (evalTreeArray {} noImpl 2 nonfinitePair XZero ops
    (plainCtx true true (.mat ⟨2, 1, #[.fin 0, .fin 0], rfl⟩ 0))).map Prod.snd =
    .ok false := by decide +kernel

/-- `one(T) * v == v` for `JF`. -/
theorem jf_one_mul (v : JF) : JlScalar.mul JlScalar.one v = v := by
  cases v with
  | fin x => show JF.mul (.fin 1) (.fin x) = .fin x; simp [JF.mul]
  | nan => rfl
  | posInf => decide
  | negInf => decide


example : (Tree.const (.fin 1 : JF)).WF 2 ops.nops XZero.nrows ∧
    (∀ v : JF, JlScalar.mul JlScalar.one v = v) ∧ ArrayValidExact JF ∧
    obs (differentiableEvalTreeArray ops XZero (.const (.fin 1))) = .ok ([.fin 1], true) :=
  ⟨by simp [Tree.WF], jf_one_mul, jf_exact, by decide +kernel⟩

end DynExpr.Eval.Ex
