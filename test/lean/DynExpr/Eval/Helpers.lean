import DynExpr.Eval.Core

/-!
Mirrors of `src/EvaluationHelpers.jl` (callable trees and `adjoint`) and the
extension fallbacks of `src/ExtensionInterface.jl`.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- `set_invalid!(out)` (src/Utils.jl:99-102): fills with `invalid_value(T)`,
a `MethodError` when the type has no such method. -/
def setInvalid (out : JVec T) : Jl (JVec T) :=
  match JlScalar.invalid? (T := T) with
  | some v => .ok (JVec.fill out.size v)
  | none => .error (.methodError "invalid_value")

/-- `set_invalid!` on a gradient matrix. -/
def setInvalidMat (g : JMat T) : Jl (JMat T) :=
  match JlScalar.invalid? (T := T) with
  | some v => .ok ⟨g.nrows, g.ncols, Array.replicate g.data.size v, by simp [g.size_eq]⟩
  | none => .error (.methodError "invalid_value")

/-- `(tree)(X, operators::OperatorEnum; kws...)` (src/EvaluationHelpers.jl:29-33)
applied to the result `r` of `eval_tree_array(tree, X, operators; kws...)`. -/
def callTree (r : Jl (JVec T × Bool)) : Jl (JVec T) := do
  let (out, ok) ← r
  if !ok then setInvalid out else pure out

/-- `(tree)(X, operators::GenericOperatorEnum; kws...)`
(src/EvaluationHelpers.jl:49-53) applied to the generic evaluation result. -/
def callTreeGeneric {R : Type} (r : Jl (Option R × Bool)) : Jl (Option R) := do
  let (out, ok) ← r
  if !ok then pure none else pure out

/-- `_grad_evaluator(tree, X, ::OperatorEnum; variable)` (src/EvaluationHelpers.jl:56-62)
applied to the result of `eval_grad_tree_array`. -/
def gradEvaluator (r : Jl (JVec T × JMat T × Bool)) : Jl (JMat T) := do
  let (_, g, ok) ← r
  if !ok then setInvalidMat g else pure g

/-- `_grad_evaluator(tree, X, ::GenericOperatorEnum)` (src/EvaluationHelpers.jl:63-67). -/
def gradEvaluatorGeneric {α : Type} : Jl α :=
  .error (.errorException "Gradients are not implemented for `GenericOperatorEnum`.")

/-- `Base.adjoint(tree)` (src/EvaluationHelpers.jl:90-91): a closure that
forwards to `_grad_evaluator`; `evalGrad` is `eval_grad_tree_array` with
`variable=Val(true)` (owned by the derivative slice). -/
def adjointTree (evalGrad : Tree T → JMat T → OpEnum T → Jl (JVec T × JMat T × Bool))
    (t : Tree T) : JMat T → OpEnum T → Jl (JMat T) :=
  fun X o => gradEvaluator (evalGrad t X o)

/-- `node_to_symbolic(args...)` (src/ExtensionInterface.jl:25-29). -/
def nodeToSymbolic {α β : Type} (ext : Ext) (impl : α → Jl β) (a : α) : Jl β :=
  if ext.symbolicUtils then impl a
  else .error (.errorException "Please load the `SymbolicUtils` package to use `node_to_symbolic`.")

/-- `symbolic_to_node(args...)` (src/ExtensionInterface.jl:32-36). -/
def symbolicToNode {α β : Type} (ext : Ext) (impl : α → Jl β) (a : α) : Jl β :=
  if ext.symbolicUtils then impl a
  else .error (.errorException "Please load the `SymbolicUtils` package to use `symbolic_to_node`.")

/-- `_zygote_gradient(args...)` (src/ExtensionInterface.jl:50-53). -/
def zygoteGradient {α β : Type} (ext : Ext) (impl : α → Jl β) (a : α) : Jl β :=
  if ext.zygote then impl a
  else .error (.errorException "Please load the Zygote.jl package.")

end DynExpr.Eval
