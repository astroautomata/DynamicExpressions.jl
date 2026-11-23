import DynExpr.Eval.Core

/-!
Mirrors of `differentiable_eval_tree_array` and the `GenericOperatorEnum`
evaluator in `src/Evaluate.jl:1061-1304`.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- `op.(cumulators...)` for equal-length arrays (src/Evaluate.jl:1102);
unequal lengths raise `DimensionMismatch`. -/
def bcast {V : Type} (f : List V → Jl V) : List (JVec V) → Jl (JVec V)
  | [] => .error (.errorException "broadcast without arguments")
  | c1 :: cs =>
    if (c1 :: cs).all (fun c => c.size == c1.size) then do
      let vs ← (List.range c1.size).mapM (fun j => do
        let args ← (c1 :: cs).mapM (fun c => match c[j]? with
          | some v => .ok v
          | none => .error .boundsError)
        f args)
      pure vs.toArray
    else .error (.errorException "DimensionMismatch")

/-- `fill_similar(one(T), cX, axes(cX, 2)) .* tree.val` (src/Evaluate.jl:1094). -/
def constRow (n : Nat) (v : T) : JVec T :=
  (List.replicate n (JlScalar.one : T)).toArray.map (fun u => JlScalar.mul u v)

mutual
/- Source: src/Evaluate.jl:1090-1099
function deg0_diff_eval(
    tree::AbstractExpressionNode{T1}, cX::AbstractMatrix{T}, operators::OperatorEnum
)::ResultOk where {T<:Number,T1}
    if tree.constant
        ResultOk(fill_similar(one(T), cX, axes(cX, 2)) .* tree.val, is_valid(tree.val))
    else
        out = cX[tree.feature, :]
        ResultOk(out, is_valid_array(out))
    end
end
-/
/-- `_differentiable_eval_tree_array` (src/Evaluate.jl:1073-1135). -/
def diffT (o : OpEnum T) (X : JMat T) : Tree T → Jl (ResultOk T)
  | .const v => .ok ⟨constRow X.ncols v, valid v, .fresh⟩
  | .feature f => do
    let r ← X.row f
    pure ⟨r, isValidArray r, .fresh⟩
  | .branch op cs => do
    match ← diffL o X cs with
    | .inl r => pure r
    | .inr xs => do
      let f ← nifOp (opsOf o cs.length) op
      let out ← bcast (fun args => .ok (f args)) xs
      pure ⟨out, out.toList.all valid, .fresh⟩
/-- Children of `dispatch_degn_diff_eval` with `!result.ok && return result`. -/
def diffL (o : OpEnum T) (X : JMat T) : List (Tree T) → Jl (ResultOk T ⊕ List (JVec T))
  | [] => .ok (.inr [])
  | c :: cs => do
    let r ← diffT o X c
    if !r.ok then pure (.inl r)
    else do
      match ← diffL o X cs with
      | .inl e => pure (.inl e)
      | .inr xs => pure (.inr (r.x :: xs))
end

/-- `differentiable_eval_tree_array(tree, cX, operators)` (src/Evaluate.jl:1066-1071). -/
def differentiableEvalTreeArray (o : OpEnum T) (X : JMat T) (t : Tree T) :
    Jl (JVec T × Bool) :=
  (diffT o X t).map fun r => (r.x, r.ok)

/-- An operator of a `GenericOperatorEnum` on dynamically typed values `V`. -/
structure GOp (V : Type) where
  /-- `hasmethod(op, Tuple{typeof.(args)...})` for scalar arguments (`N == 1`). -/
  hasMethod : List V → Bool
  /-- `hasmethod(op, Tuple{eltype.(cumulators)...})` for array arguments (`N > 1`). -/
  hasMethodArr : List (JVec V) → Bool
  /-- Calling the operator; it may throw (e.g. `MethodError`). -/
  call : List V → Jl V

/-- `GenericOperatorEnum` (src/OperatorEnum.jl:23-29). -/
structure GOpEnum (V : Type) where
  ops : List (List (GOp V))

/-- `operators[d]`. -/
def gopsOf {V : Type} (o : GOpEnum V) (d : Nat) : List (GOp V) := (o.ops[d - 1]?).getD []

/-- `@nif` operator selection with the `get_op` error (src/Evaluate.jl:384-395, 1289-1301). -/
def gnifOp {V : Type} (ops : List (GOp V)) (op : Nat) : Jl (GOp V) :=
  match ops.getLast? with
  | none => .error (.errorException
      "Invalid access: a node has degree d, but no operators were passed for this degree.")
  | some last => .ok (if 1 ≤ op ∧ op < ops.length then (ops[op - 1]?).getD last else last)

section generic
variable {V : Type} (o : GOpEnum V) (throw : Bool)

mutual
/-- `_eval_tree_array_generic` for a vector input (`N == 1`): a feature leaf is
the scalar `cX[feature]` (src/Evaluate.jl:1211-1304). `none` is `nothing`. -/
def gen1 (x : JVec V) : Tree V → Jl (Option V × Bool)
  | .const v => .ok (some v, true)
  | .feature f =>
    if 1 ≤ f then
      match x[f - 1]? with
      | some v => .ok (some v, true)
      | none => .error .boundsError
    else .error .boundsError
  | .branch op cs => do
    match ← gen1L x cs with
    | .inl r => pure r
    | .inr vs => do
      let g ← gnifOp (gopsOf o cs.length) op
      if !throw && !g.hasMethod vs then pure (none, false)
      else do
        let v ← g.call vs
        pure (some v, true)
/-- Children loop with `!throw_errors && !complete && return nothing, false`. -/
def gen1L (x : JVec V) : List (Tree V) → Jl ((Option V × Bool) ⊕ List V)
  | [] => .ok (.inr [])
  | c :: cs => do
    let (v?, ok) ← gen1 x c
    if !throw && !ok then pure (.inl (none, false))
    else match v? with
      | none => .error (.methodError "operator applied to nothing")
      | some v => do
        match ← gen1L x cs with
        | .inl e => pure (.inl e)
        | .inr vs => pure (.inr (v :: vs))
end

mutual
/-- `_eval_tree_array_generic` for a features-by-samples matrix (`N == 2`):
leaves are slices along the first axis and operators broadcast
(src/Evaluate.jl:1233-1263). -/
def gen2 (X : JMat V) : Tree V → Jl (Option (JVec V) × Bool)
  | .const v => .ok (some (JVec.fill X.ncols v), true)
  | .feature f => do
    let r ← X.row f
    pure (some r, true)
  | .branch op cs => do
    match ← gen2L X cs with
    | .inl r => pure r
    | .inr xs => do
      let g ← gnifOp (gopsOf o cs.length) op
      if !throw && !g.hasMethodArr xs then pure (none, false)
      else do
        let out ← bcast g.call xs
        pure (some out, true)
/-- Children loop for `gen2`. -/
def gen2L (X : JMat V) : List (Tree V) → Jl ((Option (JVec V) × Bool) ⊕ List (JVec V))
  | [] => .ok (.inr [])
  | c :: cs => do
    let (v?, ok) ← gen2 X c
    if !throw && !ok then pure (.inl (none, false))
    else match v? with
      | none => .error (.methodError "operator applied to nothing")
      | some v => do
        match ← gen2L X cs with
        | .inl e => pure (.inl e)
        | .inr vs => pure (.inr (v :: vs))
end

/-- The `try`/`catch` wrapper of `eval_tree_array(tree, cX, ::GenericOperatorEnum;
throw_errors)` (src/Evaluate.jl:1185-1209). Any exception becomes
`(nothing, false)` without `throw_errors`, otherwise an `ErrorException`
("Failed to evaluate tree ..."). -/
def genCatch {R : Type} (r : Jl (Option R × Bool)) : Jl (Option R × Bool) :=
  match r with
  | .ok v => .ok v
  | .error _ =>
    if !throw then .ok (none, false)
    else .error (.errorException "Failed to evaluate tree")

/-- Generic evaluation of a vector input. -/
def genEvalVec (t : Tree V) (x : JVec V) : Jl (Option V × Bool) :=
  genCatch throw (gen1 o throw x t)

/-- Generic evaluation of a matrix input. -/
def genEvalMat (t : Tree V) (X : JMat V) : Jl (Option (JVec V) × Bool) :=
  genCatch throw (gen2 o throw X t)

end generic

end DynExpr.Eval
