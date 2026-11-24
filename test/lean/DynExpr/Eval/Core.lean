import DynExpr.Model.Denote
import DynExpr.Runtime.Value

/-!
Mirror of the typed evaluator `eval_tree_array(tree, X, ::OperatorEnum)` in
`src/Evaluate.jl`, including the constant-tree shortcut, the fused kernels,
early exit, and `ArrayBuffer` slot allocation.

Modelling choices:
* Arrays are values. A kernel that writes into a cumulator returns the
  written array; the buffer state records only the slot index (and, for the
  vector-backed buffer, the slot list). Within one evaluation each slot is
  handed out once, so writes are never read back through the buffer.
* Uninitialised storage from `similar` is the fixed value `JlScalar.undef`;
  no property depends on its contents.
* `sum` in `is_valid_array` (src/ValueInterface.jl:20) is a left fold starting
  at the first element, which is Julia's order for arrays shorter than 1024.
* Out-of-range accesses under `@inbounds` are `JlError.undefinedBehavior`.
* `checkbounds` and the checked `@view` of an `ArrayBuffer` slot raise
  `JlError.boundsError`.
-/

namespace DynExpr.Eval

/-- Scalar element types of the typed evaluator. Fields record the Julia
facts the evaluator uses about `T`. -/
class JlScalar (T : Type) extends JlValue T where
  /-- `zero(T)` (src/Evaluate.jl:806) and the empty `sum`. -/
  zero : T
  /-- `one(T)` (src/Evaluate.jl:1094). -/
  one : T
  /-- `+` used by `sum` in `is_valid_array` (src/ValueInterface.jl:20). -/
  add : T → T → T
  /-- `*` used by `differentiable_eval_tree_array` (src/Evaluate.jl:1094). -/
  mul : T → T → T
  /-- `T <: Number` (src/Evaluate.jl:470). -/
  isNumber : Bool
  /-- `T in (Float32, Float64)` (src/Evaluate.jl:269). -/
  isFloat : Bool
  /-- `T <: Union{AbstractFloat,Complex{<:AbstractFloat}}`, which selects the
  `is_valid_array` method that tries the sum first (src/ValueInterface.jl:18-21). -/
  floatLike : Bool
  /-- Contents of uninitialised storage returned by `similar` (src/Evaluate.jl:71). -/
  undef : T
  /-- `invalid_value(T)` when a method exists (src/ValueInterface.jl:13-15). -/
  invalid? : Option T

variable {T : Type} [JlScalar T]

/-- `is_valid` (src/ValueInterface.jl:5-6). -/
abbrev valid (x : T) : Bool := JlValue.valid x

/-- `T <: Number`. -/
abbrev isNum (T : Type) [JlScalar T] : Bool := JlScalar.isNumber (T := T)

/-- `sum(x)` as a left fold from the first element (empty: `zero(T)`). -/
def jsum (a : JVec T) : T :=
  match a.toList with
  | [] => JlScalar.zero
  | x :: xs => xs.foldl JlScalar.add x

/-- `is_valid_array` (src/ValueInterface.jl:17-21): for floating-point element
types `is_valid(sum(x)) || all(is_valid, x)`, otherwise `all(is_valid, x)`. -/
def isValidArray (a : JVec T) : Bool :=
  if JlScalar.floatLike (T := T) then valid (jsum a) || a.all valid else a.all valid

/-- Identity of an array object returned by the evaluator: freshly allocated
(by `similar`, `fill_similar` or a `getindex` copy), or the `ArrayBuffer`
slot with the given one-based index. -/
inductive Ident where
  | fresh
  | slot (k : Nat)
  deriving DecidableEq, Repr

/-- `ResultOk` (src/Utils.jl:76-79), with the identity of the array `x`. -/
structure ResultOk (T : Type) where
  x : JVec T
  ok : Bool
  id : Ident

/-- Evaluation policy fields of `EvalContext` used by `_eval_tree_array`
(src/Evaluate.jl:142-148), plus the node type's maximum degree `D`. -/
structure Ctx where
  earlyExit : Bool := true
  useFused : Bool := true
  D : Nat := 2

/-- `ArrayBuffer` storage (src/Evaluate.jl:40-56): `nothing`, a matrix whose
rows are slots, or a vector of slot arrays; `idx` is `buffer.index[]`. -/
inductive Buf (T : Type) where
  | none
  | mat (A : JMat T) (idx : Nat)
  | vec (arrs : Array (JVec T)) (idx : Nat)

/-- Identity of the array the next `get_array`-style call returns. -/
def nextId : Buf T → Ident
  | .none => .fresh
  | .mat _ i => .slot (i + 1)
  | .vec _ i => .slot (i + 1)

def Buf.isNone : Buf T → Bool
  | .none => true
  | _ => false

/-- `@inbounds X[f, :]` (src/Evaluate.jl:98). -/
def rowInb (X : JMat T) (f : Nat) : Jl (JVec T) :=
  if 1 ≤ f ∧ f ≤ X.nrows then X.row f
  else .error (.undefinedBehavior "row index out of bounds")

/-- `@inbounds X[k]` with linear indexing (src/Evaluate.jl:112). The index is
in range whenever `first_feature_index` passed its `checkbounds`. -/
def linInb (X : JMat T) (k : Nat) : Jl T :=
  if h : 1 ≤ k ∧ k ≤ X.data.size then .ok (X.data[k - 1]'(by omega))
  else .error (.undefinedBehavior "linear index out of bounds")

/-- `feature_at(X, input_index, feature, j, IndexLinear())` at loop iteration
`j`, where `input_index = first_feature_index(X, feature) + (j-1)*size(X,1)`
(src/Evaluate.jl:106-112, e.g. :692-700). Matrices use linear indexing. -/
def featureAt (X : JMat T) (f j : Nat) : Jl T :=
  linInb X (f + (j - 1) * X.nrows)

/-- `checkbounds(X, feature, :)` in `first_feature_index` and `deg0_eval`
(src/Evaluate.jl:107-110,377). -/
def chk (X : JMat T) (f : Nat) : Jl Unit :=
  if 1 ≤ f ∧ f ≤ X.nrows then .ok () else .error .boundsError

/-- `get_array(buffer, template, axes(X, 2))` (src/Evaluate.jl:70-88). The
matrix case takes the checked view `buffer.array[i, axes(X, 2)]` of the next
slot row (src/Evaluate.jl:74-78). -/
def getArray : Buf T → Nat → Jl (JVec T × Buf T)
  | .none, n => .ok (JVec.fill n JlScalar.undef, .none)
  | .mat A i, n => do
    let r ← A.row (i + 1)
    if n ≤ A.ncols then pure (r.extract 0 n, .mat A (i + 1))
    else .error .boundsError
  | .vec arrs i, n =>
    if h : i < arrs.size then
      if arrs[i].size = n then .ok (arrs[i], .vec arrs (i + 1))
      else
        let a := JVec.fill n JlScalar.undef
        .ok (a, .vec (arrs.set i a) (i + 1))
    else
      let a := JVec.fill n JlScalar.undef
      .ok (a, .vec (arrs.push a) (i + 1))

/-- `get_filled_array(buffer, value, template, axes(X, 2))`
(src/Evaluate.jl:90-95): `fill_similar`, or `fill!` of the next slot. -/
def getFilled : Buf T → T → Nat → Jl (JVec T × Buf T)
  | .none, v, n => .ok (JVec.fill n v, .none)
  | .mat A i, v, n => do
    let (a, b) ← getArray (.mat A i) n
    pure (JVec.fill a.size v, b)
  | .vec arrs i, v, n => do
    let (a, b) ← getArray (.vec arrs i) n
    pure (JVec.fill a.size v, b)

/-- `get_feature_array(buffer, X, feature)` (src/Evaluate.jl:97-104): the row
`X[feature, :]`, copied into the next slot when there is a buffer. -/
def getFeature : Buf T → JMat T → Nat → Jl (JVec T × Buf T)
  | .none, X, f => do
    let r ← rowInb X f
    pure (r, .none)
  | .mat A i, X, f => do
    let (_, b) ← getArray (.mat A i) X.ncols
    let r ← rowInb X f
    pure (r, b)
  | .vec arrs i, X, f => do
    let (_, b) ← getArray (.vec arrs i) X.ncols
    let r ← rowInb X f
    pure (r, b)

/-- Operator tuple `operators[d]` (src/OperatorEnum.jl:32). -/
def opsOf (o : OpEnum T) (d : Nat) : List (List T → T) := (o.ops[d - 1]?).getD []

/-- `Base.Cartesian.@nif(nops, i -> i == op_idx, i -> ops[i])`: indices other
than `1..nops-1` select the last operator; an empty tuple raises the
`get_op` error (src/Evaluate.jl:381-392, 432-438, 485-488, 593-596). -/
def nifOp (ops : List (List T → T)) (op : Nat) : Jl (List T → T) :=
  match ops.getLast? with
  | none => .error (.errorException
      "Invalid access: a node has degree d, but no operators were passed for this degree.")
  | some last => .ok (if 1 ≤ op ∧ op < ops.length then (ops[op - 1]?).getD last else last)

/-- Bounds-checked `operators.binops[op_idx]` used beyond 15 operators
(src/Evaluate.jl:483,589,1031). -/
def idxOp (ops : List (List T → T)) (op : Nat) : Jl (List T → T) :=
  if op = 0 then .error .boundsError
  else match ops[op - 1]? with
    | some f => .ok f
    | none => .error .boundsError

/-- `OPERATOR_LIMIT_BEFORE_SLOWDOWN` (src/Evaluate.jl:14). -/
def operatorLimit : Nat := 15

def isLeaf : Tree T → Bool
  | .branch .. => false
  | _ => true

def isConstLeaf : Tree T → Bool
  | .const _ => true
  | _ => false

/-- The `.val` field of a leaf. -/
def leafVal : Tree T → T
  | .const v => v
  | _ => JlScalar.undef

/-- The `.feature` field of a leaf. -/
def leafFeat : Tree T → Nat
  | .feature f => f
  | _ => 0

mutual
/-- `is_constant` (src/NodeUtils.jl:73): every leaf is a constant. -/
def isConstant : Tree T → Bool
  | .const _ => true
  | .feature _ => false
  | .branch _ cs => isConstantL cs
def isConstantL : List (Tree T) → Bool
  | [] => true
  | c :: cs => isConstant c && isConstantL cs
end

mutual
/-- `dispatch_constant_tree` (src/Evaluate.jl:990-1059). The validity
flag records the scalar result; the policy controls whether a bad child
prevents computing its parent. -/
def constEval (o : OpEnum T) : Tree T → (early : Bool := true) → Jl (T × Bool)
  | .const v, _ => .ok (v, valid v)
  | .feature _, _ => .ok (JlScalar.undef, valid (JlScalar.undef : T))
  | .branch op cs, early => do
    match ← constEvalL o cs early with
    | .inl r => pure r
    | .inr vs => do
      let ops := opsOf o cs.length
      let f ← if operatorLimit < ops.length then idxOp ops op else nifOp ops op
      let out := f vs
      pure (out, valid out)
def constEvalL (o : OpEnum T) : List (Tree T) → (early : Bool := true) → Jl ((T × Bool) ⊕ List T)
  | [], _ => .ok (.inr [])
  | c :: cs, early => do
    let (v, ok) ← constEval o c early
    if early && !ok then pure (.inl (v, ok))
    else do
      match ← constEvalL o cs early with
      | .inl r => pure (.inl r)
      | .inr vs => pure (.inr (v :: vs))
end

/-- `@inbounds @simd for j in axes(cX, 2); cumulator[j] = f(j); end`
(e.g. src/Evaluate.jl:695-701). -/
def simdWrite (cum : JVec T) (n : Nat) (f : Nat → Jl T) : Jl (JVec T) :=
  if n ≤ cum.size then do
    let vs ← (List.range n).mapM (fun j => f (j + 1))
    pure (vs.toArray ++ cum.extract n cum.size)
  else do
    let _ ← (List.range (cum.size + 1)).mapM (fun j => f (j + 1))
    .error (.undefinedBehavior "write past end of cumulator")

/-- `@inbounds @simd for j in eachindex(cumulator); cumulator[j] = g(j, cumulator[j]); end`
(src/Evaluate.jl:929-932, 959-962). -/
def inplaceMap (cum : JVec T) (g : Nat → T → Jl T) : Jl (JVec T) := do
  let vs ← (List.range cum.size).mapM (fun j => g (j + 1) (cum.getD j JlScalar.undef))
  pure vs.toArray

/-- `@inbounds c[j]`. -/
def getInb (c : JVec T) (j : Nat) : Jl T :=
  if h : j < c.size then .ok c[j] else .error (.undefinedBehavior "cumulator index out of bounds")

/-- `degn_eval` (src/Evaluate.jl:340-351): `cumulators[1] .= op.(cumulators...)`. -/
def degnEval (f : List T → T) : List (JVec T) → Jl (JVec T)
  | [] => .error (.errorException "degn_eval without cumulators")
  | c1 :: cs => do
    let vs ← (List.range c1.size).mapM (fun j => do
      let args ← (c1 :: cs).mapM (fun c => getInb c j)
      pure (f args))
    pure vs.toArray

/-- `apply_op_array` (`src/Evaluate.jl:381-400`): selects `operators[D][op_idx]`
via `@nif` when `1 ≤ nops ≤ OPERATOR_LIMIT_BEFORE_SLOWDOWN` and direct indexing
otherwise, then applies `degn_eval`. -/
def applyOpArray (o : OpEnum T) (op : Nat) (cums : List (JVec T)) : Jl (JVec T) := do
  let ops := opsOf o cums.length
  let f ← if ops.length = 0 || operatorLimit < ops.length then idxOp ops op else nifOp ops op
  degnEval f cums

/-- `@return_on_nonfinite_val` (src/Evaluate.jl:16-24) followed by the
continuation `k`. -/
def retV (cx : Ctx) (X : JMat T) (v : T) (k : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  if cx.earlyExit && !valid v then do
    let (a, b') ← getArray b X.ncols
    pure (⟨a, false, nextId b⟩, b')
  else k b

/-- `@return_on_nonfinite_val` executed only when `c` holds, then `k`
(src/Evaluate.jl:831-837). -/
def retVIf (cx : Ctx) (X : JMat T) (c : Bool) (v : T) (k : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  if c then retV cx X v k b else k b

/-- `ResultOk(get_filled_array(buffer, v, cX, axes(cX, 2)), true)`. -/
def filled (X : JMat T) (v : T) (b : Buf T) : Jl (ResultOk T × Buf T) := do
  let (a, b') ← getFilled b v X.ncols
  pure (⟨a, true, nextId b⟩, b')

/-- Unary fused post-processing `early_exit && !is_valid(x_l) ? x_l : op(x_l)`
(src/Evaluate.jl:698,713,730,764). -/
def post (early : Bool) (f : List T → T) (xl : T) : T :=
  if early && !valid xl then xl else f [xl]

/-- `deg1_l2_ll0_lr0_eval` (src/Evaluate.jl:669-738): `op(op_l(a, b))` with
leaves `a`, `b`. -/
def deg1L2 (cx : Ctx) (X : JMat T) (f fl : List T → T) (ll lr : Tree T)
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  let n := X.ncols
  if isConstLeaf ll && isConstLeaf lr then
    let a := leafVal ll
    let c := leafVal lr
    retV cx X a (retV cx X c (fun b =>
      let xl := fl [a, c]
      retV cx X xl (fun b => let x := f [xl]; retV cx X x (filled X x) b) b)) b
  else if isConstLeaf ll then
    let a := leafVal ll
    retV cx X a (fun b => do
      chk X (leafFeat lr)
      let (cum, b') ← getArray b n
      let out ← simdWrite cum n (fun j => do
        let v ← featureAt X (leafFeat lr) j
        pure (post cx.earlyExit f (fl [a, v])))
      pure (⟨out, true, nextId b⟩, b')) b
  else if isConstLeaf lr then do
    chk X (leafFeat ll)
    let c := leafVal lr
    retV cx X c (fun b => do
      let (cum, b') ← getArray b n
      let out ← simdWrite cum n (fun j => do
        let v ← featureAt X (leafFeat ll) j
        pure (post cx.earlyExit f (fl [v, c])))
      pure (⟨out, true, nextId b⟩, b')) b
  else do
    chk X (leafFeat ll)
    chk X (leafFeat lr)
    let (cum, b') ← getArray b n
    let out ← simdWrite cum n (fun j => do
      let v1 ← featureAt X (leafFeat ll) j
      let v2 ← featureAt X (leafFeat lr) j
      pure (post cx.earlyExit f (fl [v1, v2])))
    pure (⟨out, true, nextId b⟩, b')

/-- `deg1_l1_ll0_eval` (src/Evaluate.jl:741-771): `op(op_l(a))` with leaf `a`. -/
def deg1L1 (cx : Ctx) (X : JMat T) (f fl : List T → T) (ll : Tree T)
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  if isConstLeaf ll then
    let a := leafVal ll
    retV cx X a (fun b =>
      let xl := fl [a]
      retV cx X xl (fun b => let x := f [xl]; retV cx X x (filled X x) b) b) b
  else do
    chk X (leafFeat ll)
    let (cum, b') ← getArray b X.ncols
    let out ← simdWrite cum X.ncols (fun j => do
      let v ← featureAt X (leafFeat ll) j
      pure (post cx.earlyExit f (fl [v])))
    pure (⟨out, true, nextId b⟩, b')

/-- `deg2_l0_r0_eval` (src/Evaluate.jl:861-921): `op(a, b)` with leaves. -/
def deg2L0R0 (cx : Ctx) (X : JMat T) (f : List T → T) (l r : Tree T)
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  let n := X.ncols
  if isConstLeaf l && isConstLeaf r then
    let a := leafVal l
    let c := leafVal r
    retV cx X a (retV cx X c (fun b => let x := f [a, c]; retV cx X x (filled X x) b)) b
  else if isConstLeaf l then do
    let (cum, b1) ← getArray b n
    let a := leafVal l
    retV cx X a (fun b2 => do
      chk X (leafFeat r)
      let out ← simdWrite cum n (fun j => do
        let v ← featureAt X (leafFeat r) j
        pure (f [a, v]))
      pure (⟨out, true, nextId b⟩, b2)) b1
  else if isConstLeaf r then do
    let (cum, b1) ← getArray b n
    chk X (leafFeat l)
    let c := leafVal r
    retV cx X c (fun b2 => do
      let out ← simdWrite cum n (fun j => do
        let v ← featureAt X (leafFeat l) j
        pure (f [v, c]))
      pure (⟨out, true, nextId b⟩, b2)) b1
  else do
    let (cum, b') ← getArray b n
    chk X (leafFeat l)
    chk X (leafFeat r)
    let out ← simdWrite cum n (fun j => do
      let v1 ← featureAt X (leafFeat l) j
      let v2 ← featureAt X (leafFeat r) j
      pure (f [v1, v2]))
    pure (⟨out, true, nextId b⟩, b')

/-- `deg2_l0_eval` (src/Evaluate.jl:923-951): `op(a, cumulator)` with leaf `a`;
the result is written into `cumulator` (identity `cid`). -/
def deg2L0 (cx : Ctx) (X : JMat T) (f : List T → T) (l : Tree T) (cum : JVec T) (cid : Ident)
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  if isConstLeaf l then
    let a := leafVal l
    retV cx X a (fun b => do
      let out ← inplaceMap cum (fun _ x => pure (f [a, x]))
      pure (⟨out, true, cid⟩, b)) b
  else do
    chk X (leafFeat l)
    let out ← inplaceMap cum (fun j x => do
      let v ← featureAt X (leafFeat l) j
      pure (f [v, x]))
    pure (⟨out, true, cid⟩, b)

/-- `deg2_r0_eval` (src/Evaluate.jl:953-980): `op(cumulator, c)` with leaf `c`;
the result is written into `cumulator` (identity `cid`). -/
def deg2R0 (cx : Ctx) (X : JMat T) (f : List T → T) (r : Tree T) (cum : JVec T) (cid : Ident)
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  if isConstLeaf r then
    let c := leafVal r
    retV cx X c (fun b => do
      let out ← inplaceMap cum (fun _ x => pure (f [x, c]))
      pure (⟨out, true, cid⟩, b)) b
  else do
    chk X (leafFeat r)
    let out ← inplaceMap cum (fun j x => do
      let v ← featureAt X (leafFeat r) j
      pure (f [x, v]))
    pure (⟨out, true, cid⟩, b)

/-- Which child holds the inner binary node in `deg2_branch0_eval`. -/
inductive Side where
  | left
  | right

/-- `_fused_binary3` (src/Evaluate.jl:773-793). -/
def fused3 (side : Side) (early : Bool) (f g : List T → T) (x1 x2 x3 : T) : T :=
  match side with
  | .left =>
    let bx := g [x1, x2]
    if early && (!valid bx || !valid x3) then (if valid bx then x3 else bx) else f [bx, x3]
  | .right =>
    let bx := g [x2, x3]
    if early && (!valid x1 || !valid bx) then (if valid x1 then bx else x1) else f [x1, bx]

/- Source: src/Evaluate.jl:819-837
    index_style = IndexStyle(typeof(cX))
    ok, features, values, bounds = branch0_leaves(tree, Val(side), eval_context.early_exit)
    cumulator = get_array(eval_context.buffer, cX, axes(cX, 2))
    ok || return ResultOk(cumulator, false)
    feature1, feature2, feature3 = features
    value1, value2, value3 = values
    bound1, bound2, bound3 = bounds
    input1_index = first_feature_index(cX, feature1)
    input2_index = first_feature_index(cX, feature2)
    input3_index = first_feature_index(cX, feature3)
    feature_stride = size(cX, 1)
    constant1, constant2, constant3 = map(==(-1), bounds)
    if side === :left && constant1 && constant2
        val_branch = branch_op(value1, value2)::T
        @return_on_nonfinite_val(eval_context, val_branch, cX)
    elseif side === :right && constant2 && constant3
        val_branch = branch_op(value2, value3)::T
        @return_on_nonfinite_val(eval_context, val_branch, cX)
    end
-/
/-- `deg2_branch0_eval` (src/Evaluate.jl:795-858). Each constant has a
dummy feature index of 1; `ifelse` also evaluates that feature read.
The first slot is reserved before checking bounds. The invalid constant
pair in the inner branch takes the early-return macro's second slot. -/
def branch0 (cx : Ctx) (X : JMat T) (f g : List T → T) (side : Side) (l1 l2 l3 : Tree T)
    (b : Buf T) : Jl (ResultOk T × Buf T) := do
  let n := X.ncols
  let bad (ℓ : Tree T) : Bool := cx.earlyExit && isConstLeaf ℓ && !valid (leafVal ℓ)
  let (cum, b') ← getArray b n
  if bad l1 || bad l2 || bad l3 then
    pure (⟨cum, false, nextId b⟩, b')
  else do
    let feat (ℓ : Tree T) : Nat := if isConstLeaf ℓ then 1 else leafFeat ℓ
    chk X (feat l1)
    chk X (feat l2)
    chk X (feat l3)
    let value (ℓ : Tree T) : T := if isConstLeaf ℓ then leafVal ℓ else JlScalar.zero
    let pick (ℓ : Tree T) (j : Nat) : Jl T := do
      let a ← featureAt X (feat ℓ) j
      pure (if isConstLeaf ℓ then value ℓ else a)
    let body (c : Buf T) : Jl (ResultOk T × Buf T) := do
      let out ← simdWrite cum n (fun j => do
        let x1 ← pick l1 j
        let x2 ← pick l2 j
        let x3 ← pick l3 j
        pure (fused3 side cx.earlyExit f g x1 x2 x3))
      pure (⟨out, true, nextId b⟩, c)
    match side with
    | .left => retVIf cx X (isConstLeaf l1 && isConstLeaf l2) (g [value l1, value l2]) body b'
    | .right => retVIf cx X (isConstLeaf l2 && isConstLeaf l3) (g [value l2, value l3]) body b'

/-- Child evaluation followed by `!result.ok && return result` and
`@return_on_nonfinite_array` (src/Evaluate.jl:26-32, e.g. :616-618). The
continuation receives the child's array and its identity. -/
def checked (cx : Ctx) (ev : Buf T → Jl (ResultOk T × Buf T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) :
    Jl (ResultOk T × Buf T) := do
  let (r, b) ← ev b
  if !r.ok then pure (r, b)
  else if cx.earlyExit && !isValidArray r.x then pure (⟨r.x, false, r.id⟩, b)
  else k r.x r.id b

/-- Unfused unary evaluation `deg1_eval(result.x, op)` (src/Evaluate.jl:359-363,
583-586, 616-619); the operator is looked up after the child for the long
compilation path. -/
def unfused1 (cx : Ctx) (fop : Jl (List T → T)) (evC : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  checked cx evC (fun x cid b => do
    let f ← fop
    let out ← degnEval f [x]
    pure (⟨out, true, cid⟩, b)) b

/-- `dispatch_deg1_eval` (src/Evaluate.jl:575-627). -/
def deg1Dispatch (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat) (c : Tree T)
    (evC : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) : Jl (ResultOk T × Buf T) :=
  let unaops := opsOf o 1
  if operatorLimit < unaops.length then unfused1 cx (idxOp unaops op) evC b
  else do
    let f ← nifOp unaops op
    match c with
    | .branch lop [ll, lr] =>
      if cx.useFused && isLeaf ll && isLeaf lr then do
        let fl ← nifOp (opsOf o 2) lop
        deg1L2 cx X f fl ll lr b
      else unfused1 cx (pure f) evC b
    | .branch lop [ll] =>
      if cx.useFused && isLeaf ll then do
        let fl ← nifOp unaops lop
        deg1L1 cx X f fl ll b
      else unfused1 cx (pure f) evC b
    | _ => unfused1 cx (pure f) evC b

/-- Unfused binary evaluation (src/Evaluate.jl:473-480, 536-545). -/
def unfused2 (cx : Ctx) (fop : Jl (List T → T)) (evL evR : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) : Jl (ResultOk T × Buf T) :=
  checked cx evL (fun xl cid => checked cx evR (fun xr _ b => do
    let f ← fop
    let out ← degnEval f [xl, xr]
    pure (⟨out, true, cid⟩, b))) b

/-- `dispatch_deg2_eval` (src/Evaluate.jl:464-553). -/
def deg2Dispatch (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat) (l r : Tree T)
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) : Jl (ResultOk T × Buf T) :=
  let binops := opsOf o 2
  if operatorLimit < binops.length then unfused2 cx (idxOp binops op) evL evR b
  else do
    let f ← nifOp binops op
    let r0path := checked cx evL (fun xl cid b => deg2R0 cx X f r xl cid b) b
    let l0path := checked cx evR (fun xr cid b => deg2L0 cx X f l xr cid b) b
    if cx.useFused && isLeaf l && isLeaf r then deg2L0R0 cx X f l r b
    else if cx.useFused && isLeaf r then
      match l with
      | .branch lop [ll, lr] =>
        if isNum T && isLeaf ll && isLeaf lr then do
          let g ← nifOp binops lop
          branch0 cx X f g .left ll lr r b
        else r0path
      | _ => r0path
    else if cx.useFused && isLeaf l then
      match r with
      | .branch rop [rl, rr] =>
        if isNum T && isLeaf rl && isLeaf rr then do
          let g ← nifOp binops rop
          branch0 cx X f g .right l rl rr b
        else l0path
      | _ => l0path
    else unfused2 cx (pure f) evL evR b

/-- Completion of `inner_dispatch_degn_eval` after the children
(src/Evaluate.jl:430-438); the result is written into the first cumulator. -/
def degnFinish (o : OpEnum T) (d op : Nat)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)) : Jl (ResultOk T × Buf T) :=
  match res with
  | .inl r => pure r
  | .inr (xs, b) => do
    let f ← nifOp (opsOf o d) op
    let out ← degnEval f (xs.map Prod.fst)
    pure (⟨out, true, (xs.head?.map Prod.snd).getD .fresh⟩, b)

/- Source: src/Evaluate.jl:319-328
    elseif is_constant(tree)
        # Speed hack for constant trees.
        const_result =
            dispatch_constant_tree(tree, operators, eval_context.early_exit)::ResultOk{T}
        eval_context.early_exit isa Val{true} &&
            !const_result.ok &&
            return ResultOk(get_array(eval_context.buffer, cX, axes(cX, 2)), false)
        return ResultOk(
            get_filled_array(eval_context.buffer, const_result.x, cX, axes(cX, 2)), true
        )
-/
/-- Constant-tree shortcut in `_eval_tree_array` (src/Evaluate.jl:319-328). -/
def constPath (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (early : Bool := true) : Jl (ResultOk T × Buf T) :=
  match constEval o t early with
  | .error e => .error e
  | .ok (v, ok) =>
    if early && !ok then do
      let (a, b') ← getArray b X.ncols
      pure (⟨a, false, nextId b⟩, b')
    else filled X v b

mutual
/-- `_eval_tree_array` (src/Evaluate.jl:309-338); leaves go through
`deg0_eval` (src/Evaluate.jl:368-380), where a constant leaf reports its own
validity under early exit and a feature leaf is bounds-checked. -/
def evalT (cx : Ctx) (o : OpEnum T) (X : JMat T) : Tree T → Buf T → Jl (ResultOk T × Buf T)
  | .const v, b => do
    let (a, b') ← getFilled b v X.ncols
    pure (⟨a, !cx.earlyExit || valid v, nextId b⟩, b')
  | .feature f, b => do
    chk X f
    let (a, b') ← getFeature b X f
    pure (⟨a, true, nextId b⟩, b')
  | .branch op cs, b =>
    if isConstantL cs then constPath o X (.branch op cs) b cx.earlyExit
    else match cs with
      | [c] => deg1Dispatch cx o X op c (evalT cx o X c) b
      | [l, r] => deg2Dispatch cx o X op l r (evalT cx o X l) (evalT cx o X r) b
      | l :: r :: rest =>
        if cx.D = 2 then deg2Dispatch cx o X op l r (evalT cx o X l) (evalT cx o X r) b
        else do
          let res ← evalChildren cx o X (l :: r :: rest) b
          degnFinish o (rest.length + 2) op res
      | [] => .error (.undefinedBehavior "branch without children")
/-- The children loop of `inner_dispatch_degn_eval` (src/Evaluate.jl:421-429). -/
def evalChildren (cx : Ctx) (o : OpEnum T) (X : JMat T) :
    List (Tree T) → Buf T → Jl ((ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T))
  | [], b => .ok (.inr ([], b))
  | c :: cs, b => do
    let (r, b) ← evalT cx o X c b
    if !r.ok then pure (.inl (r, b))
    else if cx.earlyExit && !isValidArray r.x then pure (.inl (⟨r.x, false, r.id⟩, b))
    else do
      match ← evalChildren cx o X cs b with
      | .inl e => pure (.inl e)
      | .inr (xs, b') => pure (.inr ((r.x, r.id) :: xs, b'))
end

/-- The return statement of `eval_tree_array` (src/Evaluate.jl:276-280). -/
def evalArr (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T) :
    Jl (JVec T × Bool) := do
  let (r, _) ← evalT cx o X t b
  pure (r.x, r.ok && (!cx.earlyExit || isValidArray r.x))

/-- `EvalContext` (src/Evaluate.jl:142-148). The `bumper` field is deprecated
and has no effect (src/Evaluate.jl:123). -/
structure EvalContext (T : Type) where
  turbo : Bool
  bumper : Bool
  earlyExit : Bool
  buffer : Buf T
  useFused : Bool

/-- Keyword constructor `EvalContext(; ...)` (src/Evaluate.jl:150-162). -/
def mkEvalContext (turbo : Bool := false) (_bumper : Bool := false) (earlyExit : Bool := true)
    (buffer : Buf T := .none) (useFused : Bool := true) : Jl (EvalContext T) :=
  .ok ⟨turbo, false, earlyExit, buffer, useFused⟩

/-- Which optional extensions are loaded (src/ExtensionInterface.jl:5,56). -/
structure Ext where
  symbolicUtils : Bool := false
  zygote : Bool := false
  loopVectorization : Bool := false

/-- Extension implementations, opaque to the base package. `turboEval` is
`_eval_tree_array` with LoopVectorization kernels. -/
structure ExtImpl (T : Type) where
  turboEval : Tree T → JMat T → Jl (ResultOk T)

/-- `_eval_tree_array_fast(tree, X, ::OperatorEnum, eval_context::EvalContext{false})`
(`src/Evaluate.jl:260-271`): positional non-turbo entry point equivalent to
`eval_tree_array` with `turbo = false`. -/
def evalTreeArrayFast (D : Nat) (t : Tree T) (X : JMat T) (o : OpEnum T)
    (ec : EvalContext T) : Jl (JVec T × Bool) :=
  evalArr ⟨ec.earlyExit, ec.useFused, D⟩ o X t ec.buffer

/-- `eval_tree_array(tree, X, ::OperatorEnum; eval_context)` (src/Evaluate.jl:273-294)
for a tree of node type with maximum degree `D`. -/
def evalTreeArray (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T) (X : JMat T)
    (o : OpEnum T) (ec : EvalContext T) : Jl (JVec T × Bool) :=
  if ec.turbo && !JlScalar.isFloat (T := T) then
    .error (.assertionError "T in (Float32, Float64)")
  else if ec.turbo && !ext.loopVectorization then
    .error (.errorException "Please load the LoopVectorization.jl package to use this feature.")
  else if ec.turbo then do
    let r ← impl.turboEval t X
    pure (r.x, r.ok && (!ec.earlyExit || isValidArray r.x))
  else evalArr ⟨ec.earlyExit, ec.useFused, D⟩ o X t ec.buffer

/-- `reshape(cX, (size(cX, 1), 1))` (src/Evaluate.jl:285). -/
def colMatrix (v : JVec T) : JMat T := ⟨v.size, 1, v, by simp⟩

/-- Vector-input overload (src/Evaluate.jl:282-286). -/
def evalTreeArrayVec (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T) (v : JVec T)
    (o : OpEnum T) (ec : EvalContext T) : Jl (JVec T × Bool) :=
  evalTreeArray ext impl D t (colMatrix v) o ec

mutual
/-- Elementwise conversion of a tree, `convert(with_type_parameters(...), tree)`
(src/Evaluate.jl:295). -/
def mapTree {A B : Type} (g : A → B) : Tree A → Tree B
  | .const v => .const (g v)
  | .feature f => .feature f
  | .branch op cs => .branch op (mapTreeL g cs)
/-- Children conversion for `mapTree`. -/
def mapTreeL {A B : Type} (g : A → B) : List (Tree A) → List (Tree B)
  | [] => []
  | c :: cs => mapTree g c :: mapTreeL g cs
end

/-- Elementwise conversion of a matrix, `Base.Fix1(convert, T).(cX)` (src/Evaluate.jl:296). -/
def mapMat {A B : Type} (g : A → B) (X : JMat A) : JMat B :=
  ⟨X.nrows, X.ncols, X.data.map g, by simp [X.size_eq]⟩

/-- Mixed-type overload (src/Evaluate.jl:288-298): promote both arguments to
`T = promote_type(T1, T2)` through the conversions `c1`, `c2`, then evaluate. -/
def evalTreeArrayMixed {T1 T2 : Type} (c1 : T1 → T) (c2 : T2 → T) (ext : Ext)
    (impl : ExtImpl T) (D : Nat) (t : Tree T1) (X : JMat T2) (o : OpEnum T)
    (ec : EvalContext T) : Jl (JVec T × Bool) :=
  evalTreeArray ext impl D (mapTree c1 t) (mapMat c2 X) o ec

/-- Decidable equality of Julia call results, used to check concrete runs. -/
instance instDecEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

/-- Observable form of an evaluation result, with the array as a list
(array equality does not reduce in the kernel). -/
def obs {T : Type} (r : Jl (JVec T × Bool)) : Jl (List T × Bool) :=
  r.map fun p => (p.1.toList, p.2)

end DynExpr.Eval
