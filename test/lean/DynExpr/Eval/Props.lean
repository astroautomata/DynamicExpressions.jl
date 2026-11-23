import DynExpr.Eval.Core
import DynExpr.Eval.Generic
import DynExpr.Eval.Helpers

/-!
Specifications and property statements for the evaluator slice.
-/

namespace DynExpr.Eval

section spec
variable {T : Type} [JlScalar T]

/-- Feature values of sample `j` of a features-by-samples matrix, as read by
`Tree.denoteRow`. -/
def col (X : JMat T) (j : Nat) : Nat → Option T := fun f => (X.get? f j).toOption

/-- Every node of `t`, leaves included, has a defined valid value under the
feature assignment `x` ("every intermediate is valid"). -/
def AllValid (o : OpEnum T) (x : Nat → Option T) : Tree T → Prop
  | .const v => valid v = true
  | .feature i => ∃ v, x i = some v ∧ valid v = true
  | .branch op cs =>
    (∀ c ∈ cs, AllValid o x c) ∧ ∃ v, (Tree.branch op cs).denote o x = some v ∧ valid v = true

/-- `is_valid_array` accepts arrays whose elements are all valid (true for
every element type on master, src/ValueInterface.jl:17-21). -/
def ArrayValidSound (T : Type) [JlScalar T] : Prop :=
  ∀ a : JVec T, (∀ x ∈ a.toList, valid x = true) → isValidArray a = true

/-- `is_valid_array` holds exactly for arrays of valid elements. -/
def ArrayValidExact (T : Type) [JlScalar T] : Prop :=
  ∀ a : JVec T, isValidArray a = true ↔ ∀ x ∈ a.toList, valid x = true

/-- `EvalContext(; early_exit, use_fused, buffer)` with turbo and bumper off. -/
def plainCtx (early fused : Bool) (b : Buf T) : EvalContext T := ⟨false, false, early, b, fused⟩

/-- Output `out` holds the denotation of `t` at every sample. -/
def Denotes (o : OpEnum T) (X : JMat T) (t : Tree T) (out : JVec T) : Prop :=
  out.size = X.ncols ∧ ∀ j, 1 ≤ j → j ≤ X.ncols → out[j - 1]? = t.denoteRow o X j

/-- Buffers that can serve every slot a tree of `t.size` nodes may request:
none, a vector-backed buffer, or a matrix with one column per sample and at
least `t.size` unused rows. -/
def BufferFits (X : JMat T) (t : Tree T) (b : Buf T) : Prop :=
  b = .none ∨ (∃ arrs i, b = .vec arrs i) ∨
    ∃ A i, b = .mat A i ∧ A.ncols = X.ncols ∧ i + t.size ≤ A.nrows

/-- `buffer.index[]` (0 for `nothing`). -/
def Buf.idx : Buf T → Nat
  | .none => 0
  | .mat _ i => i
  | .vec _ i => i

/-- Feature assignment of a vector input reshaped to one sample. -/
def vecAssign (v : JVec T) (f : Nat) : Option T := if 1 ≤ f then v[f - 1]? else none

/-! Input-level preconditions. -/

/-- Every input matrix entry is valid (finite). -/
def XFinite (X : JMat T) : Prop := ∀ x ∈ X.data.toList, valid x = true

mutual
/-- Every constant leaf satisfies `p`. -/
def constsOK (p : T → Bool) : Tree T → Bool
  | .const v => p v
  | .feature _ => true
  | .branch _ cs => constsOKL p cs
/-- List version of `constsOK`. -/
def constsOKL (p : T → Bool) : List (Tree T) → Bool
  | [] => true
  | c :: cs => constsOK p c && constsOKL p cs
end

/-- Every constant leaf of the tree is valid (finite). -/
def ConstsFinite (t : Tree T) : Prop := constsOK valid t = true

/-- Every operator maps valid arguments to a valid result (e.g. `+`, `*`,
`sin`, `tanh`; not `/`, `exp`, `log`). -/
def OpsFinite (o : OpEnum T) : Prop :=
  ∀ d op f, o.lookup d op = some f → ∀ args : List T, (∀ a ∈ args, valid a = true) →
    valid (f args) = true

mutual
/-- No branch node has only constant leaves below it (no constant subexpression
other than single constants). -/
def noConstBranch : Tree T → Bool
  | .branch _ cs => !isConstantL cs && noConstBranchL cs
  | _ => true
/-- List version of `noConstBranch`. -/
def noConstBranchL : List (Tree T) → Bool
  | [] => true
  | c :: cs => noConstBranch c && noConstBranchL cs
end

/-- Every unary operator returns an invalid argument unchanged (as IEEE
functions do for NaN). -/
def UnaryKeepsInvalid (o : OpEnum T) : Prop :=
  ∀ op f, o.lookup 1 op = some f → ∀ x : T, valid x = false → f [x] = x

/-- Every generic operator has a method for all arguments and never throws. -/
def GOpsTotal {V : Type} (o : GOpEnum V) : Prop :=
  ∀ d, ∀ g ∈ gopsOf o d, (∀ args, g.hasMethod args = true) ∧
    (∀ args, g.hasMethodArr args = true) ∧ ∀ args, ∃ v, g.call args = .ok v

end spec

/-- eval-denote: for well-formed trees and inputs where every intermediate
value is valid, `eval_tree_array` returns the denotation at every sample and
completes, for every `early_exit`/`use_fused` setting. -/
def evalDenoteAV : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) →
    ∃ out, evalTreeArray ext impl D t X o (plainCtx early fused .none) = .ok (out, true) ∧
      Denotes o X t out

/-- eval-buffer: evaluating with an `ArrayBuffer` that fits gives exactly the
unbuffered result. -/
def evalBufferAV : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) → BufferFits X t b →
    evalTreeArray ext impl D t X o (plainCtx early fused b) =
      evalTreeArray ext impl D t X o (plainCtx early fused .none)

/-- eval-constant: a tree without feature leaves whose values are all valid
fills every sample (also with zero samples) with its value and completes. -/
def evalConstantAV : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidSound T → t.WF D o.nops X.nrows → isConstant t = true →
    AllValid o (fun _ => none) t →
    ∃ v, t.denote o (fun _ => none) = some v ∧
      evalTreeArray ext impl D t X o (plainCtx early fused .none) =
        .ok (JVec.fill X.ncols v, true)

/-- eval-unfused-flag: with `use_fused=false` and `early_exit=true`, the call
returns, its flag is true exactly when every intermediate value at every
sample is valid, and a true flag comes with the denotation. -/
def evalUnfusedFlag : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    ∃ out ok, evalTreeArray ext impl D t X o (plainCtx true false .none) = .ok (out, ok) ∧
      (ok = true ↔ ∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) ∧
      (ok = true → Denotes o X t out)

/-- eval-fused-flag-agree (documented behaviour of `use_fused`, PR #276): with
`early_exit=true` the fused kernels check only their outputs, so the fused flag
is never stricter than the unfused one (whenever `use_fused=false` completes,
`use_fused=true` completes with the same output), and the two flags agree when
every input entry is finite. -/
def evalFusedFlagAgree : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    (∀ out, evalTreeArray ext impl D t X o (plainCtx true false .none) = .ok (out, true) →
      evalTreeArray ext impl D t X o (plainCtx true true .none) = .ok (out, true)) ∧
    (XFinite X →
      (evalTreeArray ext impl D t X o (plainCtx true true .none)).map Prod.snd =
        (evalTreeArray ext impl D t X o (plainCtx true false .none)).map Prod.snd)

/-- eval-noearly-fused-agree: with `early_exit=false` the output does not
depend on `use_fused`. -/
def evalNoEarlyFusedAgree : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → noConstBranch t = true →
    (evalTreeArray ext impl D t X o (plainCtx false true .none)).map (·.1.toList) =
      (evalTreeArray ext impl D t X o (plainCtx false false .none)).map (·.1.toList)

/-- eval-noearly-denote: with `early_exit=false` (and no fusion) evaluation of
a non-constant tree never terminates early: it completes and returns the
elementwise denotation, valid or not. -/
def evalNoEarlyDenote : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → isConstant t = false →
    ∃ out, evalTreeArray ext impl D t X o (plainCtx false false .none) = .ok (out, true) ∧
      Denotes o X t out

/-- eval-zero-samples-leaf: with zero samples and no constant subexpression,
the completion flag does not depend on `use_fused`. -/
def evalZeroSamplesLeaf : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → X.ncols = 0 → t.WF D o.nops X.nrows → noConstBranch t = true →
    (evalTreeArray ext impl D t X o (plainCtx true true .none)).map Prod.snd =
      (evalTreeArray ext impl D t X o (plainCtx true false .none)).map Prod.snd

/-- eval-zero-samples-pair: with zero samples and finite constants, the
completion flag does not depend on `use_fused`. -/
def evalZeroSamplesPair : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → X.ncols = 0 → t.WF D o.nops X.nrows → ConstsFinite t →
    (evalTreeArray ext impl D t X o (plainCtx true true .none)).map Prod.snd =
      (evalTreeArray ext impl D t X o (plainCtx true false .none)).map Prod.snd

/-- eval-feature-oob: evaluation never has undefined behaviour (an unchecked
out-of-bounds read) for any feature index below 65536; an index beyond the
input rows must raise an error instead. -/
def evalFeatureOOB : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops 65535 →
    ∀ m, evalTreeArray ext impl D t X o (plainCtx early fused .none) ≠
      .error (.undefinedBehavior m)

/-- eval-wide-buffer: a matrix buffer with at least one column per sample and
enough free rows gives the unbuffered result. -/
def evalWideBuffer : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (A : JMat T) (i : Nat),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    XFinite X → ConstsFinite t → OpsFinite o →
    X.ncols ≤ A.ncols → i + t.size ≤ A.nrows →
    (evalTreeArray ext impl D t X o (plainCtx early fused (.mat A i))).map (·.1.toList) =
      (evalTreeArray ext impl D t X o (plainCtx early fused .none)).map (·.1.toList)

/-- eval-small-buffer: a matrix buffer with one column per sample never leads
to undefined behaviour; running out of slots raises an exception. -/
def evalSmallBuffer : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (A : JMat T) (i : Nat),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → A.ncols = X.ncols →
    ∀ m, evalTreeArray ext impl D t X o (plainCtx early fused (.mat A i)) ≠
      .error (.undefinedBehavior m)

/-- eval-vector: a vector input is one sample whose features are its entries. -/
def evalVectorAV : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (v : JVec T) (t : Tree T),
    ArrayValidSound T → t.WF D o.nops v.size → AllValid o (vecAssign v) t →
    ∃ w, t.denote o (vecAssign v) = some w ∧
      (evalTreeArrayVec ext impl D t v o (plainCtx early fused .none)).map (·.1.toList) =
        .ok [w] ∧
      (evalTreeArrayVec ext impl D t v o (plainCtx early fused .none)).map Prod.snd = .ok true

/-- eval-mixed: the mixed-type overload evaluates the promoted tree on the
promoted matrix, so it returns the promoted denotation. -/
def evalMixedAV : Prop :=
  ∀ (T1 T2 T : Type) [JlScalar T] (c1 : T1 → T) (c2 : T2 → T) (ext : Ext) (impl : ExtImpl T)
    (D : Nat) (early fused : Bool) (o : OpEnum T) (X : JMat T2) (t : Tree T1),
    ArrayValidSound T → 1 ≤ X.ncols → (mapTree c1 t).WF D o.nops X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col (mapMat c2 X) j) (mapTree c1 t)) →
    ∃ out, evalTreeArrayMixed c1 c2 ext impl D t X o (plainCtx early fused .none) =
        .ok (out, true) ∧ Denotes o (mapMat c2 X) (mapTree c1 t) out

/-- eval-context: `EvalContext(; bumper=true, buffer)` accepts a buffer, the
deprecated `bumper` option is cleared and has no effect on `eval_tree_array`, and with
`turbo=true` but without LoopVectorization loaded `eval_tree_array` raises
the documented error (for `Float32`/`Float64`). -/
def evalContextExt : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (turbo early fused : Bool) (b : Buf T),
    mkEvalContext false true early b fused = .ok ⟨false, false, early, b, fused⟩ ∧
    evalTreeArray ext impl D t X o ⟨turbo, true, early, b, fused⟩ =
      evalTreeArray ext impl D t X o ⟨turbo, false, early, b, fused⟩ ∧
    (JlScalar.isFloat (T := T) = true → ext.loopVectorization = false →
      evalTreeArray ext impl D t X o ⟨true, false, early, b, fused⟩ =
        .error (.errorException "Please load the LoopVectorization.jl package to use this feature."))

/-- eval-turbo-nonnumeric: with LoopVectorization loaded, `turbo=true` on a
non-numeric element type is rejected before evaluation, by the
`T in (Float32, Float64)` assertion (src/Evaluate.jl:267-269). -/
def evalTurboNonNumeric : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (early fused : Bool) (b : Buf T),
    isNum T = false → (JlScalar.isFloat (T := T) = true → isNum T = true) →
    ext.loopVectorization = true →
    evalTreeArray ext impl D t X o ⟨true, false, early, b, fused⟩ =
      .error (.assertionError "T in (Float32, Float64)")

/-- eval-diff-flag: a true flag from `differentiable_eval_tree_array` means
every output value is valid. -/
def evalDiffFlag : Prop :=
  ∀ (T : Type) [JlScalar T] (o : OpEnum T) (X : JMat T) (t : Tree T) (out : List T),
    t.WF 2 o.nops X.nrows → (∀ v : T, JlScalar.mul JlScalar.one v = v) →
    ArrayValidExact T →
    obs (differentiableEvalTreeArray o X t) = .ok (out, true) → ∀ x ∈ out, valid x = true

/-- eval-diff-denote: if every intermediate is valid and `one(T) * v == v`,
`differentiable_eval_tree_array` returns the denotation and completes. -/
def evalDiffDenoteAV : Prop :=
  ∀ (T : Type) [JlScalar T] (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T),
    (∀ v : T, JlScalar.mul JlScalar.one v = v) → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) →
    ∃ out, differentiableEvalTreeArray o X t = .ok (out, true) ∧ Denotes o X t out

section generic
variable {V : Type}

mutual
/-- Successful generic evaluation of `t` to `v` at feature assignment `x`:
every operator is found by its one-based index, has a method for its
arguments, and returns without throwing. -/
inductive GOk (o : GOpEnum V) (x : Nat → Option V) : Tree V → V → Prop
  | const (v : V) : GOk o x (.const v) v
  | feature (f : Nat) (v : V) : x f = some v → GOk o x (.feature f) v
  | branch (op : Nat) (cs : List (Tree V)) (vs : List V) (g : GOp V) (v : V) :
      GOkL o x cs vs → (gopsOf o cs.length)[op - 1]? = some g → 1 ≤ op →
      g.hasMethod vs = true → g.call vs = .ok v → GOk o x (.branch op cs) v
/-- Children of a successful generic evaluation. -/
inductive GOkL (o : GOpEnum V) (x : Nat → Option V) : List (Tree V) → List V → Prop
  | nil : GOkL o x [] []
  | cons (c : Tree V) (cs : List (Tree V)) (v : V) (vs : List V) :
      GOk o x c v → GOkL o x cs vs → GOkL o x (c :: cs) (v :: vs)
end

/-- Generic evaluation of a matrix input succeeds at sample `j` with value
`v`, broadcasting each operator over samples (`throw_errors=true` skips the
`hasmethod` check). -/
def genSample (X : JMat V) (j : Nat) : Nat → Option V :=
  fun f => (X.get? f j).toOption

end generic

/-- eval-generic-vector: when no operator fails, the generic evaluator on a
vector input returns the scalar value with flag true, whatever `throw_errors`. -/
def evalGenericVectorAV : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (throw : Bool) (x : JVec V) (t : Tree V) (v : V),
    GOk o (fun f => if 1 ≤ f then x[f - 1]? else none) t v →
    genEvalVec o throw t x = .ok (some v, true)

/-- eval-generic-matrix: with `throw_errors=true`, when every sample
evaluates without failure, the generic evaluator on a matrix returns the
per-sample values (slicing features along the first axis). -/
def evalGenericMatrixAV : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (X : JMat V) (t : Tree V) (vs : Nat → V),
    t.WF 255 (fun d => (gopsOf o d).length) X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → GOk o (genSample X j) t (vs j)) →
    ∃ out, genEvalMat o true t X = .ok (some out, true) ∧ out.size = X.ncols ∧
      ∀ j, 1 ≤ j → j ≤ X.ncols → out[j - 1]? = some (vs j)

/-- eval-generic-throw: with `throw_errors=false` the generic evaluator never
throws, and a false flag comes with `nothing`; with `throw_errors=true` every
failure is an `ErrorException`. -/
def evalGenericThrow : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (x : JVec V) (X : JMat V) (t : Tree V),
    (∃ r, genEvalVec o false t x = .ok r ∧ (r.2 = false → r.1 = none)) ∧
    (∃ r, genEvalMat o false t X = .ok r ∧ (r.2 = false → r.1 = none)) ∧
    (∀ e, genEvalVec o true t x = .error e → ∃ m, e = .errorException m) ∧
    (∀ e, genEvalMat o true t X = .error e → ∃ m, e = .errorException m)

/-- eval-callable: `tree(X, operators)` never raises for in-range features,
returns one value per sample, and returns exactly the `eval_tree_array`
output when it completes and `invalid_value(T)` at every sample otherwise. -/
def evalCallable : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (inv : T),
    JlScalar.invalid? (T := T) = some inv → t.WF D o.nops X.nrows →
    ∃ y ok out, evalTreeArray ext impl D t X o (plainCtx early fused .none) = .ok (y, ok) ∧
      callTree (evalTreeArray ext impl D t X o (plainCtx early fused .none)) = .ok out ∧
      out.size = X.ncols ∧ (ok = true → out = y) ∧ (ok = false → out = JVec.fill X.ncols inv)

/-- eval-callable-generic: `tree(x, operators::GenericOperatorEnum;
throw_errors=false)` on a vector returns the value the tree denotes whenever
every operator application along the tree has a method and succeeds (which
eval-generic-vector shows for total operators). -/
def evalCallableGeneric : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (x : JVec V) (t : Tree V) (v : V),
    GOk o (fun f => if 1 ≤ f then x[f - 1]? else none) t v →
      callTreeGeneric (genEvalVec o false t x) = .ok (some v)

/-- eval-adjoint: `tree'(X, operators)` returns the gradient of
`eval_grad_tree_array` when it completes, and otherwise a same-shape matrix of
`invalid_value(T)`; with a `GenericOperatorEnum` it raises an error. -/
def evalAdjoint : Prop :=
  ∀ (T : Type) [JlScalar T] (evalGrad : Tree T → JMat T → OpEnum T → Jl (JVec T × JMat T × Bool))
    (t : Tree T) (X : JMat T) (o : OpEnum T) (inv : T),
    JlScalar.invalid? (T := T) = some inv →
    (∀ y g, evalGrad t X o = .ok (y, g, true) → adjointTree evalGrad t X o = .ok g) ∧
    (∀ y g, evalGrad t X o = .ok (y, g, false) → ∃ g', adjointTree evalGrad t X o = .ok g' ∧
        g'.nrows = g.nrows ∧ g'.ncols = g.ncols ∧ ∀ z ∈ g'.data.toList, z = inv) ∧
    (gradEvaluatorGeneric (α := JMat T) =
      .error (.errorException "Gradients are not implemented for `GenericOperatorEnum`."))

/-- eval-ext-fallbacks: each extension entry point raises its documented error
when the extension is not loaded and forwards to the extension otherwise. -/
def evalExtFallbacks : Prop :=
  ∀ (α β : Type) (impl : α → Jl β) (a : α),
    nodeToSymbolic {} impl a =
      .error (.errorException "Please load the `SymbolicUtils` package to use `node_to_symbolic`.") ∧
    symbolicToNode {} impl a =
      .error (.errorException "Please load the `SymbolicUtils` package to use `symbolic_to_node`.") ∧
    zygoteGradient {} impl a = .error (.errorException "Please load the Zygote.jl package.") ∧
    nodeToSymbolic { symbolicUtils := true } impl a = impl a ∧
    symbolicToNode { symbolicUtils := true } impl a = impl a ∧
    zygoteGradient { zygote := true } impl a = impl a

/-- eval-alias-fresh: without a buffer, `_eval_tree_array` returns a freshly
allocated array for every tree and input (never `X`, a row of `X`, or storage
reachable from the tree), so mutating the output, as `tree(X)` does on
failure, cannot change the inputs. -/
def evalAliasFresh : Prop :=
  ∀ (T : Type) [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T),
    t.WF cx.D o.nops X.nrows →
    ∃ r, evalT cx o X t .none = .ok (r, .none) ∧ r.id = .fresh

/-- eval-alias-slots: with an `ArrayBuffer`, the output is a slot handed out
during this call (above the starting index, at most the final index), and the
buffer stays an `ArrayBuffer`. -/
def evalAliasSlots : Prop :=
  ∀ (T : Type) [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (b : Buf T),
    t.WF cx.D o.nops X.nrows → BufferFits X t b → b.isNone = false →
    ∃ r b', evalT cx o X t b = .ok (r, b') ∧
      b'.isNone = false ∧ ∃ k, r.id = .slot k ∧ b.idx < k ∧ k ≤ b'.idx

/-- eval-alias-successive: two evaluations sharing an `ArrayBuffer` without
`reset_index!` in between never return the same slot. -/
def evalAliasSuccessive : Prop :=
  ∀ (T : Type) [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T) (t1 t2 : Tree T)
    (b : Buf T),
    t1.WF cx.D o.nops X.nrows → t2.WF cx.D o.nops X.nrows →
    ((∃ arrs i, b = .vec arrs i) ∨
      ∃ A i, b = .mat A i ∧ A.ncols = X.ncols ∧ i + t1.size + t2.size ≤ A.nrows) →
    ∃ r1 b1 r2 b2, evalT cx o X t1 b = .ok (r1, b1) ∧
      evalT cx o X t2 b1 = .ok (r2, b2) ∧ r1.id ≠ r2.id

/-- eval-generic-exposure: on a vector input the generic evaluator returns a
feature leaf's input element and a constant leaf's own value without copying
(`cX[tree.feature]`, `tree.val`; Julia `===`); for a matrix input a constant
leaf fills every sample with the tree's value. -/
def evalGenericExposure : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (throw : Bool) (x : JVec V) (X : JMat V) (f : Nat) (v : V),
    (1 ≤ f → f ≤ x.size → genEvalVec o throw (.feature f) x = .ok (x[f - 1]?, true)) ∧
    genEvalVec o throw (.const v) x = .ok (some v, true) ∧
    genEvalMat o throw (.const v) X = .ok (some (JVec.fill X.ncols v), true)

/-! Registered properties with input-level preconditions, and companions of
the refuted properties. -/

/-- eval-denote: for well-formed trees, finite inputs, finite constants and
operators mapping finite arguments to finite values, `eval_tree_array` returns
the denotation at every sample and completes, for every `early_exit` and
`use_fused` setting. -/
def evalDenote : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    XFinite X → ConstsFinite t → OpsFinite o →
    ∃ out, evalTreeArray ext impl D t X o (plainCtx early fused .none) = .ok (out, true) ∧
      Denotes o X t out

/-- eval-buffer: with the inputs of eval-denote, an `ArrayBuffer` that fits
gives exactly the unbuffered result. -/
def evalBuffer : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    XFinite X → ConstsFinite t → OpsFinite o → BufferFits X t b →
    evalTreeArray ext impl D t X o (plainCtx early fused b) =
      evalTreeArray ext impl D t X o (plainCtx early fused .none)

/-- eval-constant: a tree without feature leaves, with finite constants and
finite-preserving operators, fills every sample (also zero samples) with its
value and completes. -/
def evalConstant : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidSound T → t.WF D o.nops X.nrows → isConstant t = true →
    ConstsFinite t → OpsFinite o →
    ∃ v, t.denote o (fun _ => none) = some v ∧
      evalTreeArray ext impl D t X o (plainCtx early fused .none) =
        .ok (JVec.fill X.ncols v, true)

/-- eval-vector: a vector input is one sample whose features are its entries. -/
def evalVector : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (v : JVec T) (t : Tree T),
    ArrayValidSound T → t.WF D o.nops v.size → (∀ x ∈ v.toList, valid x = true) →
    ConstsFinite t → OpsFinite o →
    ∃ w, t.denote o (vecAssign v) = some w ∧
      (evalTreeArrayVec ext impl D t v o (plainCtx early fused .none)).map (·.1.toList) =
        .ok [w] ∧
      (evalTreeArrayVec ext impl D t v o (plainCtx early fused .none)).map Prod.snd = .ok true

/-- eval-mixed: the mixed-type overload returns the denotation of the promoted
tree on the promoted matrix, for finite promoted inputs. -/
def evalMixed : Prop :=
  ∀ (T1 T2 T : Type) [JlScalar T] (c1 : T1 → T) (c2 : T2 → T) (ext : Ext) (impl : ExtImpl T)
    (D : Nat) (early fused : Bool) (o : OpEnum T) (X : JMat T2) (t : Tree T1),
    ArrayValidSound T → 1 ≤ X.ncols → (mapTree c1 t).WF D o.nops X.nrows →
    XFinite (mapMat c2 X) → ConstsFinite (mapTree c1 t) → OpsFinite o →
    ∃ out, evalTreeArrayMixed c1 c2 ext impl D t X o (plainCtx early fused .none) =
        .ok (out, true) ∧ Denotes o (mapMat c2 X) (mapTree c1 t) out

/-- eval-diff-denote: for finite inputs and constants, finite-preserving
operators and `one(T) * v == v`, `differentiable_eval_tree_array` returns the
denotation and completes. -/
def evalDiffDenote : Prop :=
  ∀ (T : Type) [JlScalar T] (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T),
    (∀ v : T, JlScalar.mul JlScalar.one v = v) → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    XFinite X → ConstsFinite t → OpsFinite o →
    ∃ out, differentiableEvalTreeArray o X t = .ok (out, true) ∧ Denotes o X t out

/-- eval-generic-vector: with operators that always have a method and never
throw, the generic evaluator on a vector input returns the value the
operators compute, with flag true, whatever `throw_errors`. -/
def evalGenericVector : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (throw : Bool) (x : JVec V) (t : Tree V),
    t.WF 255 (fun d => (gopsOf o d).length) x.size → GOpsTotal o →
    ∃ v, GOk o (fun f => if 1 ≤ f then x[f - 1]? else none) t v ∧
      genEvalVec o throw t x = .ok (some v, true)

/-- eval-generic-matrix: with total operators, the generic evaluator with
`throw_errors=true` on a matrix returns the per-sample values (features
sliced along the first axis), including zero samples. -/
def evalGenericMatrix : Prop :=
  ∀ (V : Type) (o : GOpEnum V) (X : JMat V) (t : Tree V),
    t.WF 255 (fun d => (gopsOf o d).length) X.nrows → GOpsTotal o →
    ∃ out, genEvalMat o true t X = .ok (some out, true) ∧ out.size = X.ncols ∧
      ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, GOk o (genSample X j) t v ∧ out[j - 1]? = some v

/-- eval-total (companion of eval-feature-oob): with every feature index
within the input rows, evaluation never raises, for any values. -/
def evalTotal : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops 65535 → t.WF D o.nops X.nrows →
    ∃ r, evalTreeArray ext impl D t X o (plainCtx early fused .none) = .ok r

/-- eval-fused-flag-finite (companion of eval-fused-flag-agree): with finite
inputs the completion flag does not depend on `use_fused`. -/
def evalFusedFlagFinite : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → 1 ≤ X.ncols → t.WF D o.nops X.nrows → XFinite X →
    (evalTreeArray ext impl D t X o (plainCtx true true .none)).map Prod.snd =
      (evalTreeArray ext impl D t X o (plainCtx true false .none)).map Prod.snd

/-- eval-noearly-fused-keep (companion of eval-noearly-fused-agree): with
`early_exit=false`, if unary operators return invalid arguments unchanged, the
output does not depend on `use_fused`. -/
def evalNoEarlyFusedKeep : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → noConstBranch t = true → UnaryKeepsInvalid o →
    (evalTreeArray ext impl D t X o (plainCtx false true .none)).map (·.1.toList) =
      (evalTreeArray ext impl D t X o (plainCtx false false .none)).map (·.1.toList)

/-- eval-noearly-noconst (companion of eval-noearly-denote): with
`early_exit=false` and no constant subexpression, evaluation completes with the
elementwise denotation, valid or not. -/
def evalNoEarlyNoConst : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → noConstBranch t = true →
    ∃ out, evalTreeArray ext impl D t X o (plainCtx false false .none) = .ok (out, true) ∧
      Denotes o X t out

/-- eval-zero-samples-clean (companion of eval-zero-samples-leaf and
eval-zero-samples-pair): with zero samples, finite constants and no constant
subexpression, the flag does not depend on `use_fused`. -/
def evalZeroSamplesClean : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T),
    ArrayValidExact T → X.ncols = 0 → t.WF D o.nops X.nrows → noConstBranch t = true →
    ConstsFinite t →
    (evalTreeArray ext impl D t X o (plainCtx true true .none)).map Prod.snd =
      (evalTreeArray ext impl D t X o (plainCtx true false .none)).map Prod.snd

/-- eval-wide-buffer-exact (companion of eval-wide-buffer): a matrix buffer
with exactly one column per sample and enough rows gives the unbuffered
result. -/
def evalWideBufferExact : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (A : JMat T) (i : Nat),
    ArrayValidSound T → 1 ≤ X.ncols → t.WF D o.nops X.nrows →
    XFinite X → ConstsFinite t → OpsFinite o →
    X.ncols ≤ A.ncols → i + t.size ≤ A.nrows → A.ncols = X.ncols →
    (evalTreeArray ext impl D t X o (plainCtx early fused (.mat A i))).map (·.1.toList) =
      (evalTreeArray ext impl D t X o (plainCtx early fused .none)).map (·.1.toList)

/-- eval-small-buffer-fits (companion of eval-small-buffer): a matrix buffer
with one column per sample and at least `count_nodes` free rows never raises
or has undefined behaviour, for any values. -/
def evalSmallBufferFits : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (early fused : Bool)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (A : JMat T) (i : Nat),
    1 ≤ X.ncols → t.WF D o.nops X.nrows → A.ncols = X.ncols → i + t.size ≤ A.nrows →
    ∃ r, evalTreeArray ext impl D t X o (plainCtx early fused (.mat A i)) = .ok r

/-- eval-turbo-dispatch (companion of eval-turbo-nonnumeric): with
LoopVectorization loaded and `T` in `(Float32, Float64)`, `turbo=true`
forwards to the extension evaluator and applies the final validity check. -/
def evalTurboDispatch : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat)
    (o : OpEnum T) (X : JMat T) (t : Tree T) (early fused : Bool) (b : Buf T),
    JlScalar.isFloat (T := T) = true → isNum T = true → ext.loopVectorization = true →
    evalTreeArray ext impl D t X o ⟨true, false, early, b, fused⟩ =
      (impl.turboEval t X).map (fun r => (r.x, r.ok && (!early || isValidArray r.x)))

/-- eval-diff-flag-finite (companion of eval-diff-flag): with finite input
values and constants, a true flag from `differentiable_eval_tree_array` means
every output value is valid. -/
def evalDiffFlagFinite : Prop :=
  ∀ (T : Type) [JlScalar T] (o : OpEnum T) (X : JMat T) (t : Tree T) (out : List T),
    t.WF 2 o.nops X.nrows → (∀ v : T, JlScalar.mul JlScalar.one v = v) →
    XFinite X ∧ ConstsFinite t →
    obs (differentiableEvalTreeArray o X t) = .ok (out, true) → ∀ x ∈ out, valid x = true

end DynExpr.Eval
