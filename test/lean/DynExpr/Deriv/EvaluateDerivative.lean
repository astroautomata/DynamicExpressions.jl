import DynExpr.Model.Denote
import DynExpr.Runtime.Value
import DynExpr.Registry.Types
import DynExpr.Eval.Scalars

namespace DynExpr.Deriv

abbrev zero : JF := .fin 0
abbrev one : JF := .fin 1
instance : Inhabited JF := ⟨zero⟩
/-- An operator and the derivative tuple supplied by the Zygote extension,
src/EvaluateDerivative.jl:111-117,352-363. The tuple has one function per input.
No analytic claim is made about these functions. -/
structure DOp where
  primal : List JF → JF
  deriv : Nat → List JF → JF

/-- Degree-indexed operator tuples, src/EvaluateDerivative.jl:132,148-169. -/
structure DEnum where
  ops : List (List DOp)

def DEnum.lookup (o : DEnum) (degree index : Nat) : Option DOp :=
  if degree = 0 ∨ index = 0 then none else (o.ops[degree - 1]?.getD [])[index - 1]?

def DEnum.primal (o : DEnum) : OpEnum JF := ⟨o.ops.map (List.map DOp.primal)⟩

/-- Generated n-argument +, src/EvaluateDerivative.jl:117,360-364.
Unary + is identity; the empty case is unreachable for representable branches. -/
def addTerms : List JF → JF
  | [] => zero
  | a :: as => as.foldl JF.add a

/-- Fused scalar chain rule using the operator's derivative tuple,
src/EvaluateDerivative.jl:112-120. -/
def diffKernel (op : DOp) (children : List (JF × JF)) : JF × JF :=
  let xs := children.map Prod.fst
  (op.primal xs, addTerms ((children.zipIdx).map fun (child, i) =>
    op.deriv i xs * child.2))

/-- Scalar projection of generated degree dispatch. Both lookup paths pick the
same op; leaves and fused kernels return true without a validity check,
src/EvaluateDerivative.jl:72-172. -/
def diffScalar (o : DEnum) (x : Nat → Option JF) (direction : Nat) :
    Tree JF → Option (JF × JF)
  | .const v => some (v, zero)
  | .feature k => do
      let v ← x k
      pure (v, if k = direction then one else zero)
  | .branch idx cs => do
      let children ← cs.mapM (diffScalar o x direction)
      let op ← o.lookup cs.length idx
      pure (diffKernel op children)

/-- The symbolic chain-rule specification, using supplied operator derivatives
rather than real analysis. -/
def _root_.DynExpr.Tree.denoteDeriv (o : DEnum) (x : Nat → Option JF)
    (direction : Nat) : Tree JF → Option (JF × JF)
  | .const v => some (v, zero)
  | .feature k => (x k).map fun v => (v, if k = direction then one else zero)
  | .branch idx cs => do
      let children ← cs.mapM (Tree.denoteDeriv o x direction)
      let op ← o.lookup cs.length idx
      let values := children.map Prod.fst
      let terms := children.zipIdx |>.map fun (child, i) => op.deriv i values * child.2
      pure (op.primal values, addTerms terms)

/-- The public directional evaluator. Every successful scalar traversal has
`result.ok = true`; the returned flag also requires `is_valid_array` of the
values and of the derivatives, src/EvaluateDerivative.jl:40-57,
src/ValueInterface.jl:17-22. -/
def eval_diff_tree_array (o : DEnum) (X : JMat JF) (direction : Nat) (t : Tree JF) :
    Option (List (JF × JF) × Bool) :=
  ((List.range X.ncols).mapM fun j => diffScalar o
    (fun k => (X.get? k (j + 1)).toOption) direction t).map fun ys =>
      (ys, Eval.isValidArray (ys.map Prod.fst).toArray &&
        Eval.isValidArray (ys.map Prod.snd).toArray)

/-- Dense or generic AbstractMatrix branch of grad_deg0_eval, src/EvaluateDerivative.jl:380. -/
inductive Storage where | dense | generic deriving DecidableEq, Repr
/-- Bool/Val gradient modes, src/EvaluateDerivative.jl:204-228. -/
inductive Mode where | features | constants | both deriving DecidableEq, Repr

/-- Column-major gradient storage. Each list is one sample column,
src/EvaluateDerivative.jl:353-365. Explicit dimensions preserve the empty cases. -/
structure GradMatrix where
  nrows : Nat
  ncols : Nat
  columns : List (List JF)
  deriving DecidableEq, Repr

structure GradResult where
  primal : List JF
  gradient : GradMatrix
  complete : Bool
  deriving DecidableEq, Repr
instance : Inhabited GradResult := ⟨⟨[], ⟨0, 0, []⟩, false⟩⟩
/-- Numeric constant traversal order, src/NodeUtils.jl:99-116,186-203. -/
def scalarConstants : Tree JF → List JF
  | .const v => [v]
  | .feature _ => []
  | .branch _ cs => cs.flatMap scalarConstants

def nGradients (mode : Mode) (nf nc : Nat) : Nat :=
  match mode with
  | .features => nf
  | .constants => nc
  | .both => nf + nc

/-- UInt16 addition in the both-mode constant index is performed before indexing,
src/EvaluateDerivative.jl:391-402. -/
def leafIndex (mode : Mode) (nf : Nat) (constant : Bool) (index : Nat) : Option Nat :=
  match mode, constant with
  | .features, true | .constants, false => none
  | .both, true => some ((index + (nf % 65536)) % 65536)
  | _, _ => some index

/-- `fill_similar(zero(T), cX, n_gradients, axes(cX, 2))` for an `Array` or
zero gradients, otherwise the adjoint of `hcat` of `n_gradients` zero
vectors. Both are `ng`-by-`ns` zero matrices; the matrix type is not modelled,
src/EvaluateDerivative.jl:380-384. -/
def zeroMatrix (_storage : Storage) (ng ns : Nat) : GradMatrix :=
  ⟨ng, ns, List.replicate ns (List.replicate ng zero)⟩

/-- The leaf gradient allocation and one-hot write through a checked row view,
src/EvaluateDerivative.jl:371-408. -/
def grad_deg0_eval (storage : Storage) (mode : Mode) (nf ng : Nat)
    (values : List JF) (constant : Bool) (index : Nat) : Jl GradResult := do
  let mat := zeroMatrix storage ng values.length
  match leafIndex mode nf constant index with
  | none => pure ⟨values, mat, true⟩
  | some row =>
      if 1 ≤ row ∧ row ≤ mat.nrows then
        let columns := mat.columns.map fun col => col.zipIdx |>.map fun (v, i) =>
          if i + 1 = row then one else v
        pure ⟨values, {mat with columns := columns}, true⟩
      else .error .boundsError

/-- Public and recursive finite checks, src/EvaluateDerivative.jl:242-246. -/
def checkResult (r : GradResult) : GradResult :=
  if !r.complete then r
  else {r with complete := r.primal.all JF.valid &&
    r.gradient.columns.all (fun col => col.all JF.valid)}

/-- All samples are computed together. A failed child exits before evaluating
later children or the parent, src/EvaluateDerivative.jl:302-315. -/
def firstIncomplete (rs : List GradResult) : Option GradResult :=
  rs.find? fun r => !r.complete

/-- Stop on the first exception or incomplete child, src/EvaluateDerivative.jl:305-313. -/
def collectChildren : List (Jl GradResult) → Jl (List GradResult)
  | [] => pure []
  | a :: as => do
      let r ← a
      if !r.complete then pure [r]
      else
        let rs ← collectChildren as
        match firstIncomplete rs with
        | some failed => pure [failed]
        | none => pure (r :: rs)

/-- Fused Jacobian kernel with child-one storage shape and generated derivative
sum, src/EvaluateDerivative.jl:344-368. Valid arrays have matching sample axes. -/
def gradKernel (op : DOp) (ns : Nat) (rs : List GradResult) : Jl GradResult := do
  let shape := rs[0]!.gradient
  let ng := shape.nrows
  if ng > 0 ∧ rs.any (fun r => r.gradient.ncols < ns || r.gradient.nrows < ng) then
    .error (.undefinedBehavior "fused gradient matrix index out of bounds")
  else
    let values := (List.range ns).map fun j =>
      op.primal (rs.map fun r => r.primal[j]!)
    let cols := (List.range ns).map fun j =>
      let xs := rs.map fun r => r.primal[j]!
      (List.range ng).map fun k => addTerms (rs.zipIdx |>.map fun (r, i) =>
        op.deriv i xs * ((r.gradient.columns[j]!).getD k zero))
    pure ⟨values, ⟨ng, shape.ncols, cols⟩, true⟩

mutual
/-- Forward gradient traversal and recursive validity checks. The constant
index tree is represented by the running preorder offset `start`: a constant
leaf receives `start`, and each later sibling starts after the constants of the
earlier ones, as built by index_constant_nodes, src/NodeUtils.jl:186-203,
src/EvaluateDerivative.jl:197-409. -/
def gradTree (storage : Storage) (mode : Mode) (o : DEnum) (X : JMat JF)
    (ng start : Nat) : Tree JF → Jl GradResult
  | .const v =>
      (grad_deg0_eval storage mode X.nrows ng (List.replicate X.ncols v)
        true (start % 65536)).map checkResult
  | .feature k => do
      let vals ← X.row k
      (grad_deg0_eval storage mode X.nrows ng vals.toList false k).map checkResult
  | .branch idx cs => do
      -- The recursive loop returns the first incomplete child unchanged.
      let rs ← collectChildren (gradTreeList storage mode o X ng start cs)
      match firstIncomplete rs with
      | some r => pure r
      | none =>
          match o.lookup cs.length idx with
          | none => .error (.undefinedBehavior "generated operator dispatch has no matching arm")
          | some op => (gradKernel op X.ncols rs).map checkResult

/-- The children's calls in order with their index-tree offsets,
src/EvaluateDerivative.jl:302-315. -/
def gradTreeList (storage : Storage) (mode : Mode) (o : DEnum) (X : JMat JF)
    (ng start : Nat) : List (Tree JF) → List (Jl GradResult)
  | [] => []
  | c :: cs => gradTree storage mode o X ng start c ::
      gradTreeList storage mode o X ng (start + (scalarConstants c).length) cs
end

/-- Public gradient mode selection and count, src/EvaluateDerivative.jl:197-232. -/
def eval_grad_tree_array (storage : Storage) (mode : Mode) (o : DEnum)
    (X : JMat JF) (t : Tree JF) : Jl GradResult :=
  gradTree storage mode o X (nGradients mode X.nrows (scalarConstants t).length) 1 t

/-- Number of operators of a degree, `get_nops(operators, Val(degree))`. -/
def DEnum.nops (o : DEnum) (degree : Nat) : Nat := (o.ops[degree - 1]?.getD []).length

/-- `Base.Cartesian.@nif(nops, i -> i == op_idx, i -> op_i)`: tests the indices
in order and takes the last arm unconditionally, src/EvaluateDerivative.jl:158-169,329-340. -/
def nifSelect (idx : Nat) : Nat → List DOp → Option DOp
  | _, [] => none
  | _, [op] => some op
  | i, op :: rest => if idx = i then some op else nifSelect idx (i + 1) rest

/-- Generated operator dispatch: above `OPERATOR_LIMIT_BEFORE_SLOWDOWN = 15`
operators the tuple is indexed directly, otherwise the `@nif` chain selects,
src/EvaluateDerivative.jl:148-169,321-340, src/Evaluate.jl:14. -/
def generatedOp (o : DEnum) (degree idx : Nat) : Option DOp :=
  if degree = 0 then none
  else
    let ops := o.ops[degree - 1]?.getD []
    if 15 < ops.length then (if idx = 0 then none else ops[idx - 1]?)
    else nifSelect idx 1 ops


end DynExpr.Deriv
