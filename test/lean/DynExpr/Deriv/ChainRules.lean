import DynExpr.Deriv.EvaluateDerivative

namespace DynExpr.Deriv

/-- Tangent fields, src/ChainRules.jl:18-21. -/
structure NodeTangent where
  tree : Tree JF
  gradient : List JF

/-- The second argument is ignored, src/ChainRules.jl:22-24. -/
def extract_gradient (a : NodeTangent) (_tree : Tree JF) : List JF := a.gradient

/-- set_invalid! applied to every gradient element, src/ChainRules.jl:63-65. -/
def invalidateMatrix (a : GradMatrix) : GradMatrix :=
  {a with columns := a.columns.map (List.map fun _ => JF.nan)}

structure PullbackResult where
  tree : NodeTangent
  features : GradMatrix
  functionNoTangent : Bool
  operatorsNoTangent : Bool

/-- An empty cotangent gives `fill_similar` zeros, one per constant row.
Otherwise, for each scalar constant, sum sample contributions: the coordinate
form of `sum(j -> dconstants_dY[:, j] * dY[j], eachindex(dY, axes(dconstants_dY, 2)))`,
where `eachindex` throws unless the sample axes agree, src/ChainRules.jl:69-75. -/
def constantPullback (nf : Nat) (a : GradMatrix) (dY : List JF) : Jl (List JF) :=
  if dY.isEmpty then pure (List.replicate (a.nrows - nf) zero)
  else if dY.length ≠ a.ncols then .error (.argumentError "sample axes do not match")
  else pure ((List.range (a.nrows - nf)).map fun k =>
    addTerms (dY.zipIdx |>.map fun (dy, j) =>
      ((a.columns[j]!).getD (nf + k) zero) * dy))

/-- `dX_dY .* reshape(dY, 1, length(dY))`: the feature view keeps its rows and
column `j` is scaled by `dY[j]`. Broadcasting also expands a singleton sample
axis on either side and otherwise throws DimensionMismatch,
src/ChainRules.jl:67-68,78. -/
def featurePullback (nf : Nat) (a : GradMatrix) (dY : List JF) : Jl GradMatrix :=
  if dY.length = a.ncols then
    pure ⟨nf, a.ncols, a.columns.zipIdx |>.map fun (col, j) =>
      (col.take nf).map fun v => v * dY[j]!⟩
  else if a.ncols = 1 then
    pure ⟨nf, dY.length, dY.map fun dy => ((a.columns[0]!).take nf).map fun v => v * dy⟩
  else if dY.length = 1 then
    pure ⟨nf, a.ncols, a.columns.map fun col => (col.take nf).map fun v => v * dY[0]!⟩
  else .error (.argumentError "arrays could not be broadcast to a common size")

/-- Explicit EvalPullback object, src/ChainRules.jl:50-54. -/
structure EvalPullback where
  tree : Tree JF
  X : JMat JF
  operators : DEnum

/-- The pullback recalculates both-mode gradients, invalidates failures, ignores
the cotangent of the Bool flag and returns no operator/function tangents,
src/ChainRules.jl:57-80. -/
def EvalPullback.call (e : EvalPullback) (dY : List JF) (_dComplete : Bool) :
    Jl PullbackResult := do
  let result ← eval_grad_tree_array .dense .both e.operators e.X e.tree
  let a := if result.complete then result.gradient else invalidateMatrix result.gradient
  let constants ← constantPullback e.X.nrows a dY
  let features ← featurePullback e.X.nrows a dY
  pure ⟨⟨e.tree, constants⟩, features, true, true⟩

/-- The six explicit macro registrations with their method-signature patterns,
src/NonDifferentiableDeclarations.jl:14-19. -/
inductive RegisteredMethod where
  | treeMapreduceLeaf | treeMapreduceBranch | getOperators
  | getVariableNames | validateInput | setInvalid
  deriving DecidableEq, Repr

def nonDifferentiableRegistrations : List (RegisteredMethod × Nat) :=
  [(.treeMapreduceLeaf, 4), (.treeMapreduceBranch, 5), (.getOperators, 2),
   (.getVariableNames, 2), (.validateInput, 3), (.setInvalid, 1)]

end DynExpr.Deriv
