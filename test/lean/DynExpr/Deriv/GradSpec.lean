import DynExpr.Deriv.GradBounds

/-! Specification of the gradient evaluator for all trees, operator enums and
input matrices, and the proof that the mirror of `eval_grad_tree_array`
(src/EvaluateDerivative.jl:197-409) meets it. -/

namespace DynExpr.Deriv

/-! ## Specification -/

mutual
/-- Forward-mode derivative with an arbitrary seed for every leaf: feature `i`
has tangent `fseed i`, and the constant numbered `n` in preorder (starting at
`start`) has tangent `cseed n`. The chain rule uses the operator's supplied
derivative tuple, as in `Tree.denoteDeriv`. -/
def denoteSeed (o : DEnum) (x : Nat → Option JF) (fseed cseed : Nat → JF) (start : Nat) :
    Tree JF → Option (JF × JF)
  | .const v => some (v, cseed start)
  | .feature i => (x i).map fun v => (v, fseed i)
  | .branch idx cs => do
      let children ← denoteSeedList o x fseed cseed start cs
      let op ← o.lookup cs.length idx
      let values := children.map Prod.fst
      pure (op.primal values, addTerms (children.zipIdx.map fun (child, i) =>
        op.deriv i values * child.2))

/-- Children in order; each child's constants are numbered after those of the
earlier siblings. -/
def denoteSeedList (o : DEnum) (x : Nat → Option JF) (fseed cseed : Nat → JF) (start : Nat) :
    List (Tree JF) → Option (List (JF × JF))
  | [] => some []
  | c :: cs => do
      let r ← denoteSeed o x fseed cseed start c
      let rs ← denoteSeedList o x fseed cseed (start + (scalarConstants c).length) cs
      pure (r :: rs)
end

/-- Partial derivative with respect to the `c`-th constant (one-based,
preorder, i.e. the `c`-th entry of `get_scalar_constants`). -/
def constPartial (o : DEnum) (x : Nat → Option JF) (c : Nat) (t : Tree JF) :
    Option (JF × JF) :=
  denoteSeed o x (fun _ => zero) (fun n => if n = c then one else zero) 1 t

/-- Value of feature `k` at zero-based sample `j`. -/
def sampleX (X : JMat JF) (j : Nat) (k : Nat) : Option JF :=
  match X.row k with
  | .ok v => v.toList[j]?
  | .error _ => none

/-- Gradient row of feature `i`: absent in constant mode. -/
def featRow (m : Mode) (i : Nat) : Option Nat :=
  match m with
  | .constants => none
  | _ => some i

/-- Gradient row of constant `c`: absent in feature mode, after all features in
`:both` mode. -/
def constRow (m : Mode) (nf c : Nat) : Option Nat :=
  match m with
  | .features => none
  | .constants => some c
  | .both => some (nf + c)

/-- Leaf seeds selecting gradient row `q`. -/
def rowSeedF (m : Mode) (q i : Nat) : JF := if featRow m i = some q then one else zero
def rowSeedC (m : Mode) (nf q c : Nat) : JF := if constRow m nf c = some q then one else zero

/-- Zero-based gradient entry for sample `j` and row `k + 1`. -/
def entry (r : GradResult) (j k : Nat) : JF := (r.gradient.columns[j]!).getD k zero

/-- Primal of length `ns`; gradient of shape `ng`-by-`ns` stored as `ns` columns. -/
def GradShape (ns ng : Nat) (r : GradResult) : Prop :=
  r.primal.length = ns ∧ r.gradient.nrows = ng ∧ r.gradient.ncols = ns ∧
    r.gradient.columns.length = ns ∧ ∀ col ∈ r.gradient.columns, col.length = ng

/-- Every primal value is the tree's denotation and every gradient entry is the
seeded derivative selecting that row. -/
def RowsMatch (o : DEnum) (X : JMat JF) (m : Mode) (ng start : Nat) (t : Tree JF)
    (r : GradResult) : Prop :=
  ∀ j < X.ncols, Tree.denote o.primal (sampleX X j) t = some r.primal[j]! ∧
    ∀ k < ng, denoteSeed o (sampleX X j) (rowSeedF m (k + 1)) (rowSeedC m X.nrows (k + 1))
      start t = some (r.primal[j]!, entry r j k)

/-- At one node, every sample's value and every requested partial is finite. -/
def SpecValid (o : DEnum) (X : JMat JF) (m : Mode) (ng start : Nat) (t : Tree JF) : Prop :=
  ∀ j < X.ncols, (∃ v, Tree.denote o.primal (sampleX X j) t = some v ∧ v.valid = true) ∧
    ∀ k < ng, ∃ v d, denoteSeed o (sampleX X j) (rowSeedF m (k + 1))
      (rowSeedC m X.nrows (k + 1)) start t = some (v, d) ∧ d.valid = true

mutual
/-- Reasonable-input condition: all intermediate values and partials are finite. -/
def AllValid (o : DEnum) (X : JMat JF) (m : Mode) (ng start : Nat) : Tree JF → Prop
  | .const v => SpecValid o X m ng start (.const v)
  | .feature i => SpecValid o X m ng start (.feature i)
  | .branch idx cs => SpecValid o X m ng start (.branch idx cs) ∧ AllValidList o X m ng start cs

def AllValidList (o : DEnum) (X : JMat JF) (m : Mode) (ng start : Nat) :
    List (Tree JF) → Prop
  | [] => True
  | c :: cs => AllValid o X m ng start c ∧
      AllValidList o X m ng (start + (scalarConstants c).length) cs
end

/-- Reasonable finite inputs: every matrix entry is finite. -/
def FiniteMatrix (X : JMat JF) : Prop := ∀ v ∈ X.data, v.valid = true
/-- Every numeric constant of the tree is finite. -/
def FiniteConstants (t : Tree JF) : Prop := ∀ v ∈ scalarConstants t, v.valid = true
/-- Every operator and every supplied partial maps finite arguments to finite
values (for example +, -, *, but not /). -/
def FiniteOps (o : DEnum) : Prop :=
  ∀ d i op, o.lookup d i = some op → ∀ xs : List JF, (∀ x ∈ xs, x.valid = true) →
    (op.primal xs).valid = true ∧ ∀ n, (op.deriv n xs).valid = true

mutual
/-- Constant leaves with the index the gradient traversal assigns them
(`gradTree` passes `start` to a constant leaf and advances siblings by their
constant counts), in traversal order. -/
def constLeaves (start : Nat) : Tree JF → List (JF × Nat)
  | .const v => [(v, start)]
  | .feature _ => []
  | .branch _ cs => constLeavesList start cs

def constLeavesList (start : Nat) : List (Tree JF) → List (JF × Nat)
  | [] => []
  | c :: cs => constLeaves start c ++ constLeavesList (start + (scalarConstants c).length) cs
end

/-- The gradient traversal numbers constant leaves consecutively from `start`
in exactly the order of `get_scalar_constants`, src/NodeUtils.jl:99-116,186-203. -/
def constantOrdering : Prop :=
  ∀ (t : Tree JF) (start : Nat), constLeaves start t = (scalarConstants t).zipIdx start

/-- For every well-formed tree, operator enum with derivative tuples, input
matrix, storage kind and gradient mode, `eval_grad_tree_array` returns a primal of
length nsamples and an ngradients-by-nsamples gradient, where ngradients is
nfeatures, nconstants or nfeatures+nconstants. When it reports completion,
each primal entry is the tree's value at that sample, the row of feature q
(features and :both modes) is `Tree.denoteDeriv` in direction q, and the row of
constant c is the partial for the c-th `get_scalar_constants` entry, placed after
all features in :both mode. For finite inputs, finite constants and operators
that preserve finiteness it always reports completion. -/
def gradientModes : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat),
    let nc := (scalarConstants t).length
    let ng := nGradients m X.nrows nc
    t.WF D o.nops X.nrows → X.nrows + nc ≤ 65535 →
    ∃ r, eval_grad_tree_array s m o X t = .ok r ∧ GradShape X.ncols ng r ∧
      (FiniteMatrix X → FiniteConstants t → FiniteOps o → r.complete = true) ∧
      (r.complete = true → ∀ j < X.ncols,
        Tree.denote o.primal (sampleX X j) t = some r.primal[j]! ∧
        (m ≠ .constants → ∀ q, 1 ≤ q → q ≤ X.nrows →
          t.denoteDeriv o (sampleX X j) q = some (r.primal[j]!, entry r j (q - 1))) ∧
        (∀ c row, 1 ≤ c → c ≤ nc → constRow m X.nrows c = some row →
          constPartial o (sampleX X j) c t = some (r.primal[j]!, entry r j (row - 1))))

/-- For every well-formed tree, operator enum, input matrix with at least one
sample, and cotangent dY with one entry per sample, the rrule pullback succeeds
and returns the tree itself (as the `NodeTangent`'s tree), one constant
sensitivity per `get_scalar_constants` entry, an nfeatures-by-nsamples input
gradient, and NoTangent for the function and operators. For finite inputs,
finite constants and operators that preserve finiteness, `extract_gradient`
gives `sum_j dY[j] * dconst_c(sample j)` for each constant c and the input
gradient is `dX[q, j] = d_q(sample j) * dY[j]` (Jacobian-transpose times dY,
blockwise per sample). src/ChainRules.jl:18-24,57-80. -/
def pullbackEndToEnd : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat) (dY : List JF) (dComplete : Bool),
    let nc := (scalarConstants t).length
    let dC := fun j c => ((constPartial o (sampleX X j) c t).map Prod.snd).getD zero
    let dF := fun j q => ((t.denoteDeriv o (sampleX X j) q).map Prod.snd).getD zero
    t.WF D o.nops X.nrows → X.nrows + nc ≤ 65535 → dY.length = X.ncols → 0 < X.ncols →
    ∃ res, (EvalPullback.mk t X o).call dY dComplete = .ok res ∧
      res.tree.tree = t ∧ res.functionNoTangent = true ∧ res.operatorsNoTangent = true ∧
      (extract_gradient res.tree t).length = nc ∧
      res.features.nrows = X.nrows ∧ res.features.ncols = X.ncols ∧
      res.features.columns.length = X.ncols ∧
      (FiniteMatrix X → FiniteConstants t → FiniteOps o →
        extract_gradient res.tree t = (List.range nc).map (fun k =>
          addTerms (dY.zipIdx.map fun (dy, j) => dC j (k + 1) * dy)) ∧
        ∀ j < X.ncols, ∀ q, 1 ≤ q → q ≤ X.nrows →
          (res.features.columns[j]!).getD (q - 1) zero = dF j q * dY[j]!)

end DynExpr.Deriv
