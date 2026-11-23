import DynExpr.Deriv.Rrule

namespace DynExpr.Deriv

private def provenEntry (id file : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) : Registry.Entry :=
  ⟨id, file, fns, statement, pre, .proven, prop, some thm, ""⟩

private def fixedEntry (id file : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) (notes : String) : Registry.Entry :=
  ⟨id, file, fns, statement, pre, .proven, prop, some thm, notes⟩

def entries : List Registry.Entry := [
  provenEntry "deriv-chain-rule" "src/EvaluateDerivative.jl" ["eval_diff_tree_array", "diff_degn_eval"]
    "Directional evaluation equals Tree.denoteDeriv for every tree and supplied derivative tuple."
    "None: the Option-valued equality holds for every tree, feature binding and operator enum, including undefined ones."
    ``directionalChainRule ``directionalChainRule_proof,
  provenEntry "deriv-feature-leaf" "src/EvaluateDerivative.jl" ["eval_diff_tree_array", "diff_deg0_eval"]
    "Feature k has derivative one in direction k, zero in every other direction."
    "Feature binding exists; indices are one-based on reasonable Julia inputs."
    ``featureDerivative ``featureDerivative_proof,
  provenEntry "deriv-constant-leaf" "src/EvaluateDerivative.jl" ["eval_diff_tree_array", "diff_deg0_eval"]
    "Constant leaves have zero feature derivative." "Numeric constants."
    ``constantDerivative ``constantDerivative_proof,
  provenEntry "deriv-generated-dispatch" "src/EvaluateDerivative.jl"
    ["dispatch_diff_degn_eval", "dispatch_grad_degn_eval"]
    "For every operator enum, degree and in-range operator index, the generated dispatch (the @nif chain up to 15 operators, direct tuple indexing above) selects the same operator as the one-based lookup the derivative mirrors use."
    "Degree at least 1; operator index in 1..nops (well-formed trees)."
    ``generatedDispatch ``generatedDispatch_proof,
  provenEntry "deriv-repeated-features" "src/EvaluateDerivative.jl" ["eval_diff_tree_array", "diff_degn_eval"]
    "For every operator, subtree c and arity n, the directional derivative of op(c,...,c) is the sum over argument positions of the supplied partial times c's derivative (x+x gives 2, x*x gives 2x)."
    "At least one copy; the operator index exists for arity n. The branch is defined exactly when the repeated subtree is."
    ``repeatedFeatures ``repeatedFeatures_proof,
  { id := "deriv-gradient-modes", juliaFile := "src/EvaluateDerivative.jl",
    juliaFns := ["eval_grad_tree_array", "grad_deg0_eval", "grad_degn_eval", "dispatch_grad_degn_eval", "index_constant_nodes"],
    statement := "For every tree, operator enum, matrix, storage and mode, eval_grad_tree_array returns shape (nfeatures | nconstants | nfeatures+nconstants, nsamples); on completion every primal entry is the tree value and every gradient entry is the Tree.denoteDeriv feature partial or the get_scalar_constants-ordered constant partial, with features first in :both; finite intermediates imply completion.",
    preconditions := "Well-formed tree (valid feature and operator indices); nfeatures + nconstants <= 65535. Completion is proven for finite matrix entries and constants and operators whose values and partials are finite on finite arguments.",
    status := .proven, prop := ``gradientModes, thm := some ``gradientModes_proof,
    notes := "Earlier worked-example statement (2*x+5) used 8 attempts; replaced by this general statement, proven on the first attempt by structural induction (gradTree_good in Deriv/GradProofs.lean)." },
  { id := "deriv-constant-order", juliaFile := "src/EvaluateDerivative.jl",
    juliaFns := ["eval_grad_tree_array", "index_constant_nodes"],
    statement := "For every tree and starting index, the gradient traversal numbers constant leaves start, start+1, ... in get_scalar_constants order.",
    preconditions := "None beyond a finite tree.",
    status := .proven, prop := ``constantOrdering, thm := some ``constantOrdering_proof },
  provenEntry "deriv-both-constant-index" "src/EvaluateDerivative.jl" ["grad_deg0_eval", "eval_grad_tree_array"]
    "The both-mode constant index equals the number of features plus its constant index."
    "The feature count plus total constant count is at most 65535; constant index is in 1..nconstants."
    ``bothConstantIndex ``bothConstantIndex_proof,
  fixedEntry "deriv-generic-zero-shape" "src/EvaluateDerivative.jl" ["grad_deg0_eval", "eval_grad_tree_array"]
    "For every well-formed tree and non-Array matrix (view/transpose) with zero requested gradients, eval_grad_tree_array returns a 0-by-nsamples gradient."
    "Well-formed tree; nfeatures + nconstants <= 65535; zero requested gradients."
    ``genericZeroShape ``genericZeroShape_proof
    "Fixed by PR #225: zero requested gradients take the fill_similar branch, which gives a 0-by-nsamples matrix, instead of the hcat() adjoint (1-by-0).",
  fixedEntry "deriv-view-constant-grad-oob" "src/EvaluateDerivative.jl"
    ["eval_grad_tree_array", "grad_deg0_eval", "grad_degn_eval"]
    "Constant-gradient mode (variable=false) on a non-Array matrix (view/transpose) never performs an out-of-range @inbounds access."
    "Well-formed tree (degree at most 2, valid operator and feature indices)."
    ``viewConstantGradSafe ``viewConstantGradSafe_proof
    "Fixed by PR #225: with zero constants the leaf gradient is 0-by-nsamples, so the fused kernel writes no rows; every remaining error is the checked row view's BoundsError.",
  provenEntry "deriv-grad-no-oob" "src/EvaluateDerivative.jl" ["eval_grad_tree_array", "grad_degn_eval", "grad_deg0_eval"]
    "In every mode and storage, gradient evaluation never performs an out-of-range @inbounds access."
    "Well-formed tree; nfeatures + nconstants <= 65535."
    ``gradNoOutOfBounds ``gradNoOutOfBounds_proof,
  fixedEntry "deriv-directional-validity" "src/EvaluateDerivative.jl" ["eval_diff_tree_array"]
    "For every well-formed tree, eval_diff_tree_array reports completion exactly when every returned value and derivative is finite (its documented contract). Companion: deriv-directional-validity-finite."
    "Well-formed tree; nonfinite constants and operator results allowed (they are the behaviour under test)."
    ``directionalValidity ``directionalValidity_proof
    "Fixed by PR #226: the returned flag is result.ok && is_valid_array(result.x) && is_valid_array(result.dx).",
  provenEntry "deriv-directional-validity-finite" "src/EvaluateDerivative.jl" ["eval_diff_tree_array"]
    "Companion of deriv-directional-validity: for every well-formed tree with finite inputs and constants and finiteness-preserving operators, directional evaluation succeeds with all values finite and complete=true, which agrees with the finiteness check."
    "Well-formed tree; finite matrix entries and constants; operators and their supplied partials map finite arguments to finite values (excludes exactly the NaN/Inf trigger)."
    ``directionalValidityFinite ``directionalValidityFinite_proof,
  provenEntry "deriv-gradient-validity" "src/EvaluateDerivative.jl" ["eval_grad_tree_array"]
    "For every well-formed tree, operator enum, matrix, storage and mode, eval_grad_tree_array succeeds and reports completion exactly when every returned primal and gradient value is finite (including results returned by the early exit)."
    "Well-formed tree; nfeatures + nconstants <= 65535."
    ``gradientValidity ``gradientValidity_proof,
  { id := "deriv-early-exit", juliaFile := "src/EvaluateDerivative.jl",
    juliaFns := ["dispatch_grad_degn_eval", "eval_grad_tree_array"],
    statement := "For every branch whose first child's gradient call returns an incomplete result, the branch returns that result unchanged, whatever the later children are (even ones that would throw).",
    preconditions := "The first child's call returns an incomplete result (its success on well-formed inputs is proven by deriv-gradient-modes).",
    status := .proven, prop := ``earlyExit, thm := some ``earlyExit_proof,
    notes := "The success hypothesis is on the first child; deriv-gradient-modes proves success for well-formed inputs." },
  { id := "deriv-pullback-end-to-end", juliaFile := "src/ChainRules.jl",
    juliaFns := ["EvalPullback", "NodeTangent", "extract_gradient", "rrule"],
    statement := "For every well-formed tree, operator enum, matrix with at least one sample and cotangent dY, the pullback succeeds, returns a NodeTangent of the tree with one sensitivity per constant, an nfeatures-by-nsamples dX and NoTangent for function and operators; for finite inputs extract_gradient gives sum_j dY[j]*dconst(sample j) in get_scalar_constants order and dX[q,j] = dfeature_q(sample j)*dY[j]. Companion of deriv-empty-pullback.",
    preconditions := "Well-formed tree; nfeatures + nconstants <= 65535; at least one sample and one cotangent entry per sample. Values: finite matrix entries and constants; operators and supplied partials map finite arguments to finite values.",
    status := .proven, prop := ``pullbackEndToEnd, thm := some ``pullbackEndToEnd_proof,
    notes := "Earlier worked-example statement (2*x+5) used 6 attempts; replaced by this general statement, proven from gradTree_good." },
  fixedEntry "deriv-empty-pullback" "src/ChainRules.jl" ["EvalPullback", "NodeTangent"]
    "For every well-formed tree and matrix with zero samples, the pullback with an empty cotangent returns zero constant sensitivities. Companion: deriv-pullback-end-to-end (at least one sample)."
    "Well-formed tree; nfeatures + nconstants <= 65535; zero samples (the primal rule accepts them)."
    ``emptyPullback ``emptyPullback_proof
    "Fixed by PR #227: an empty cotangent gives fill_similar zeros for the constants instead of a sum over an empty collection.",
  provenEntry "deriv-failed-primal-invalidates" "src/ChainRules.jl" ["rrule", "eval_tree_array"]
    "For every well-formed tree, operator enum, matrix, evaluation policy and fitting buffer, the rrule succeeds and returns eval_tree_array's array and flag when complete, and the same array filled with NaN with complete=false otherwise."
    "Well-formed tree; buffer none, a vector ArrayBuffer, or a matrix ArrayBuffer with enough rows (Eval's BufferFits)."
    ``failedRuleInvalidates ``failedRuleInvalidates_proof,
  provenEntry "deriv-alias-rule-arena-primal" "src/ChainRules.jl" ["rrule", "eval_tree_array"]
    "For every well-formed input and fitting buffer, the rrule's primal is the evaluator's output array object itself: freshly allocated without a buffer (never X), and an ArrayBuffer slot handed out during this call with a buffer (borrowed until reset_index!)."
    "Well-formed tree; fitting buffer as in deriv-failed-primal-invalidates."
    ``ruleBorrowedPrimal ``ruleBorrowedPrimal_proof,
  provenEntry "deriv-nondiff-inventory" "src/NonDifferentiableDeclarations.jl"
    ["@non_differentiable", "get_operators", "get_variable_names", "_validate_input", "set_invalid!", "tree_mapreduce"]
    "The six @non_differentiable registrations have argument counts [4,5,2,2,3,1]."
    "None: fixed registration table in package code (static fact)."
    ``registrationInventory ``registrationInventory_proof,
  provenEntry "deriv-alias-grad-outputs" "src/EvaluateDerivative.jl" ["eval_grad_tree_array", "grad_deg0_eval", "grad_degn_eval"]
    "For every well-formed input, eval_grad_tree_array returns its value and gradient in two distinct arrays allocated during the call, equal to the pure mirror's results; neither aliases X, a view of X, a constant or any earlier array, and every pre-existing object, X included, is unchanged although fused kernels write child arrays in place."
    "Well-formed tree; nfeatures + nconstants <= 65535; X is an allocated input object."
    ``gradOutputsFresh ``gradOutputsFresh_proof,
  provenEntry "deriv-alias-fused-reuse" "src/EvaluateDerivative.jl" ["grad_degn_eval", "dispatch_grad_degn_eval"]
    "For every well-formed root branch, the children's value and gradient arrays that the in-place fused kernel reads and overwrites are pairwise distinct objects allocated during the call, so in-place writes never clobber data still to be read, X, or any pre-existing array."
    "Well-formed tree; nfeatures + nconstants <= 65535; X is an allocated input object."
    ``fusedChildrenDisjoint ``fusedChildrenDisjoint_proof,
  provenEntry "deriv-alias-diff-outputs" "src/EvaluateDerivative.jl" ["eval_diff_tree_array", "diff_deg0_eval", "diff_degn_eval"]
    "For every well-formed input and direction, eval_diff_tree_array returns its value and derivative in two distinct arrays allocated during the call, equal sample by sample to the chain-rule mirror; neither aliases X or any earlier array, and every pre-existing object, X included, is unchanged."
    "Well-formed tree; X is an allocated input object."
    ``diffOutputsFresh ``diffOutputsFresh_proof,
  provenEntry "deriv-alias-pullback-outputs" "src/ChainRules.jl" ["EvalPullback", "NodeTangent"]
    "For every well-formed input with at least one sample, the pullback returns dtree.gradient and dX as two distinct arrays allocated during the call, equal to the pure pullback's results; X, dY and every other pre-existing object are unchanged (set_invalid! only touches the pullback's own gradient array)."
    "Well-formed tree; nfeatures + nconstants <= 65535; at least one sample; dY has one entry per sample; X and dY are allocated objects."
    ``pullbackOutputsFresh ``pullbackOutputsFresh_proof
]

end DynExpr.Deriv
