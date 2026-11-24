import DynExpr.Registry.Types
import DynExpr.Eval.Refute
import DynExpr.Eval.Easy
import DynExpr.Eval.Top
import DynExpr.Eval.GenericProofs
import DynExpr.Eval.UnfusedProofs
import DynExpr.Eval.AliasProofs
import DynExpr.Eval.Final
import DynExpr.Eval.ZeroProofs
import DynExpr.Eval.SafeProofs
import DynExpr.Eval.FeatureMajor

/-! Slice root: imports this slice's files and lists its registry entries. -/

namespace DynExpr.Eval
open DynExpr.Registry

private def entry (id file : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) (status : Status := .proven) (notes : String := "") : Entry :=
  ⟨id, file, fns, statement, pre, status, prop, some thm, notes⟩

def entries : List Entry := [
  entry "eval-denote" "src/Evaluate.jl"
    ["eval_tree_array", "EvalContext", "_eval_tree_array", "dispatch_deg1_eval",
      "dispatch_deg2_eval", "dispatch_degn_eval", "deg1_l2_ll0_lr0_eval", "deg1_l1_ll0_eval",
      "deg2_l0_r0_eval", "deg2_l0_eval", "deg2_r0_eval", "deg2_branch0_eval", "degn_eval",
      "dispatch_constant_tree", "get_feature_array", "feature_at", "first_feature_index"]
    "For every early_exit/use_fused setting, with finite inputs, finite constants and operators that map finite arguments to finite values, eval_tree_array returns the denotation at every sample and flag true."
    "Well-formed tree (degree <= D, operator indices in range, features in 1..size(X,1)); at least one sample; Finite inputs X (XFinite), finite constants (ConstsFinite), operators mapping finite arguments to finite values (OpsFinite); is_valid_array accepts all-valid arrays (no overflow in its sum, true for JF)."
    ``evalDenote ``evalDenote_proof .proven
    "The precondition that is_valid_array accepts all-valid arrays is needed: it fails for Float64 near floatmax (bug refuted as nodeutils-array-overflow).",
  entry "eval-fused-valid" "src/Evaluate.jl" ["_kernels_validate", "degn_eval", "deg0_eval", "deg2_l0_r0_eval", "deg2_l0_eval", "deg2_r0_eval", "deg2_branch0_eval"]
    "The fused SIMD accumulator validity check (is_valid(acc) || all(is_valid, out)) agrees with elementwise validity for every float vector, including NaN, Inf, and Float16 sum overflow."
    "Arbitrary float vectors (JF and Float16 sum-overflow model)."
    ``fusedValidAgree ``fusedValidAgree_proof,
  entry "eval-feature-major-equiv" "src/Evaluate.jl" ["FeatureMajorMatrix", "feature_major_matrix", "first_feature_index", "feature_stride", "feature_at", "get_feature_array"]
    "FeatureMajorMatrix constructed by feature_major_matrix(X) preserves matrix dimensions, checked getindex (including BoundsError), unit-stride feature_at, and buffered/unbuffered get_feature_array."
    "Arbitrary dense matrix X and valid feature/sample coordinates (arbitrary coordinates for getindex)."
    ``featureMajorEquiv ``featureMajorEquiv_proof,
  entry "eval-feature-major-batch-safe" "src/Evaluate.jl" ["feature_major_batch", "FeatureMajorMatrix"]
    "feature_major_batch(X, indices) raises BoundsError (never undefined behaviour) when any index is out of range, and otherwise gathers exact transposed columns X[f, indices[k]]."
    "Arbitrary dense matrix X and arbitrary column index list."
    ``featureMajorBatchSafe ``featureMajorBatchSafe_proof,
  entry "eval-kernels-validate-sound" "src/Evaluate.jl" ["_kernels_validate", "eval_tree_array"]
    "When _kernels_validate is active and fused validity agrees with is_valid_array, skipping the duplicate @return_on_nonfinite_array and top-level is_valid_array checks produces the exact same flag and early-exit behaviour as unvalidated evaluation."
    "fusedValid agrees with isValidArray (proven for JF)."
    ``kernelsValidateSound ``kernelsValidateSound_proof,
  entry "eval-buffer" "src/Evaluate.jl" ["eval_tree_array", "EvalContext", "ArrayBuffer", "get_array", "get_filled_array", "get_feature_array"]
    "With an ArrayBuffer that fits (vector-backed, or matrix-backed with one column per sample and at least count_nodes free rows) the result equals the unbuffered result."
    "As eval-denote; vector-backed buffer, or matrix buffer with size(buffer,2) == samples and >= count_nodes free rows."
    ``evalBuffer ``evalBuffer_proof,
  entry "eval-constant" "src/Evaluate.jl" ["eval_tree_array", "dispatch_constant_tree", "is_constant"]
    "A tree without feature leaves fills every sample (also zero samples) with its value, flag true."
    "Well-formed tree; finite constants; operators mapping finite arguments to finite values; is_valid_array accepts all-valid arrays."
    ``evalConstant ``evalConstant_proof,
  entry "eval-unfused-flag" "src/Evaluate.jl" ["eval_tree_array", "EvalContext"]
    "With use_fused=false and early_exit=true the call returns, its flag is true exactly when every intermediate value at every sample is valid, and a true flag comes with the denotation."
    "Well-formed tree; at least one sample; is_valid_array holds exactly for all-valid arrays."
    ``evalUnfusedFlag ``evalUnfusedFlag_proof,
  entry "eval-fused-flag-agree" "src/Evaluate.jl" ["eval_tree_array", "deg2_l0_r0_eval", "EvalContext"]
    "With early_exit=true the fused kernels check only their outputs: whenever use_fused=false completes with flag true, use_fused=true completes with the same output and flag true, and when every input entry is finite the two flags agree."
    "Well-formed tree; at least one sample; is_valid_array holds exactly for all-valid arrays (true for JF)."
    ``evalFusedFlagAgree ``evalFusedFlagAgree_proof .proven
    "Documented behaviour (Q38; Miles ruled: document, do not fix; docs PR #276 states it on use_fused). `1.0 / x1` at x1 = Inf still returns ([0.0], true) fused but ([Inf], false) unfused: a non-finite input mapped to a finite output passes the fused check. Companion: eval-fused-flag-finite.",
  entry "eval-fused-flag-finite" "src/Evaluate.jl" ["eval_tree_array", "EvalContext"]
    "With finite inputs X, the completion flag (early_exit=true) does not depend on use_fused."
    "As eval-fused-flag-agree, plus finite X entries."
    ``evalFusedFlagFinite ``evalFusedFlagFinite_proof,
  entry "eval-noearly-fused-agree" "src/Evaluate.jl" ["eval_tree_array", "deg1_l1_ll0_eval", "deg1_l2_ll0_lr0_eval", "EvalContext"]
    "With early_exit=false the output does not depend on use_fused."
    "Well-formed tree; at least one sample; no constant subexpression (noConstBranch)."
    ``evalNoEarlyFusedAgree ``evalNoEarlyFusedAgree_proof .proven
    "Fixed by PR #268: fused unary kernels apply the outer operator when early_exit is off, so inv(inv(x1)) at x1 = 0 gives [0.0] fused and unfused. Companion: eval-noearly-fused-keep.",
  entry "eval-noearly-fused-keep" "src/Evaluate.jl" ["eval_tree_array", "deg1_l1_ll0_eval", "deg1_l2_ll0_lr0_eval"]
    "With early_exit=false and unary operators that return invalid arguments unchanged, the output does not depend on use_fused."
    "As eval-noearly-fused-agree, plus UnaryKeepsInvalid."
    ``evalNoEarlyFusedKeep ``evalNoEarlyFusedKeep_proof,
  entry "eval-noearly-denote" "src/Evaluate.jl" ["eval_tree_array", "dispatch_constant_tree", "EvalContext"]
    "With early_exit=false (and no fusion) evaluation of a non-constant tree never terminates early: it completes and returns the elementwise denotation, valid or not."
    "Well-formed tree; at least one sample; the tree is not constant."
    ``evalNoEarlyDenote ``evalNoEarlyDenote_proof .proven
    "Fixed by PR #269: constant subtrees also honor early_exit=false.",
  entry "eval-noearly-noconst" "src/Evaluate.jl" ["eval_tree_array", "EvalContext"]
    "With early_exit=false and no constant subexpression, evaluation completes with the elementwise denotation, valid or not."
    "As eval-noearly-denote, plus no constant subexpression."
    ``evalNoEarlyNoConst ``evalNoEarlyNoConst_proof,
  entry "eval-zero-samples-leaf" "src/Evaluate.jl" ["eval_tree_array", "deg2_l0_r0_eval", "deg0_eval"]
    "With zero samples and no constant subexpression, the completion flag does not depend on use_fused."
    "Well-formed tree; zero samples (reasonable input); no constant subexpression; is_valid_array exact."
    ``evalZeroSamplesLeaf ``evalZeroSamplesLeaf_proof .proven
    "Fixed by PR #267: a constant leaf reports its own validity under early_exit, so `NaN + x1` on a 1x0 matrix returns flag false fused and unfused.",
  entry "eval-zero-samples-pair" "src/Evaluate.jl" ["eval_tree_array", "deg2_branch0_eval", "dispatch_constant_tree"]
    "With zero samples and finite constants, the completion flag does not depend on use_fused."
    "Well-formed tree; zero samples (reasonable input); finite constants; is_valid_array exact."
    ``evalZeroSamplesPair ``evalZeroSamplesPair_proof .proven
    "Fixed by PR #270: deg2_branch0_eval checks its constant pair like the unfused constant shortcut, so `(1.0/0.0) + x1` on a 1x0 matrix returns flag false fused and unfused.",
  entry "eval-zero-samples-clean" "src/Evaluate.jl" ["eval_tree_array"]
    "With zero samples, finite constants and no constant subexpression, the completion flag does not depend on use_fused."
    "Well-formed tree; zero samples; finite constants; no constant subexpression; is_valid_array exact."
    ``evalZeroSamplesClean ``evalZeroSamplesClean_proof,
  entry "eval-feature-oob" "src/Evaluate.jl" ["eval_tree_array", "get_feature_array", "first_feature_index", "feature_at"]
    "Evaluation never has undefined behaviour (an unchecked out-of-bounds read) for any feature index below 65536; an index beyond the input rows raises an error instead."
    "Tree well-formed for 65535 features; at least one sample."
    ``evalFeatureOOB ``evalFeatureOOB_proof .proven
    "Fixed by PR #264: every feature leaf runs checkbounds(X, feature, :) before the @inbounds kernels, so `x3 + 2.0` on a 2x3 matrix raises BoundsError.",
  entry "eval-wide-buffer" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer", "get_array", "EvalContext"]
    "A matrix ArrayBuffer with more columns than samples (and enough free rows) gives the unbuffered result."
    "Matrix buffer with size(buffer, 2) >= number of samples and at least count_nodes free rows; Finite inputs X (XFinite), finite constants (ConstsFinite), operators mapping finite arguments to finite values (OpsFinite); is_valid_array accepts all-valid arrays."
    ``evalWideBuffer ``evalWideBuffer_proof .proven
    "Fixed by PR #265: get_array views a matrix slot only over the sample columns. Companion: eval-wide-buffer-exact.",
  entry "eval-wide-buffer-exact" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer"]
    "A matrix ArrayBuffer with exactly one column per sample and enough free rows gives the unbuffered result."
    "As eval-wide-buffer, plus size(buffer, 2) == number of samples."
    ``evalWideBufferExact ``evalWideBufferExact_proof,
  entry "eval-small-buffer" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer", "get_array", "get_filled_array", "get_feature_array"]
    "A matrix ArrayBuffer with one column per sample but fewer free rows than the evaluation needs never causes undefined behaviour; running out of slots raises an exception."
    "Matrix buffer with size(buffer, 2) == number of samples; well-formed tree; at least one sample."
    ``evalSmallBuffer ``evalSmallBuffer_proof .proven
    "PR #265 makes slot exhaustion a BoundsError. The fused branch in PR #278 can request a second slot when an inner constant pair is invalid (src/Evaluate.jl:820-836). A buffer sized by count_nodes still suffices; see eval-small-buffer-fits.",
  entry "eval-small-buffer-fits" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer"]
    "A matrix ArrayBuffer with one column per sample and at least count_nodes free rows never raises or has undefined behaviour, for any values."
    "As eval-small-buffer, plus at least count_nodes free rows."
    ``evalSmallBufferFits ``evalSmallBufferFits_proof,
  entry "eval-total" "src/Evaluate.jl" ["eval_tree_array", "get_feature_array", "feature_at"]
    "With every feature index within size(X, 1), evaluation never raises (no undefined behaviour), for any values and every early_exit/use_fused setting."
    "As eval-feature-oob, plus features in 1..size(X, 1)."
    ``evalTotal ``evalTotal_proof .proven
    "Companion of eval-feature-oob.",
  entry "eval-vector" "src/Evaluate.jl" ["eval_tree_array"]
    "A vector input is one sample whose features are its entries: the result is the one-element denotation with flag true."
    "Well-formed tree for length(v) features; every intermediate valid; is_valid_array accepts all-valid arrays."
    ``evalVector ``evalVector_proof,
  entry "eval-mixed" "src/Evaluate.jl" ["eval_tree_array"]
    "The mixed-type overload evaluates the promoted tree on the promoted matrix and returns the promoted denotation."
    "Promoted tree well-formed; every promoted intermediate valid; at least one sample."
    ``evalMixed ``evalMixed_proof,
  entry "eval-context" "src/Evaluate.jl" ["EvalContext", "eval_tree_array", "_is_loopvectorization_loaded"]
    "EvalContext(bumper=true, buffer) accepts the buffer and stores bumper=false; turbo=true without LoopVectorization loaded raises the documented error for Float32/Float64."
    "None beyond the stated element-type facts."
    ``evalContextExt ``evalContextExt_proof,
  entry "eval-turbo-nonnumeric" "src/Evaluate.jl" ["eval_tree_array", "EvalContext"]
    "With LoopVectorization loaded, turbo=true on a non-numeric element type is rejected before evaluation by the `T in (Float32, Float64)` assertion."
    "Non-numeric T (e.g. Vector{Float64})."
    ``evalTurboNonNumeric ``evalTurboNonNumeric_proof .proven
    "Fixed by PR #266: the unreachable numeric-element-type error branch was deleted, so the Float32/Float64 assertion is the documented rejection. Companion: eval-turbo-dispatch.",
  entry "eval-turbo-dispatch" "src/Evaluate.jl" ["eval_tree_array", "EvalContext", "_is_loopvectorization_loaded"]
    "With LoopVectorization loaded and T in (Float32, Float64), turbo=true forwards to the extension evaluator and applies the final validity check."
    "LoopVectorization loaded; T is Float32 or Float64 (hence numeric)."
    ``evalTurboDispatch ``evalTurboDispatch_proof,
  entry "eval-diff-flag" "src/Evaluate.jl" ["differentiable_eval_tree_array"]
    "A true flag from differentiable_eval_tree_array means every output value is valid."
    "Well-formed tree; one(T) * v == v; is_valid_array exact (src/ValueInterface.jl:17-22)."
    ``evalDiffFlag ``evalDiffFlag_proof .proven
    "Fixed by PR #275: deg0_diff_eval checks constant and feature leaves before returning or passing their results to an operator.",
  entry "eval-diff-flag-finite" "src/Evaluate.jl" ["differentiable_eval_tree_array"]
    "With finite input values and constants, a true flag from differentiable_eval_tree_array means every output value is valid."
    "Well-formed tree; one(T) * v == v; finite X entries and finite constants."
    ``evalDiffFlagFinite ``evalDiffFlagFinite_proof,
  entry "eval-diff-denote" "src/Evaluate.jl" ["differentiable_eval_tree_array"]
    "With finite inputs, finite constants, finite-preserving operators and one(T)*v == v, differentiable_eval_tree_array returns the denotation with flag true."
    "Well-formed tree; at least one sample; Finite inputs X (XFinite), finite constants (ConstsFinite), operators mapping finite arguments to finite values (OpsFinite)."
    ``evalDiffDenote ``evalDiffDenote_proof,
  entry "eval-generic-vector" "src/Evaluate.jl" ["eval_tree_array", "GenericOperatorEnum"]
    "With operators that have methods for all arguments and never throw, the generic evaluator on a vector input returns the value the operators compute, flag true, for either throw_errors."
    "Well-formed tree (operator indices in range, features in 1..length(x)); total operators (GOpsTotal)."
    ``evalGenericVector ``evalGenericVector_proof,
  entry "eval-generic-matrix" "src/Evaluate.jl" ["eval_tree_array", "GenericOperatorEnum"]
    "With total operators and throw_errors=true, the generic evaluator on a matrix returns the per-sample values (features sliced along axis 1), including zero samples."
    "Well-formed tree; total operators (GOpsTotal)."
    ``evalGenericMatrix ``evalGenericMatrix_proof,
  entry "eval-generic-throw" "src/Evaluate.jl" ["eval_tree_array", "GenericOperatorEnum"]
    "throw_errors=false never throws and pairs a false flag with nothing; throw_errors=true turns every failure into an ErrorException."
    "None."
    ``evalGenericThrow ``evalGenericThrow_proof,
  entry "eval-alias-fresh" "src/Evaluate.jl" ["eval_tree_array"]
    "For well-formed trees without a buffer, the evaluator succeeds and returns a freshly allocated array (never X, a row of X, or tree storage), leaving the buffer nothing."
    "Well-formed tree."
    ``evalAliasFresh ``evalAliasFresh_proof .proven
    "Success is part of the statement (via the totality lemma evalT_total). Julia check: test/lean/repro/eval-alias-checks.jl (mightalias(y, X) false; X unchanged after fused/unfused evaluations and failed calls).",
  entry "eval-alias-slots" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer"]
    "For well-formed trees and a vector buffer or a matrix buffer with count_nodes free rows, the evaluator succeeds and its output is a slot handed out during this call; in-place kernels write only into such slots."
    "Well-formed tree; buffer fits (BufferFits); buffer not nothing."
    ``evalAliasSlots ``evalAliasSlots_proof .proven
    "Success is part of the statement (via the totality lemma evalT_total).",
  entry "eval-alias-successive" "src/Evaluate.jl" ["eval_tree_array", "ArrayBuffer"]
    "Two evaluations of well-formed trees sharing an ArrayBuffer without reset_index! both succeed and never return the same slot (after a reset the earlier output is overwritten, as documented)."
    "Well-formed trees; vector buffer, or matrix buffer with room for both trees' nodes."
    ``evalAliasSuccessive ``evalAliasSuccessive_proof .proven
    "Success is part of the statement (via the totality lemma evalT_total_room).",
  entry "eval-generic-exposure" "src/Evaluate.jl" ["eval_tree_array", "GenericOperatorEnum"]
    "On a vector input the generic evaluator returns a feature leaf's input element and a constant leaf's own value uncopied; a matrix constant leaf is filled with the tree value."
    "Feature index in range."
    ``evalGenericExposure ``evalGenericExposure_proof .proven
    "Exposure, not a bug (parent aliasing ruling): Julia check shows y === x[1], y === tree.val, and every element of a matrix constant output === tree.val.",
  entry "eval-callable" "src/EvaluationHelpers.jl" ["EvaluationHelpersModule", "set_invalid!"]
    "For well-formed trees, calling a tree never raises, returns one value per sample, and returns the eval_tree_array output when complete and otherwise invalid_value(T) at every sample."
    "Well-formed tree; invalid_value(T) defined."
    ``evalCallable ``evalCallable_proof,
  entry "eval-callable-generic" "src/EvaluationHelpers.jl" ["EvaluationHelpersModule"]
    "Calling a tree with a GenericOperatorEnum on a vector returns the value the operators compute whenever every operator application along the tree has a method and succeeds."
    "Every operator application along the tree succeeds (GOk); eval-generic-vector proves this for total operators."
    ``evalCallableGeneric ``evalCallableGeneric_proof,
  entry "eval-adjoint" "src/EvaluationHelpers.jl" ["EvaluationHelpersModule", "_grad_evaluator", "adjoint"]
    "tree'(X, operators) returns the eval_grad_tree_array gradient when complete, otherwise a same-shape matrix of invalid_value(T); with a GenericOperatorEnum it errors."
    "invalid_value(T) defined; eval_grad_tree_array abstract (owned by the derivative slice)."
    ``evalAdjoint ``evalAdjoint_proof .proven
    "Stated per eval_grad_tree_array outcome; its success is the Deriv slice's property.",
  entry "eval-ext-fallbacks" "src/ExtensionInterface.jl"
    ["node_to_symbolic", "symbolic_to_node", "_zygote_gradient", "is_extension_loaded"]
    "Each extension entry point raises its documented error when the extension is not loaded and forwards to the extension otherwise."
    "None."
    ``evalExtFallbacks ``evalExtFallbacks_proof
]

end DynExpr.Eval
