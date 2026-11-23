import DynExpr.Registry.Types
import DynExpr.Plumbing.Assembly
import DynExpr.Plumbing.Interfaces
import DynExpr.Plumbing.Deprecated
import DynExpr.Plumbing.Precompile
import DynExpr.Plumbing.ConstantsAliases
import DynExpr.Plumbing.Aliasing

namespace DynExpr.Plumbing
open DynExpr.Registry

private def entry (id file : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) (status : Status := .proven) (notes : String := "") : Entry :=
  ⟨id, file, fns, statement, pre, status, prop, some thm, notes⟩

def entries : List Entry := [
  entry "plumbing-exports" "src/DynamicExpressions.jl" ["DynamicExpressions", "@ignore"]
    "Every explicit re-export resolves in its named submodule." "Fixed source binding inventories; parent-approved static fact."
    ``exportsResolve ``exportsResolve_proof,
  entry "plumbing-include-order" "src/DynamicExpressions.jl" ["include"]
    "Definitions precede dependent includes; ignored tests do not execute." "Fixed include sequence; static fact."
    ``bootstrapOrder ``bootstrapOrder_proof,
  entry "plumbing-version-success" "src/DynamicExpressions.jl" ["PACKAGE_VERSION"]
    "Successful TOML version lookup returns the parsed Project.toml version." "Existing package directory and successful parse."
    ``versionSuccess ``versionSuccess_proof,
  entry "plumbing-version-fallback" "src/DynamicExpressions.jl" ["PACKAGE_VERSION"]
    "Missing pkgdir or read/lookup/parse exception returns version 0.0.0." "None."
    ``versionFallback ``versionFallback_proof,
  entry "plumbing-checkout-version" "src/DynamicExpressions.jl" ["PACKAGE_VERSION"]
    "The checkout's package version matches Project.toml version 2.14.0 (origin/master 65884b65)." "Fixed checkout version; static fact."
    ``checkoutVersion ``checkoutVersion_proof,
  entry "plumbing-node-interface" "src/Interfaces.jl" ["NodeInterface", "_check_tree_mapreduce", "_check_equality"]
    "Real plain-Node count traversal equals the independent tree size and recursive equality is reflexive." "Representable bounded-degree trees with lawful Nat scalar equality. Covers these checks, not every mandatory check."
    ``builtinNodeChecks ``builtinNodeChecks_proof,
  entry "plumbing-expression-interface" "src/Interfaces.jl" ["ExpressionInterface", "Expression", "_check_get_contents", "_check_get_metadata", "_check_get_tree", "_check_with_contents", "_check_with_metadata"]
    "Public Expression replacement/getter mirrors return the changed component and preserve the untouched component." "Ordinary Expression; arbitrary well-typed contents and metadata. Covers reconstruction/getter checks."
    ``builtinExpressionChecks ``builtinExpressionChecks_proof,
  entry "plumbing-interface-assignment" "src/Interfaces.jl" ["_check_set_node!"]
    "The real set_node! mirror succeeds, preserves unrelated objects, and gives the target the source tree." "Allocated initialized source/target; valid slots; target not reachable from source."
    ``assignmentCheck ``assignmentCheck_proof,
  entry "plumbing-parametric-registration" "src/Interfaces.jl" ["all_ei_methods_except", "ParametricExpression"]
    "ParametricExpression's fixed registration excludes its three documented optional checks." "Fixed registration table; static fact."
    ``parametricRegistration ``parametricRegistration_proof,
  entry "plumbing-legacy-aliases" "src/deprecated.jl" ["count_constants", "get_constants", "index_constants", "set_constants!", "simplify_tree"]
    "The five concrete deprecated aliases request deprecation and forward unchanged arguments, default/explicit index type, errors and heap effects to public modern mirrors." "Numeric scalar protocol; plain/GraphNode count and index domains represented by the targets."
    ``constantsAliasTargets ``constantsAliasTargets_proof,
  entry "plumbing-legacy-bindings" "src/deprecated.jl" ["EquationModule", "EquationUtilsModule", "EvaluateEquationModule", "EvaluateEquationDerivativeModule", "SimplifyEquationModule", "EvalOptions"]
    "The six deprecated module/type bindings point to their modern targets." "Fixed declaration table; static fact."
    ``bindingTargets ``bindingTargets_proof,
  entry "plumbing-legacy-constructors" "src/deprecated.jl" ["Node", "GraphNode"]
    "All five positional forms request deprecation, reject invalid degree/flag combinations, and forward valid value/child rewrites to the real modern constructor." "Specified Julia conversion protocol. Conversion and target errors remain observable; no success hypothesis."
    ``constructorEquivalence ``constructorEquivalence_proof,
  entry "plumbing-legacy-enums" "src/deprecated.jl" ["OperatorEnum", "GenericOperatorEnum"]
    "Keyword-constructor mirrors request the compiled warning, preserve helper/global options, forward degree pairs, succeed on lawful inputs and retain operator tuples." "Actual Base.@deprecate compiled warning text; modern EnumInput when helpers are enabled, including UInt8 capacity and unambiguous broadcasts."
    ``enumEquivalence ``enumEquivalence_proof,
  entry "plumbing-modes" "src/precompile.jl" ["do_precompilation", "@maybe_setup_workload", "@maybe_compile_workload"]
    "Exactly compile/precompile modes are selected; other Symbols fail." "Total workload operators."
    ``modesExact ``modesExact_proof,
  entry "plumbing-invalid-mode" "src/precompile.jl" ["do_precompilation", "@maybe_setup_workload", "@maybe_compile_workload"]
    "Invalid mode raises the intended ErrorException diagnostic." "Unsupported Symbol mode."
    ``invalidModeError ``invalidModeError_proof .proven
    "Fixed by PR #257: the diagnostic uses repr(mode), so error(...) raises the ErrorException (src/precompile.jl:153,168).",
  entry "plumbing-domain-errors" "src/precompile.jl" ["@ignore_domain_error"]
    "Only DomainError is suppressed; all other exceptions propagate." "None."
    ``domainSuppression ``domainSuppression_proof,
  entry "plumbing-mixed-coverage" "src/precompile.jl" ["test_all_combinations"]
    "Mixed-loop index triples range exactly over the selected unary/binary tuples, independently of outer collection sizes." "Arbitrary lists of alternative tuple lengths; every non-skipped iteration."
    ``mixedCoverage ``mixedCoverage_proof .proven
    "Fixed by PR #258: the mixed loop iterates eachindex(binops) and eachindex(unaops) (src/precompile.jl:70-72).",
  entry "plumbing-cycle-bounds" "src/precompile.jl" ["test_functions_on_trees"]
    "Cycled operator indices stay within 1..the selected tuple length." "Positive tuple length."
    ``cycleBounds ``cycleBounds_proof,
  entry "plumbing-functions-tree" "src/precompile.jl" ["test_functions_on_trees"]
    "Every unary/binary operator index in the actual cycling workload tree belongs to its selected tuple." "Both operator tuple lengths lie in 1..255."
    ``functionsTreeIndices ``functionsTreeIndices_proof,
  entry "plumbing-workload-api" "src/precompile.jl" ["test_functions_on_trees", "do_precompilation"]
    "The fixed workload operation inventory resolves to ordinary core API bindings." "Fixed source inventory; parent-approved static fact."
    ``workloadAgreement ``workloadAgreement_proof,
  entry "plumbing-getter-arrays-fresh" "src/deprecated.jl" ["get_constants"]
    "The immutable-scalar numeric getter succeeds with distinct fresh arrays; mutating its values vector succeeds without mutating source nodes." "Immutable Nat scalar contents; initialized finite graph and sufficient fuel; plain Node input is alias-free."
    ``getterArrayMutationIsolated ``getterArrayMutationIsolated_proof,
  entry "plumbing-getter-ref-exposure" "src/deprecated.jl" ["get_constants"]
    "The numeric getter succeeds and returns the original value objects plus refs to the source nodes; shallow mutable Number exposure is intentional." "Initialized finite numeric graph and sufficient fuel; plain Node input is alias-free. Q31 accepts live element objects."
    ``borrowedReferenceMutation ``borrowedReferenceMutation_proof,
  entry "plumbing-getter-ref-rebinding" "src/deprecated.jl" ["get_constants"]
    "Ref wrappers have distinct identities, and rebinding one succeeds without rebinding another wrapper pointing at the same node." "Separate getter-created Ref allocations; no success assumption."
    ``referenceRebindingIsolated ``referenceRebindingIsolated_proof,
  entry "plumbing-index-objects-fresh" "src/deprecated.jl" ["index_constants"]
    "Every object allocated for the public indexed-tree result is fresh relative to existing objects, whose contents remain unchanged." "Previously allocated source address; default UInt16 index with at most 65535 constants."
    ``indexedObjectsFresh ``indexedObjectsFresh_proof,
  entry "plumbing-index-noalias" "src/deprecated.jl" ["index_constants"]
    "The public indexer's freshly allocated plain-Node index result has no repeated object identity." "Default UInt16 index; at most 65535 constants."
    ``indexedObjectsNoAlias ``indexedObjectsNoAlias_proof,
  entry "plumbing-skip-policy" "src/precompile.jl" ["test_all_combinations"]
    "Skipping occurs exactly for both-empty tuples or Float16 with turbo enabled." "All tuple lengths and type/turbo choices."
    ``skipPolicy ``skipPolicy_proof]

end DynExpr.Plumbing
