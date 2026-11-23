import DynExpr.Registry.Types
import DynExpr.Expressions.Wrapper
import DynExpr.Expressions.Algebra
import DynExpr.Expressions.Sampling
import DynExpr.Expressions.HeapCopy
import DynExpr.Expressions.Aliasing
import DynExpr.Expressions.ValidWeights
import DynExpr.Expressions.SamplingTotality

namespace DynExpr.Expressions
open DynExpr.Registry

private def entry (id file : String) (fns : List String) (statement pre : String)
    (prop thm : Lean.Name) (status : Status := .proven) (notes : String := "") : Entry :=
  ⟨id, file, fns, statement, pre, status, prop, some thm, notes⟩

def entries : List Entry := [
  entry "expressions-components" "src/Expression.jl"
    ["AbstractExpression", "Expression", "with_contents", "with_metadata", "get_contents", "get_metadata", "get_tree"]
    "Contents and metadata replacement change exactly the selected component; get_tree equals contents."
    "Concrete Expression implementing the abstract contents/metadata interface."
    ``componentsProperty ``components_proven,
  entry "expressions-metadata-merge" "src/Expression.jl" ["with_metadata", "Metadata"]
    "Keyword metadata merge resolves every queried key to its last update, or retains the old field value."
    "Arbitrary metadata value type, ordered old/update fields and query name; NamedTuple keys are well typed."
    ``keywordMergeProperty ``keywordMerge_proven,
  entry "expressions-evaluation" "src/Expression.jl" ["Expression", "eval_tree_array", "get_operators", "_validate_input"]
    "Wrapper evaluation equals the arbitrary tree evaluator with stored operators."
    "Resolved enum is typed; max feature does not exceed matrix rows; tree evaluator captures unchanged keywords and result buffers."
    ``forwardingProperty ``forwarding_proven,
  entry "expressions-override" "src/Expression.jl" ["get_operators", "get_variable_names", "string_tree"]
    "Explicit operators and variable names override metadata and are passed unchanged to the tree renderer."
    "Well-typed explicit enum and names; arbitrary tree renderer captures other keywords."
    ``overrideProperty ``override_proven,
  entry "expressions-validation" "src/Expression.jl" ["_validate_input", "max_feature", "Expression"]
    "Typed input validation rejects a maximum feature beyond the input row count."
    "Resolved typed enum; matrix input; out-of-range feature."
    ``validationProperty ``validation_proven,
  entry "expressions-constants" "src/Expression.jl" ["get_scalar_constants", "set_scalar_constants!", "count_scalar_constants"]
    "Constant getter and setter forward exactly the same tree, values and references."
    "Arbitrary tree-level callbacks include mutation and errors; numeric scalar constants."
    ``constantsProperty ``constants_proven,
  entry "expressions-equality-hash" "src/Expression.jl" ["==", "hash", "AbstractExpression"]
    "Wrapper equality conjoins tree and metadata equality; hashing composes metadata and tree hashes in source order."
    "Julia equality and hash operations supplied as callbacks; no NaN-reflexivity assumption."
    ``equalityHashProperty ``equalityHash_proven,
  entry "expressions-metadata-copy" "src/Expression.jl" ["copy", "Metadata", "copy_named_tuple"]
    "The real field copier succeeds on allocated metadata, retains every direct array, copies it to fresh independent storage, and preserves source cells."
    "Arbitrary recursive NamedTuple metadata and memory; every array transitively referenced from the metadata is allocated. No identity copier or successful-call hypothesis."
    ``Aliasing.metadataFieldCopyProperty ``Aliasing.metadataFieldCopy_proven,
  entry "expressions-gradient-forwarding" "src/Expression.jl" ["eval_grad_tree_array", "_grad_evaluator", "adjoint", "Expression"]
    "Gradient wrappers pass the stored enum and identical tree/input to the arbitrary tree gradient evaluator."
    "Resolved typed enum; max feature within matrix rows; callback captures gradient mode and keywords."
    ``gradientForwardingProperty ``gradientForwarding_proven,
  entry "expressions-operator-index" "src/ExpressionAlgebra.jl" ["@declare_expression_operator", "apply_operator", "insert_operator_index"]
    "For every degree/catalog/alias/operator, lookup returns exactly the first matching one-based index."
    "Positive degree; supplied catalog slot; at most 255 entries in the selected slot."
    ``Algebra.indexProperty ``Algebra.index_proven,
  entry "expressions-scalar-promotion" "src/ExpressionAlgebra.jl" ["@declare_expression_operator", "insert_operator_index"]
    "Every scalar value on either argument side becomes an ordered constant leaf and preserves expression metadata."
    "Arbitrary expression/tree/catalog/alias/operator; binary lookup succeeds within UInt8 bounds; degree capacity at least two."
    ``Algebra.promotionProperty ``Algebra.promotion_proven .proven
    "Singleton-prefix case of expressions-trailing-expression; both argument orders are covered.",
  entry "expressions-operator-alias" "src/ExpressionAlgebra.jl" ["declare_operator_alias", "apply_operator"]
    "Any unary aliased operator lookup constructs its selected node without changing tree contents or metadata."
    "Arbitrary alias function/operator/expression; unary lookup within UInt8 bounds; capacity at least one."
    ``Algebra.aliasProperty ``Algebra.alias_proven,
  entry "expressions-type-check" "src/ExpressionAlgebra.jl" ["apply_operator", "@declare_expression_operator"]
    "Any differing concrete expression type token in any argument list is rejected before lookup/construction."
    "Argument list has a first expression and another expression with a different concrete type token."
    ``Algebra.typesProperty ``Algebra.types_proven,
  entry "expressions-chaining" "src/ExpressionAlgebra.jl" ["apply_operator", "allow_chaining", "@declare_expression_operator"]
    "Any three scalar/expression arguments chain left-associatively with ordered promoted children and first-expression metadata."
    "Plus or multiplication; expression among first two arguments; matching type tokens; absent ternary match; bounded binary match and sufficient degree capacity."
    ``Algebra.chainProperty ``Algebra.chain_proven,
  entry "expressions-macro-signatures" "src/ExpressionAlgebra.jl" ["@declare_expression_operator"]
    "For every arity and signature, generated membership equals exact length and admissibility; generated signatures always contain an expression."
    "Arbitrary arity and signature from the four source wrapper forms."
    ``Algebra.macroProperty ``Algebra.macro_proven,
  entry "expressions-missing-operator" "src/ExpressionAlgebra.jl" ["apply_operator", "MissingOperatorError"]
    "Any absent nonchained operator in an existing degree slot raises MissingOperatorError."
    "First expression exists; matching concrete types; absent operator; no chaining or at most two arguments; existing degree slot."
    ``Algebra.missingPresentDegreeProperty ``Algebra.missingPresentDegree_proven .proven
    "Companion of expressions-missing-degree restricted to an existing degree slot.",
  entry "expressions-missing-degree" "src/ExpressionAlgebra.jl" ["apply_operator", "@declare_expression_operator", "MissingOperatorError"]
    "Every absent nonchained operator should raise MissingOperatorError even if its degree slot is absent."
    "Arbitrary argument list, expression/catalog/alias/operator; matching types and no matching operator; no chaining or at most two arguments."
    ``Algebra.missingDegreeProperty ``Algebra.missingDegree_proven .proven
    "Fixed by PR #253: the error message interpolates () for an absent degree slot (src/ExpressionAlgebra.jl:80-86).",
  entry "expressions-trailing-expression" "src/ExpressionAlgebra.jl" ["apply_operator", "@declare_expression_operator", "allow_chaining"]
    "Every nonempty scalar prefix followed by an expression should construct a chained plus/multiplication tree."
    "Binary lookup within UInt8 bounds; capacity at least two; no matching higher-arity operator."
    ``Algebra.trailingExpressionProperty ``Algebra.trailingExpression_proven .proven
    "Fixed by PR #254: chaining evaluates op(args[1:(end - 1)]...) by Julia dispatch, so an all-scalar prefix becomes one scalar (src/ExpressionAlgebra.jl:74-79).",
  entry "expressions-general-construction" "src/ExpressionAlgebra.jl" ["apply_operator", "insert_operator_index", "@declare_expression_operator"]
    "Any supported argument list constructs exactly the selected index, ordered promoted trees and first promoted argument metadata."
    "First expression exists; matching concrete types; lookup succeeds; index and arity at most 255; arity within node capacity."
    ``Algebra.constructionProperty ``Algebra.construction_proven,
  entry "expressions-returned-filter" "src/Random.jl" ["NodeSampler", "rand", "_get_node"]
    "Every successful public sample returns a node satisfying its filter, including successful invalid-weight cases."
    "Pure filter and weighting functions; finite acyclic heap with sufficient fuel; abstract range-valid integer draws."
    ``Sampling.returnedFilterProperty ``Sampling.returnedFilter_proven .proven
    "Independent success on reasonable inputs is proved by expressions-uniform-success and expressions-weighted-success, with expressions-matching-success supplying filtering totality.",
  entry "expressions-cumulative-selection" "src/Random.jl" ["NodeSampler", "_sample_idx"]
    "A successful weighted index identifies a cumulative sum strictly greater than the drawn threshold."
    "Arbitrary JF weights and rational draw; shared exact-finite arithmetic model."
    ``Sampling.cumulativeProperty ``Sampling.cumulative_proven .proven
    "Success on reasonable finite/nonnegative positive-total weights is independently proved by expressions-valid-weights; conditional characterization also covers successful invalid-weight cases.",
  entry "expressions-weight-intervals" "src/Random.jl" ["_sample_idx", "rand"]
    "For any weighted draw, every cumulative value preceding the selected index fails the strict threshold comparison."
    "Arbitrary JF weight list, rational draw and successful selection; no nonfinite values are assumed away."
    ``Sampling.intervalsProperty ``Sampling.intervals_proven .proven
    "Success is independently proved by expressions-valid-weights; this property identifies the first strict cumulative interval after that success guarantee.",
  entry "expressions-zero-weight" "src/Random.jl" ["NodeSampler", "_sample_idx"]
    "Any nonempty finite nonnegative vector whose cumulative fold totals zero raises the explicit zero-weight error for every draw."
    "Arbitrary weight list and draw; nonempty list of finite nonnegative weights (the src/Random.jl:88-89 check passes) and a zero total."
    ``Sampling.zeroProperty ``Sampling.zero_proven .proven
    "Since PR #259, negative or nonfinite weights raise ArgumentError before the zero-total check, so the zero-weight message requires valid weights.",
  entry "expressions-negative-weight" "src/Random.jl" ["NodeSampler", "_sample_idx", "rand"]
    "Every vector containing a negative finite weight should be rejected for every valid uniform draw."
    "Arbitrary JF weight vector; rational draw in [0,1); at least one negative finite weight."
    ``Sampling.negativeProperty ``Sampling.negative_proven .proven
    "Fixed by PR #259: _sample_idx raises ArgumentError for any negative or nonfinite weight (src/Random.jl:88-89). Q10 confirmed the old acceptance was a bug.",
  entry "expressions-nonfinite-weight" "src/Random.jl" ["NodeSampler", "_sample_idx"]
    "Every vector containing any nonfinite weight should be rejected for all valid uniform draws."
    "Arbitrary JF weight vector containing NaN or infinity; rational draw in [0,1)."
    ``Sampling.nonfiniteProperty ``Sampling.nonfinite_proven .proven
    "Fixed by PR #259: _sample_idx raises ArgumentError for any negative or nonfinite weight (src/Random.jl:88-89).",
  entry "expressions-empty-filter" "src/Random.jl" ["NodeSampler", "rand"]
    "An empty filter set errors before consuming a random draw."
    "Traversal succeeds and no nodes match."
    ``Sampling.emptyProperty ``Sampling.empty_proven .proven
    "Filtering totality on reasonable source heaps is independently proved by expressions-matching-success; an empty resulting set is an explicit error case.",
  entry "expressions-sampling-sharing" "src/Random.jl" ["NodeSampler", "rand"]
    "For all heaps, roots, fuel and policy flags, traversal returns occurrences or their identity-deduplicated list according to the policy."
    "Arbitrary traversal result, including errors; finite acyclic valid heaps use sufficient fuel."
    ``Sampling.sharingProperty ``Sampling.sharing_proven,
  entry "expressions-random-stream" "src/Random.jl" ["rand", "_sample_idx"]
    "A real draw returns the current uniform-stream value and advances its shared cursor once."
    "Abstract deterministic draw stream; probability law supplied by caller."
    ``Sampling.streamProperty ``Sampling.stream_proven,
  entry "expressions-uniform-success" "src/Random.jl" ["NodeSampler", "rand", "_get_node"]
    "A nonempty filter set always yields a matching unweighted sample and consumes one draw."
    "Pure filter; successful finite traversal; unweighted sampler; abstract range-valid integer draw stream."
    ``Sampling.uniformSuccessProperty ``Sampling.uniformSuccess_proven .proven
    "Successful filtering on every reasonable decoded source heap is independently proved by expressions-matching-success.",
  entry "expressions-copy-keyword" "src/Expression.jl" ["copy_node", "copy", "Expression"]
    "copy_node should pass every requested sharing option through to direct copy for every decodable heap expression."
    "Finite decodable source tree, arbitrary metadata and sharing options; sufficient fuel."
    ``HeapCopy.copyKeywordProperty ``HeapCopy.copyKeyword_proven .proven
    "Fixed by PR #255: copy_node(ex::AbstractExpression; kws...) forwards to copy(ex; kws...) (src/Expression.jl:292).",
  entry "expressions-direct-graph-copy" "src/Expression.jl" ["copy", "Expression"]
    "Direct copy passes every heap root, sharing option and metadata value to the raw copier with the resolved policy."
    "Arbitrary heap expression, copy fuel and preserve/break flags; results include errors."
    ``HeapCopy.directCopyProperty ``HeapCopy.directCopy_proven,

  entry "expressions-getters-expose-objects" "src/Expression.jl" ["get_contents", "get_tree", "get_metadata", "Expression"]
    "For every expression and field path, getters expose exactly the stored tree, metadata value and buffer identity."
    "Arbitrary well-typed heterogeneous metadata, root identity and nested field path; Julia borrowing semantics."
    ``Aliasing.gettersExposureProperty ``Aliasing.gettersExposure_proven,
  entry "expressions-replacements-share" "src/Expression.jl" ["with_contents", "with_metadata"]
    "Every replacement borrows the supplied component and retains the exact untouched component, including nested buffer paths."
    "Arbitrary expression, replacement root/metadata and field path; documented replacement semantics."
    ``Aliasing.replacementsExposureProperty ``Aliasing.replacementsExposure_proven,
  entry "expressions-deep-metadata-copy" "src/Expression.jl" ["copy", "Metadata", "copy_named_tuple"]
    "Every allocated inner metadata array is detached from the corresponding successful copy."
    "Arbitrary source/copy stores, expressions, field paths and array indices with allocated inner storage; metadata copy succeeds."
    ``Aliasing.deepMetadataCopyProperty ``Aliasing.deepMetadataCopy_proven .proven
    "Fixed by PR #256: _copy(::AbstractArray) deep-copies arrays whose element type is not static, with a fresh identity dictionary per call (src/Expression.jl:42-52 and src/Utils.jl:32-55), so every copied array references only arrays allocated by the same copy. Success is proved by expressions-metadata-copy-success.",
  entry "expressions-flat-metadata-isolation" "src/Expression.jl" ["copy", "Metadata"]
    "Every successful flat numeric metadata copy creates fresh storage; arbitrary writes to the copy preserve the source vector."
    "Arbitrary stores, root and array identities, key names, numeric values and writes; source allocated and copy/write succeed."
    ``Aliasing.flatCopyProperty ``Aliasing.flatCopy_proven .proven
    "Independent metadata-copy success is proved by expressions-metadata-copy-success; arbitrary writes to the fresh allocated output always succeed, as expressions-flat-owned-metadata-copy proves.",
  entry "expressions-tuple-field-isolation" "src/Expression.jl" ["copy", "Metadata", "copy_named_tuple"]
    "Nested NamedTuple array fields are copied recursively; repeated source buffer fields become independent copies."
    "Arbitrary recursively nested metadata values or field lists and stores; successful recursive copy."
    ``Aliasing.tupleAndRepeatedCopyProperty ``Aliasing.tupleAndRepeatedCopy_proven .proven
    "Success for arbitrary recursively allocated metadata is independently proved by expressions-metadata-copy-success.",
  entry "expressions-keyword-buffer-borrowing" "src/Expression.jl" ["with_metadata"]
    "For every root, old/update field list and query, metadata merge retains contents and the last live supplied field value."
    "Arbitrary NamedTuple field values including buffer identities; component replacement does not request a copy."
    ``Aliasing.keywordAliasProperty ``Aliasing.keywordAlias_proven,
  entry "expressions-constant-live-refs" "src/Expression.jl" ["get_scalar_constants", "set_scalar_constants!"]
    "Every numeric getter returns scalar values paired with the live selected node identities; setters write through those identities."
    "Arbitrary numeric graph/root/fuel/sharing policy, buffer store and successful getter/setter outputs; legal trees use adequate fuel."
    ``Aliasing.constantsAliasProperty ``Aliasing.constantsAlias_proven .proven
    "Getter success for reasonable decoded source heaps is independently proved by expressions-scalar-getter-success; setter success is proved constructively here.",
  entry "expressions-operand-borrowing" "src/ExpressionAlgebra.jl" ["apply_operator", "insert_operator_index", "@declare_expression_operator"]
    "Declared operations allocate a new branch root while borrowing operand roots and first-operand metadata."
    "Expression arguments; valid binary index; source roots allocated and separate for legal plain Node output."
    ``Aliasing.operandBorrowingProperty ``Aliasing.operandBorrowing_proven,
  entry "expressions-scalar-vector-isolation" "src/Expression.jl" ["get_scalar_constants"]
    "Numeric constant getter output has fresh vector storage; writes to it preserve existing buffers."
    "Arbitrary graph/root/fuel/sharing policy and stores; successful numeric getter, existing source buffer and successful output-vector write."
    ``Aliasing.scalarVectorIsolationProperty ``Aliasing.scalarVectorIsolation_proven .proven
    "Independent getter success is proved by expressions-scalar-getter-success; arbitrary writes to its allocated vector succeed by expressions-heap-write-success.",
  entry "expressions-dictionary-copy" "src/Expression.jl" ["copy", "Metadata", "_copy"]
    "Dictionaries with immutable numeric values copy to fresh equal storage and allocate no arrays; arbitrary outer writes preserve the source."
    "Allocated source dictionary; arbitrary keys, numeric entries, array memory, stores and writes."
    ``Aliasing.dictionaryFlatCopyProperty ``Aliasing.dictionaryFlatCopy_proven .proven
    "Numeric-valued case of master's Dict deepcopy (src/Expression.jl:42 on origin/master); reference-valued entries are covered by expressions-dictionary-deep-copy. Success is independently proved by expressions-dictionary-copy-success.",
  entry "expressions-dictionary-deep-copy" "src/Expression.jl" ["copy", "Metadata", "_copy"]
    "No entry of a successfully copied metadata dictionary references an allocated source array."
    "Arbitrary dictionary and array stores, source dictionary, copied entries, key and allocated inner array; dictionary copy succeeds."
    ``Aliasing.dictionaryDeepCopyProperty ``Aliasing.dictionaryDeepCopy_proven .proven
    "Fixed by PR #256: a Dict is not static, so _copy deep-copies it (src/Expression.jl:42 and src/Utils.jl:32-55). Success is proved by expressions-dictionary-copy-success.",
  entry "expressions-sampler-borrows-node" "src/Random.jl" ["NodeSampler", "rand", "_get_node"]
    "Sampling one eligible object returns that exact live source node identity; traversal does not clone nodes."
    "One eligible node; pure filter; unweighted range-valid integer draw stream."
    ``Aliasing.samplerBorrowProperty ``Aliasing.samplerBorrow_proven .proven
    "Filtering success on valid source heaps is independently proved by expressions-matching-success; unweighted rand success is proved by expressions-uniform-success.",
  entry "expressions-forwarded-buffer-identities" "src/Expression.jl" ["eval_tree_array", "eval_grad_tree_array", "_grad_evaluator"]
    "Wrapper evaluation returns the identical value and gradient buffer identities supplied by the backend."
    "Typed enum, valid feature rows, and tree callback with explicit output buffer identities."
    ``bufferIdentityProperty ``bufferIdentity_proven,
  entry "expressions-full-copy-isolation" "src/Expression.jl" ["copy", "Expression"]
    "Every successful full expression copy allocates a fresh root and recursive metadata buffers while preserving source node and metadata cells."
    "Arbitrary heap expression, metadata memory, fuel and sharing options; copy succeeds (legal finite trees use sufficient fuel)."
    ``Aliasing.fullCopyIsolationProperty ``Aliasing.fullCopyIsolation_proven .proven
    "Full copying success on reasonable decoded sources whose transitively referenced metadata arrays are allocated is independently proved by expressions-full-copy-success.",
  entry "expressions-valid-weights" "src/Random.jl" ["NodeSampler", "_sample_idx"]
    "All finite nonnegative weights with positive total produce a valid selected index and its exact cumulative interval for every draw in [0,1)."
    "Arbitrary finite rational weight list; each weight nonnegative; positive total; valid uniform draw. No call-success assumption."
    ``ValidWeights.validWeightsProperty ``ValidWeights.validWeights_proven .proven
    "Shared safe-domain companion to expressions-negative-weight and expressions-nonfinite-weight; excludes precisely weights that cannot represent finite probabilities.",
  entry "expressions-weighted-success" "src/Random.jl" ["NodeSampler", "rand", "_get_node"]
    "Every filtered finite nonnegative weighting with positive total returns a matching source node and consumes exactly one draw."
    "Arbitrary sampler, RNG and finite weighting; matching node list exists; eligible weights nonnegative with positive total; current draw in [0,1)."
    ``ValidWeights.weightedSuccessProperty ``ValidWeights.weightedSuccess_proven .proven
    "Filtering success on valid source heaps is independently proved by expressions-matching-success; sampleIdx success comes from expressions-valid-weights.",

  entry "expressions-copy-success" "src/Expression.jl" ["copy", "Expression"]
    "Every finite decoded heap expression succeeds under direct copying for all sharing options."
    "Arbitrary allocated finite source decoded with sufficient fuel, metadata and preserve/break options."
    ``HeapCopy.copySuccessProperty ``HeapCopy.copySuccess_proven,
  entry "expressions-copy-keyword-safe" "src/Expression.jl" ["copy_node", "copy", "Expression"]
    "The keyword wrapper and requested copy both succeed with the same result when sharing need not be broken."
    "Finite decoded input; break_sharing=false, preserve_sharing=false, or source Graph.NoAlias; arbitrary metadata/fuel/options."
    ``HeapCopy.copyKeywordSafeProperty ``HeapCopy.copyKeywordSafe_proven .proven
    "Companion to expressions-copy-keyword (whose PR #255 fix makes the wrapper equal on every input); adds success of both calls on the stated domain.",
  entry "expressions-operator-noalias-safe" "src/ExpressionAlgebra.jl" ["@declare_expression_operator", "apply_operator", "insert_operator_index"]
    "Binary insertion preserves NoAlias for all individually unaliased, jointly disjoint allocated operand trees."
    "Arbitrary heap/expressions/operator; both sources NoAlias; all reachable source addresses allocated; no common reachable identity; op in 1..255."
    ``Aliasing.operatorDisjointNoAliasProperty ``Aliasing.operatorDisjointNoAlias_proven .proven
    "Accepted Q6 domain: individually alias-free, mutually disjoint source trees. The repeated-operand verdict is owned by NoAlias.",
  entry "expressions-flat-owned-metadata-copy" "src/Expression.jl" ["copy", "Metadata", "copy_named_tuple"]
    "All numeric-only arrays nested in arbitrary tuples copy to fresh independent buffers; arbitrary writes to copied arrays preserve source cells."
    "All source metadata arrays allocated and contain immutable numeric elements; arbitrary recursive tuples, stores and writes."
    ``Aliasing.flatOwnedMetadataCopyProperty ``Aliasing.flatOwnedMetadataCopy_proven .proven
    "Numeric-only case of master's _copy (src/Expression.jl:43 on origin/master); arrays with reference-valued elements are deep-copied, see expressions-deep-metadata-copy. Success is independently proved by expressions-metadata-copy-success.",
  entry "expressions-metadata-copy-success" "src/Expression.jl" ["copy", "Metadata", "copy_named_tuple"]
    "Copying any metadata value, arbitrary tuple fields or complete metadata succeeds when every transitively referenced array is allocated."
    "Arbitrary recursive metadata and stores; every array reachable from a metadata array identity through reference-valued elements is allocated. No copy-success assumption."
    ``Aliasing.metadataCopySuccessProperty ``Aliasing.metadataCopySuccess_proven,
  entry "expressions-dictionary-copy-success" "src/Expression.jl" ["copy", "Metadata", "_copy"]
    "Every allocated metadata dictionary whose referenced arrays are transitively allocated copies successfully."
    "Arbitrary allocated dictionary identity/store and entry list, including reference-valued entries; every array reachable from a referenced entry is allocated."
    ``Aliasing.dictionaryCopySuccessProperty ``Aliasing.dictionaryCopySuccess_proven,
  entry "expressions-scalar-getter-success" "src/Expression.jl" ["get_scalar_constants", "Expression"]
    "Finite decoded source heaps make all traversal policies and numeric scalar getters succeed."
    "Arbitrary finite decoded source graph/root/fuel and sharing flags, buffer stores; sufficient decode fuel."
    ``Aliasing.scalarGetterSuccessProperty ``Aliasing.scalarGetterSuccess_proven,
  entry "expressions-full-copy-success" "src/Expression.jl" ["copy", "Expression"]
    "Full expression copying succeeds for any finite decoded source tree and metadata whose transitively referenced arrays are allocated."
    "Arbitrary graph, metadata memory, root/expression, fuel and sharing flags; decoded source and every array reachable from the metadata allocated."
    ``Aliasing.fullCopySuccessProperty ``Aliasing.fullCopySuccess_proven,
  entry "expressions-matching-success" "src/Random.jl" ["NodeSampler", "rand"]
    "NodeSampler filtering succeeds for every finite decoded source heap, arbitrary pure filter and sharing options."
    "Arbitrary sampler whose source graph is decoded with its supplied fuel; no successful filtering assumption."
    ``SamplingTotality.matchingSuccessProperty ``SamplingTotality.matchingSuccess_proven,
  entry "expressions-heap-write-success" "src/Expression.jl" ["get_scalar_constants", "set_scalar_constants!", "copy"]
    "Mutating any allocated getter or copied buffer succeeds for every replacement value."
    "Arbitrary value type, heap, allocated buffer identity, current and replacement values. No write-success assumption."
    ``Aliasing.heapWriteSuccessProperty ``Aliasing.heapWriteSuccess_proven


]

end DynExpr.Expressions
