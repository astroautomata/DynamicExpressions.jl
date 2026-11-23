import DynExpr.Registry.Types
import DynExpr.NodeUtils.Operators
import DynExpr.NodeUtils.Preallocation
import DynExpr.NodeUtils.Composite
import DynExpr.NodeUtils.GraphIndex
import DynExpr.NodeUtils.IndexCapacity
import DynExpr.NodeUtils.Memory
import DynExpr.NodeUtils.Success
import DynExpr.NodeUtils.CopySharing
import DynExpr.NodeUtils.IndexSharingTree

namespace DynExpr.NodeUtils

private def entry (id file : String) (fns : List String) (p t : Lean.Name)
    (statement preconditions : String) (status : DynExpr.Registry.Status := .proven)
    (notes : String := "") : DynExpr.Registry.Entry :=
  { id := id, juliaFile := file, juliaFns := fns, statement := statement
    preconditions := preconditions, status := status, prop := p, thm := some t, notes := notes }

def entries : List DynExpr.Registry.Entry := [
  entry "nodeutils-nullable-access" "src/Utils.jl" ["Nullable", "getindex"]
    ``NullableAccess ``nullableAccess_proven "Non-null payload reads; null access raises UndefRefError." "All payloads.",
  entry "nodeutils-nullable-convert" "src/Utils.jl" ["Nullable", "convert"]
    ``NullableConversion ``nullableConversion_proven "Accessing a converted nullable gives the converted payload for live values and preserves the null access error." "Total payload conversion; both live and null inputs.",
  entry "nodeutils-fill-shape" "src/Utils.jl" ["fill_similar"]
    ``FilledShape ``filledShape_proven "Requested dense length is preserved and every value is filled." "Dense vector, any requested length.",
  entry "nodeutils-invalid-fill" "src/Utils.jl" ["set_invalid!"]
    ``InvalidFill ``invalidFill_proven "Invalid fill preserves length and makes every nonempty output invalid." "Floating scalar vector; empty vector allowed.",
  entry "nodeutils-varmap-conflict" "src/Utils.jl" ["deprecate_varmap"]
    ``DeprecatedConflict ``deprecatedConflict_proven "Both old and new name maps raise an assertion." "Both arguments supplied.",
  entry "nodeutils-scalar-roundtrip" "src/ValueInterface.jl" ["pack_scalar_constants!", "unpack_scalar_constants"]
    ``ScalarRoundtrip ``scalarRoundtrip_proven "Packing and unpacking any scalar in any allocated buffer slot preserves it and advances exactly one position." "Arbitrary numeric buffer and scalar with matching type; 1 <= idx <= buffer length.",
  entry "nodeutils-scalar-count" "src/ValueInterface.jl" ["count_scalar_constants", "pack_scalar_constants!", "unpack_scalar_constants"]
    ``ScalarCountOne ``scalarCountOne_proven "Declared scalar count equals actual packing and unpacking index advancement, while preserving buffer length." "Arbitrary numeric scalar, buffer and allocated one-based slot.",
  entry "nodeutils-invalid-scalar" "src/ValueInterface.jl" ["invalid_value", "is_valid"]
    ``InvalidScalar ``invalidScalar_proven "Invalid values constructed for every real or complex floating type shape fail validity." "Real or complex floating type input.",
  entry "nodeutils-generic-validity" "src/ValueInterface.jl" ["is_valid_array", "is_valid"]
    ``GenericValidity ``genericValidity_proven "Nonnumeric array validity agrees with elementwise validity." "Any total validity predicate.",
  entry "nodeutils-array-overflow" "src/ValueInterface.jl" ["is_valid_array", "is_valid"]
    ``NumericArrayElementwise ``numericArrayElementwise_proven "Numeric array validity agrees with elementwise validity." "Two representable Float16 values." .proven
    "Fixed by PR #249: is_valid_array on floating arrays falls back to elementwise validity when the sum is not finite (src/ValueInterface.jl:18-22). Before, two finite Float16 maxima summed to infinity and the array was rejected.",
  entry "nodeutils-enum-index" "src/OperatorEnum.jl" ["AbstractOperatorEnum", "getindex"]
    ``EnumIndex ``enumIndex_proven "Enum indexing returns the selected degree tuple." "Present degree slot; one-based public index.",
  entry "nodeutils-enum-length" "src/OperatorEnum.jl" ["AbstractOperatorEnum", "length"]
    ``EnumLength ``enumLength_proven "Enum length counts degree tuples, including empty tuples." "Typed or generic enum.",
  entry "nodeutils-enum-copy" "src/OperatorEnum.jl" ["AbstractOperatorEnum", "copy"]
    ``EnumCopy ``enumCopy_proven "Immutable enum copy is the original wrapper." "Typed or generic enum.",
  entry "nodeutils-enum-properties" "src/OperatorEnum.jl" ["AbstractOperatorEnum", "unaops", "binops"]
    ``EnumDegreeProperties ``enumDegreeProperties_proven "Every enum exposes its first degree tuple or bounds error; its binary property is the second degree tuple or empty when absent." "Arbitrary typed or generic enum and arbitrary operator tuples.",
  entry "nodeutils-depth" "src/NodeUtils.jl" ["count_depth"]
    ``DepthCorrect ``depthCorrect_proven "Depth equals one plus the maximum child depth, with leaf depth one." "Finite tree.",
  entry "nodeutils-counts" "src/NodeUtils.jl" ["count_constant_nodes", "count_scalar_constants", "get_scalar_constants"]
    ``CountsAgree ``countsAgree_proven "Both numeric constant counts equal the depth-first getter length." "Finite unshared plain Node tree; numeric constants.",
  entry "nodeutils-presence" "src/NodeUtils.jl" ["has_constants", "has_operators"]
    ``PresenceCorrect ``presenceCorrect_proven "Presence predicates agree with positive constant count and nonzero root degree." "Finite representable tree.",
  entry "nodeutils-roundtrip" "src/NodeUtils.jl" ["get_scalar_constants", "set_scalar_constants!"]
    ``ConstantsRoundtrip ``constantsRoundtrip_proven "Every initialized finite numeric source has a successful getter and restoring its returned values preserves the entire heap." "Explicit Graph.NoAlias; Traversable source structure supplies adequate fuel and initialized active fields.",
  entry "nodeutils-set-get" "src/NodeUtils.jl" ["get_scalar_constants", "set_scalar_constants!"]
    ``NumericSetGet ``numericSetGet_proven "Setting any matching vector of numeric constants through distinct allocated refs succeeds and the getter read stage returns exactly those values." "Arbitrary source graph, numeric values and distinct refs; matching lengths and allocated ref cells.",
  entry "nodeutils-sharing-count" "src/NodeUtils.jl" ["count_constant_nodes", "count_scalar_constants", "get_scalar_constants"]
    ``SharedCounting ``sharedCounting_proven "Every acyclic initialized shared graph has a successful getter whose scalar/reference lengths equal its unique constant count." "Arbitrary numeric scalar type, source graph and root; Traversable supplies initialized active fields and adequate fuel.",
  entry "nodeutils-dfs-index" "src/NodeUtils.jl" ["NodeIndex", "index_constant_nodes", "get_scalar_constants"]
    ``TreeIndexLabels ``treeIndexLabels_proven "For every plain tree, constant leaves get consecutive depth-first indices, features get zero, and the final counter equals the constant count." "Arbitrary scalar type and tree; at most 65535 constant leaves.",
  entry "nodeutils-index-capacity" "src/NodeUtils.jl" ["NodeIndex", "index_constant_nodes"]
    ``PublicIndexCapacity ``publicIndexCapacity_proven "The final constant index is nonzero within the UInt16 capacity." "Finite representable tree with 1 to 65535 constant leaves; public counter starts at zero.",
  entry "nodeutils-composite-empty" "src/NodeUtils.jl" ["get_scalar_constants", "set_scalar_constants!"]
    ``EmptyCompositeRoundtrip ``emptyCompositeRoundtrip_proven "Getting then setting composite constants preserves every tree using a lawful numeric-vector protocol." "Arbitrary NoAlias initialized finite source, options and getter outputs; lawful vector protocol that packs and unpacks only its own slots (VectorProtocolLocal) and Traversable input structure." .proven
    "Fixed by PR #250: the setter loops over every ref, so a trailing zero-count constant is unpacked (src/NodeUtils.jl:134-139). Before, it exited early and raised an error. VectorProtocolLocal excludes protocols whose pack overwrites other values' slots, for which no setter could round-trip.",
  entry "nodeutils-composite-laws" "src/ValueInterface.jl" ["count_scalar_constants", "pack_scalar_constants!", "unpack_scalar_constants"]
    ``EmptyProtocolLaws ``emptyProtocolLaws_proven "Numeric-vector counts equal length; packing and unpacking preserve every vector and advance by its length." "Arbitrary values, buffers and equal-length unpack templates; one-based index with sufficient allocated slots.",
  entry "nodeutils-update-frame" "src/NodeUtils.jl" ["set_scalar_constants!"]
    ``ValueUpdateFrame ``valueUpdateFrame_proven "Writes to existing constant refs succeed and preserve every non-value field and every other identity." "Existing allocated ref; arbitrary source graph and scalar value.",
  entry "nodeutils-container-capacity" "src/NodePreallocation.jl" ["allocate_container"]
    ``ContainerCapacity ``containerCapacity_proven "Allocation returns exactly the requested number of slots." "Nonnegative requested length.",
  entry "nodeutils-copy-sharing" "src/NodePreallocation.jl" ["copy_into!", "allocate_container", "leaf_copy_into!", "branch_copy_into!"]
    ``CopySharing ``copySharing_proven "Every initialized acyclic source copies successfully with equal unfolded trees, exact sharing structure, preserved leaf/branch fields, and one destination slot per unique reachable object." "Arbitrary scalar type/options/graphs/root; GraphWF, PathFuel, initialized source; NoAlias for plain Node; distinct initialized destination slots and adequate capacity.",
  entry "nodeutils-graph-index" "src/NodeUtils.jl" ["NodeIndex", "index_constant_nodes", "get_scalar_constants"]
    ``GraphIndexConsistency ``graphIndexConsistency_proven "Every acyclic GraphNode source indexes successfully in first-visit order 1..k; two constant occurrences have the same index exactly when they are the same object, and feature leaves get zero." "Arbitrary scalar type/graph/root; initialized finite unfolding with adequate fuel; at most 65535 unique constant objects.",
  entry "nodeutils-filled-array-fresh" "src/Utils.jl" ["fill_similar"]
    ``FilledArrayFresh ``filledArrayFresh_proven "Filled output storage is fresh and cannot overwrite existing input arrays." "Existing source array object; dense output allocation.",
  entry "nodeutils-setter-buffer-detached" "src/NodeUtils.jl" ["set_scalar_constants!"]
    ``NumericSetterDetached ``numericSetterDetached_proven "Every valid numeric setter succeeds and later caller-vector changes do not change stored primitive scalar values." "Arbitrary graphs, input array heaps and replacement vectors; distinct allocated refs and matching lengths.",
  entry "nodeutils-getter-ref-exposure" "src/NodeUtils.jl" ["get_scalar_constants", "set_scalar_constants!"]
    ``NumericGetterRefs ``numericGetterRefs_proven "Reading allocated numeric refs succeeds, preserves those refs, and returns exact values in fresh storage without changing existing arrays." "Arbitrary source/array heaps and valid refs; intentional node-reference exposure.",
  entry "nodeutils-container-disjoint" "src/NodePreallocation.jl" ["allocate_container", "copy_into!"]
    ``ContainerDisjoint ``containerDisjoint_proven "For every input heap and requested size, allocated slots are distinct and fresh, and every existing source cell is preserved." "Arbitrary node heap and nonnegative requested capacity.",
  entry "nodeutils-invalid-array-frame" "src/Utils.jl" ["set_invalid!"]
    ``InvalidArrayFrame ``invalidArrayFrame_proven "Invalid fill succeeds in place and preserves all distinct dense owner-array storage." "Existing dense owner-array object; arbitrary elements; other objects have distinct nonoverlapping storage.",
  entry "nodeutils-fill-payload-exposure" "src/Utils.jl" ["fill_similar"]
    ``FillPayloadExposure ``fillPayloadExposure_proven "Object-valued fill intentionally repeats the supplied live payload identity." "Caller object payload; standard fill semantics.",
  entry "nodeutils-setter-payload-exposure" "src/NodeUtils.jl" ["set_scalar_constants!"]
    ``SetterPayloadExposure ``setterPayloadExposure_proven "Scalar assignment through any existing ref succeeds and stores the supplied live payload identity." "Arbitrary graph, existing cell and scalar payload identity; ordinary in-place setter semantics.",
  entry "nodeutils-scalar-getter-success" "src/NodeUtils.jl" ["get_scalar_constants", "count_scalar_constants"]
    ``ScalarGetterSuccess ``scalarGetterSuccess_proven "The numeric getter succeeds for every initialized finite source with adequate traversal fuel." "Traversable initialized active node structure; NoAlias for plain Node sources; arbitrary sharing option and numeric scalar type.",
  entry "nodeutils-array-no-overflow" "src/ValueInterface.jl" ["is_valid_array", "is_valid"]
    ``NumericArrayElementwiseNoOverflow ``numericArrayElementwiseNoOverflow_proven "Companion of nodeutils-array-overflow (implied by it since PR #249): Float16 pair validity equals elementwise validity whenever finite addition does not overflow." "NoFloat16SumOverflow restricts finite sums to (-65520,65520); NaN and infinity inputs remain included.",
  entry "nodeutils-composite-getter-success" "src/NodeUtils.jl" ["get_scalar_constants"]
    ``CompositeGetterSuccess ``compositeGetterSuccess_proven "The composite getter succeeds for every initialized finite source and lawful numeric-vector protocol." "NoAlias source graph; Traversable initialized active fields and adequate fuel; lawful packing/unpacking/count protocol.",
  entry "nodeutils-composite-no-trailing-empty" "src/NodeUtils.jl" ["get_scalar_constants", "set_scalar_constants!"]
    ``CompositeRoundtripNoTrailingEmpty ``compositeRoundtripNoTrailingEmpty_proven "Composite getters succeed and restoring their numeric-vector output restores the source when its final constant vector is nonempty." "Arbitrary NoAlias initialized finite sources; no constants or nonempty last constant vector; intermediate empty vectors are permitted.",
  entry "nodeutils-copy-immutable-values" "src/NodePreallocation.jl" ["copy_into!", "leaf_copy_into!", "branch_copy_into!"]
    ``CopyIntoImmutableValues ``copyIntoImmutableValues_proven "copy_into! succeeds for immutable scalar constants; overwriting a selected copied constant preserves every source node and mutable value object." "Arbitrary initialized acyclic source/options/storage/path; reachable constants are immutable scalars; fresh adequate destination storage; NoAlias for plain Node."
]

end DynExpr.NodeUtils
