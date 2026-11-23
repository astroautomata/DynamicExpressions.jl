import DynExpr.Registry.Types
import DynExpr.NodeBase.Types
import DynExpr.NodeBase.TreeOps
import DynExpr.NodeBase.Heap
import DynExpr.NodeBase.Traverse
import DynExpr.NodeBase.TraverseCount
import DynExpr.NodeBase.IterateLength
import DynExpr.NodeBase.TraverseCopy
import DynExpr.NodeBase.TypesCopy
import DynExpr.NodeBase.CopyValue
import DynExpr.NodeBase.TraverseComp
import DynExpr.NodeBase.GraphEq

/-! Slice root: imports this slice's files and lists its registry entries. -/

namespace DynExpr.NodeBase

open DynExpr.Registry in
/-- Registry entries for `src/Node.jl` and `src/base.jl`. -/
def entries : List DynExpr.Registry.Entry := [
  { id := "nodebase-ctor-type"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node", "GraphNode", "AbstractExpressionNode", "AbstractNode"]
    statement := "Constructor element types: leaves take T from the type, then the explicit T argument, then the value's runtime type (features default to Float32); branches whose children share the parent's degree get promote_type of the children's element types and keep that degree."
    preconditions := "Branch: nonempty children of one wrapper kind and degree D, at most D of them."
    status := .proven
    prop := ``ctor_type
    thm := some ``ctor_type_holds },
  { id := "nodebase-ctor-children-degree"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node"]
    statement := "Node(; op, children) with children of one concrete type Node{T,D} (count <= D) succeeds and returns a Node{T,D}."
    preconditions := "1 <= number of children <= D; every node in each child has degree <= D."
    status := .proven
    prop := ``ctor_children_degree
    thm := some ``ctor_children_degree_holds
    notes := "Fixed by PR #234: the branch constructor takes the maximum degree from the children when the called type has none (src/Node.jl:419-424). Before, the bare wrapper used max_degree(Node) = 2 and converting D=3 children threw." },
  { id := "nodebase-ctor-nodes"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node", "GraphNode", "get_children"]
    statement := "val gives a fresh constant leaf, feature a fresh feature leaf, op with children (or l/r) a fresh branch whose get_children are exactly the given children with degree = number of children; existing objects are unchanged; l/r are equivalent to children=(l,) / (l, r)."
    preconditions := "feature <= 65535; op <= 255; number of children <= D."
    status := .proven
    prop := ``ctor_nodes
    thm := some ``ctor_nodes_holds },
  { id := "nodebase-ctor-child-arg"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node"]
    statement := "Every child passed to the constructor through l, r or children is stored, in order, as the children of the result, or the call throws."
    preconditions := "None (all keyword combinations)."
    status := .proven
    prop := ``ctor_child_arg
    thm := some ``ctor_child_arg_holds
    notes := "Fixed by PR #235: r without l throws ArgumentError (src/Node.jl:353). Before, Node{Float64}(; r=x) returned an uninitialised node without an error." },
  { id := "nodebase-set-child"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_child!", "get_child"]
    statement := "set_child!(n, c, i) with 1 <= i <= D returns c, makes get_child(n, i) === c, and leaves all other slots, all other fields of n, and all other objects unchanged."
    preconditions := "n has a defined children tuple of length D."
    status := .proven
    prop := ``set_child
    thm := some ``set_child_holds },
  { id := "nodebase-set-children"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_children!", "get_children", "get_child"]
    statement := "set_children!(n, cs) with length(cs) <= D makes get_children(n, length(cs)) == cs (the same objects), poisons the remaining slots (UndefRefError), and changes nothing else."
    preconditions := "length(cs) <= D."
    status := .proven
    prop := ``set_children
    thm := some ``set_children_holds },
  { id := "nodebase-set-children-total"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_children!", "get_children"]
    statement := "set_children!(n, cs) either throws or stores cs: get_children(n, length(cs)) returns cs, so no child is silently dropped."
    preconditions := "n is an existing node."
    status := .proven
    prop := ``set_children_total
    thm := some ``set_children_total_holds
    notes := "Fixed by PR #236: more than D children throw ArgumentError (src/Node.jl:239-240). Before, the ntuple(..., Val(D)) branch silently dropped the extra children (QUESTIONS.md Q22)." },
  { id := "nodebase-set-node"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_node!"]
    statement := "set_node!(t, s) succeeds and copies exactly the active fields (QUESTIONS.md Q23: inactive fields are undefined): t unfolds to the same expression as s, gives t exactly the same active child objects as s (shallow: children become shared), sets t.constant to s.constant when s is a leaf (else leaves it), and leaves every other object unchanged."
    preconditions := "s well formed (constant leaves have a value, branches a full children tuple of length D); t not reachable from s."
    status := .proven
    prop := ``set_node
    thm := some ``set_node_holds },
  { id := "nodebase-tree-mapreduce-fold"
    juliaFile := "src/base.jl"
    juliaFns := ["tree_mapreduce"]
    statement := "On plain Node trees, tree_mapreduce(f_leaf, f_branch, op, tree) equals the simple recursive fold op(f_branch(node), map(fold, children)...) with f_leaf at leaves."
    preconditions := "Every branch has at most D children."
    status := .proven
    prop := ``tree_mapreduce_fold
    thm := some ``tree_mapreduce_fold_holds },
  { id := "nodebase-count-nodes-tree"
    juliaFile := "src/base.jl"
    juliaFns := ["count_nodes", "tree_mapreduce"]
    statement := "count_nodes and length on a plain Node equal the number of nodes of the tree."
    preconditions := "Every branch has at most D children."
    status := .proven
    prop := ``count_nodes_tree
    thm := some ``count_nodes_tree_holds },
  { id := "nodebase-traversal-tree"
    juliaFile := "src/base.jl"
    juliaFns := ["filter_map", "filter_map!", "tree_mapreduce"]
    statement := "filter_map! writes map_fnc of exactly the nodes satisfying filter_fnc, in depth-first pre-order, into the first slots of the destination and leaves the rest unchanged; filter_map returns exactly these values; collect returns the nodes in pre-order; count, sum and any agree with the same operations on the pre-order node list."
    preconditions := "Every branch has at most D children; for filter_map!, the destination holds at least the number of matches."
    status := .proven
    prop := ``traversal_tree
    thm := some ``traversal_tree_holds },
  { id := "nodebase-eq-tree"
    juliaFile := "src/base.jl"
    juliaFns := ["Node"]
    statement := "== on plain Node trees is structural equality, hence an equivalence, when the element == is equality."
    preconditions := "Element == coincides with equality (no NaN-like values); representable trees with degrees <= D."
    status := .proven
    prop := ``eq_tree
    thm := some ``eq_tree_holds },
  { id := "nodebase-hash-eq"
    juliaFile := "src/base.jl"
    juliaFns := ["Node"]
    statement := "Well-formed Node trees whose constants agree under isequal have equal hashes, for every element hash consistent with isequal (Julia's hash contract), with Float64 elements."
    preconditions := "Element hash consistent with isequal; representable trees with degrees <= D."
    status := .proven
    prop := ``hash_eq
    thm := some ``hash_eq_holds
    notes := "Q32: ==-equal trees with 0.0 and -0.0 constants hash differently, exactly as Julia's own floats do (0.0 == -0.0, hash(0.0) != hash(-0.0)); not a bug." },
  { id := "nodebase-hash-eq-lawful"
    juliaFile := "src/base.jl"
    juliaFns := ["Node"]
    statement := "With an element == that is equality, ==-equal Node trees have equal hashes."
    preconditions := "Element == coincides with equality; representable trees with degrees <= D."
    status := .proven
    prop := ``hash_eq_lawful
    thm := some ``hash_eq_lawful_holds },
  { id := "nodebase-eq-no-throw"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "AbstractExpressionNode"]
    statement := "== between any two nodes returns a Bool rather than throwing."
    preconditions := "Maximum degrees >= 1; each tree's node degrees are at most its maximum degree."
    status := .proven
    prop := ``eq_no_throw
    thm := some ``eq_no_throw_holds
    notes := "Fixed by PR #238: the promote rules cover every pair of maximum degrees and promote to the larger one (src/Node.jl:471-483), and raising the degree in convert always succeeds (src/base.jl:541-543). Before, Node{Float64,2}(feature=1) == Node{Float64,3}(feature=1) threw (QUESTIONS.md Q25)." },
  { id := "nodebase-convert-degree"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "convert between node types with different maximum degrees succeeds exactly when the types are equal, the target degree is at least the source degree, or every node of the tree fits the target degree; otherwise it throws ArgumentError (Miles's rule for PR #238)."
    preconditions := "None."
    status := .proven
    prop := ``convert_degree
    thm := some ``convert_degree_holds
    notes := "Mirrors src/base.jl:535-553 as fixed by PR #238." },
  { id := "nodebase-convert-unparam"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "convert(Node, tree) (and Node(tree)) on a node already of type Node{T,D} succeeds and keeps the type Node{T,D}."
    preconditions := "D >= 1; node degrees <= D."
    status := .proven
    prop := ``convert_unparam
    thm := some ``convert_unparam_holds
    notes := "Fixed by PR #239: the third convert method keeps the source's maximum degree when the target has none (src/base.jl:559-564). Before, it used max_degree(Node) = 2 and threw for D = 3." },
  { id := "nodebase-copy-type"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node"]
    statement := "copy_node on a well-formed plain Node returns a tree of the same type as its input."
    preconditions := "Representable tree with degrees <= D; constants' runtime types are allowed by the declared element type."
    status := .proven
    prop := ``copy_type
    thm := some ``copy_type_holds
    notes := "Fixed by PR #243: leaf_copy passes T explicitly, constructorof(N)(T; val=copy_value(t.val::T)) (src/base.jl:503). Before, copy_node(Node{Real}(val=1.0)) was a Node{Float64} (QUESTIONS.md Q24)." },
  { id := "nodebase-iterate-length"
    juliaFile := "src/base.jl"
    juliaFns := ["GraphNode", "count_nodes"]
    statement := "On every finite well-formed tree, iteration and length both succeed and iteration yields exactly length(tree) elements, as the declared Base.HasLength trait requires."
    preconditions := "Finite well-formed tree (unfold succeeds; Tree.WF with D, op <= 255, features <= 65535)."
    status := .proven
    prop := ``iterate_length
    thm := some ``iterate_length_holds
    notes := "Fixed by PR #240: iterate uses collect(root) with the default break_sharing (src/base.jl:451-453), matching length (src/base.jl:457-459). Before, GraphNode x1 + {x1} had length 2 but iterated 3 nodes." },
  { id := "nodebase-graph-eq-sound"
    juliaFile := "src/base.jl"
    juliaFns := ["GraphNode"]
    statement := "On finite well-formed GraphNode trees, == returns a Bool, and true only when the two trees unfold to the same expression."
    preconditions := "Element == is equality; finite well-formed trees (unfold succeeds; Tree.WF)."
    status := .proven
    prop := ``graph_eq_sound
    thm := some ``graph_eq_sound_holds
    notes := "Fixed by PR #241: the identity maps record each object's partner and a revisited pair is equal only when the objects were matched to each other (src/base.jl:198,210-216,239-242). Before, x1*x2 + {x1} == x1*x2 + {x2} was true." },
  { id := "nodebase-convert-to-node-noalias"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode", "tree_mapreduce"]
    statement := "Converting a finite well-formed GraphNode tree to a plain Node type succeeds and yields an alias-free plain Node tree."
    preconditions := "Finite well-formed source (unfold succeeds; Tree.WF)."
    status := .proven
    prop := ``convert_to_node_noalias
    thm := some ``convert_to_node_noalias_holds
    notes := "Fixed by PR #242: convert passes break_sharing=Val(!preserve_sharing(N1)) (src/base.jl:550), so converting to Node copies shared subtrees separately. Before, convert(Node{Float64,2}, x1 + {x1}) stored one Node object twice." },
  { id := "nodebase-convert-same-type-identity"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "Exposure: convert(N, tree) and N(tree) return the argument object itself, and allocate nothing, when tree already has type N."
    preconditions := "None."
    status := .proven
    prop := ``convert_same_type_identity
    thm := some ``convert_same_type_identity_holds },
  { id := "nodebase-copy-value-fresh"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node", "copy_into!"]
    statement := "copy_node shares no mutable object with its source: it succeeds, every node reachable from the copy is newly allocated, and no constant value object of the copy is a value object of the source."
    preconditions := "Finite well-formed source; element values modelled as object identities of live objects (mutable values such as Vector{Float64} constants under GenericOperatorEnum, whose copy_value is deepcopy)."
    status := .proven
    prop := ``copy_value_fresh
    thm := some ``copy_value_fresh_holds
    notes := "Fixed by PR #243: leaf_copy stores copy_value(t.val) (src/base.jl:503, src/ValueInterface.jl:82), a deepcopy for non-isbits values; leaf_copy_into! does the same (src/NodePreallocation.jl:55), which the NodeUtils copy_into! mirror carries only for by-value constants. Allocating convert still stores convert(T1, t.val), the same object for equal element types (src/base.jl:568-576); no property covers that path. Before, copy_node(Node{Vector{Float64}}) shared the value object." },
  { id := "nodebase-count-nodes-graph"
    juliaFile := "src/base.jl"
    juliaFns := ["count_nodes", "tree_mapreduce", "GraphNode"]
    statement := "count_nodes on the heap: with break_sharing=Val(true), or on plain Node, it equals the number of unfolded occurrences; on GraphNode by default it equals the number of distinct objects reachable from the root (the identity map and f_on_shared count each object once)."
    preconditions := "Finite well-formed tree (unfold succeeds) with degrees <= D."
    status := .proven
    prop := ``count_nodes_graph
    thm := some ``count_nodes_graph_holds },
  { id := "nodebase-graph-eq-refl"
    juliaFile := "src/base.jl"
    juliaFns := ["GraphNode"]
    statement := "== on GraphNode is reflexive (a == a) on well-formed trees."
    preconditions := "Element == reflexive (no NaN constants); finite well-formed tree with degrees <= D."
    status := .proven
    prop := ``graph_eq_refl
    thm := some ``graph_eq_refl_holds },
  { id := "nodebase-copy-node-heap"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node", "tree_mapreduce", "GraphNode", "Node"]
    statement := "copy_node succeeds, leaves every existing object unchanged, returns a tree that unfolds to the same expression and consists only of freshly allocated objects (no node shared with the source); without the identity map (plain Node or break_sharing=Val(true)) the copy is alias-free; with it (GraphNode default) the copy has exactly the source's sharing shape (a bijection between reachable objects that maps root to root and children lists to children lists)."
    preconditions := "Finite well-formed tree (unfold succeeds, Tree.WF with D, op <= 255, features in 1..65535)."
    status := .proven
    prop := ``copy_node_heap
    thm := some ``copy_node_heap_holds },
  { id := "nodebase-ctor-children-degree-default"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node"]
    statement := "Companion of nodebase-ctor-children-degree (implied by it since PR #234): Node(; op, children) with 1..2 children of one concrete type Node{T,2} returns a Node{T,2}."
    preconditions := "Children of the default maximum degree 2."
    status := .proven
    prop := ``ctor_children_degree_default
    thm := some ``ctor_children_degree_default_holds },
  { id := "nodebase-convert-unparam-default"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "Companion of nodebase-convert-unparam (implied by it since PR #239): convert(Node, tree) on a tree of the default degree 2 succeeds and keeps its type."
    preconditions := "Tree of maximum degree 2; node degrees <= 2."
    status := .proven
    prop := ``convert_unparam_default
    thm := some ``convert_unparam_default_holds },
  { id := "nodebase-eq-no-throw-same-degree"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "Companion of nodebase-eq-no-throw (implied by it since PR #238): == between nodes of the same maximum degree never throws."
    preconditions := "Equal maximum degrees; node degrees within them."
    status := .proven
    prop := ``eq_no_throw_same_degree
    thm := some ``eq_no_throw_same_degree_holds },
  { id := "nodebase-copy-type-concrete"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node"]
    statement := "Companion of nodebase-copy-type (implied by it since PR #243): with a concrete element type, copy_node keeps the tree's type."
    preconditions := "As nodebase-copy-type, plus: the element type is concrete (not Real)."
    status := .proven
    prop := ``copy_type_concrete
    thm := some ``copy_type_concrete_holds },
  { id := "nodebase-hash-eq-no-negzero"
    juliaFile := "src/base.jl"
    juliaFns := ["Node"]
    statement := "Well-formed Float64 Node trees without -0.0 constants that compare == have equal hashes."
    preconditions := "Element hash consistent with isequal; representable trees with degrees <= D; no constant is -0.0."
    status := .proven
    prop := ``hash_eq_no_negzero
    thm := some ``hash_eq_no_negzero_holds },
  { id := "nodebase-set-children-total-le"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_children!", "get_children"]
    statement := "Companion of nodebase-set-children-total (implied by it since PR #236): with at most D children, set_children! stores every child."
    preconditions := "As nodebase-set-children-total, plus: length(cs) <= D."
    status := .proven
    prop := ``set_children_total_le
    thm := some ``set_children_total_le_holds },
  { id := "nodebase-ctor-child-arg-with-l"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "Companion of nodebase-ctor-child-arg (implied by it since PR #235): when r is only passed together with l, every child argument is stored in order (or the call throws)."
    preconditions := "r given only together with l."
    status := .proven
    prop := ``ctor_child_arg_with_l
    thm := some ``ctor_child_arg_with_l_holds },
  { id := "nodebase-copy-value-fresh-immutable"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node"]
    statement := "Companion of nodebase-copy-value-fresh: when constant values are immutable (isbits-like) scalars, copy_node succeeds on every finite well-formed tree, all nodes of the copy are fresh, the copy equals the source, and mutating any node of the copy (including its value) leaves the source unchanged."
    preconditions := "As nodebase-copy-value-fresh, but constant values are immutable scalars carried by value (copy_value is the identity on isbits values)."
    status := .proven
    prop := ``copy_value_fresh_immutable
    thm := some ``copy_value_fresh_immutable_holds },
  { id := "nodebase-iterate-length-noalias"
    juliaFile := "src/base.jl"
    juliaFns := ["GraphNode", "count_nodes"]
    statement := "Companion of nodebase-iterate-length (implied by it since PR #240): on alias-free trees, iteration and length both succeed and iteration yields exactly length(tree) elements."
    preconditions := "As nodebase-iterate-length, plus: no object reachable along two child paths (Graph.NoAlias)."
    status := .proven
    prop := ``iterate_length_noalias
    thm := some ``iterate_length_noalias_holds },
  { id := "nodebase-graph-eq-noalias"
    juliaFile := "src/base.jl"
    juliaFns := ["GraphNode"]
    statement := "Companion of nodebase-graph-eq-sound: on alias-free operands, GraphNode == returns a Bool that is true exactly when the trees are equal."
    preconditions := "As nodebase-graph-eq-sound, plus: both operands alias-free (Graph.NoAlias)."
    status := .proven
    prop := ``graph_eq_noalias
    thm := some ``graph_eq_noalias_holds },
  { id := "nodebase-convert-to-node-noalias-src"
    juliaFile := "src/base.jl"
    juliaFns := ["Node", "GraphNode"]
    statement := "Companion of nodebase-convert-to-node-noalias (implied by it since PR #242): converting an alias-free GraphNode tree to Node succeeds and yields an alias-free tree."
    preconditions := "As nodebase-convert-to-node-noalias, plus: the source is alias-free (Graph.NoAlias)."
    status := .proven
    prop := ``convert_to_node_noalias_src
    thm := some ``convert_to_node_noalias_src_holds }
]

end DynExpr.NodeBase
