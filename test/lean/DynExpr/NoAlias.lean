import DynExpr.Registry.Types
import DynExpr.NoAlias.Core
import DynExpr.NoAlias.Ctor
import DynExpr.NoAlias.Build
import DynExpr.NoAlias.Mutate
import DynExpr.NoAlias.Operators
import DynExpr.NoAlias.Copy
import DynExpr.NoAlias.CopyInto
import DynExpr.NoAlias.Combine
import DynExpr.NoAlias.Parse
import DynExpr.NoAlias.Precompile

/-! Slice root: imports this slice's files and lists its registry entries.

Q6 (QUESTIONS.md): plain `Node` trees must never contain aliased nodes. Each
property states, on the heap model, that a package operation applied to
alias-free inputs that share no object returns (or leaves) an alias-free tree,
or refutes that for repeated operands. "Alias-free" is `Graph.NoAlias`: every
reachable object has exactly one child path from the root. -/

namespace DynExpr.NoAlias

open DynExpr.Registry in
def entries : List DynExpr.Registry.Entry := [
  { id := "noalias-node-ctor"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node"]
    statement := "Every valid form of N(; val, feature, op, l, r, children) succeeds and returns an alias-free tree whose objects are one new node plus the passed child trees, and changes no existing object, when the passed children are alias-free, distinct and share no object."
    preconditions := "A valid keyword combination (only val; only feature <= 65535; or op <= 255 with l/r or children, at most D children); children are alias-free closed trees, pairwise distinct and disjoint."
    status := .proven
    prop := ``node_ctor_noalias
    thm := some ``node_ctor_noalias_holds },
  { id := "noalias-node-ctor-repeated-child"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node", "@extend_operators", "parse_expression", "parse_leaf", "@declare_expression_operator", "test_functions_on_trees"]
    statement := "Passing the same alias-free tree x twice to the constructor Node(; op, children=(x, x)) / Node(op, x, x) succeeds and stores the caller's object in both child slots of one new node, keeps x alias-free, and changes no existing object. The other listed entry points (generated operators x * x, parse_expression(:($x + $x)), ex + ex, the precompile workload) build such nodes through this constructor."
    preconditions := "op <= 255; D >= 2; x is an alias-free closed tree."
    status := .proven
    prop := ``node_ctor_repeated_child
    thm := some ``node_ctor_repeated_child_holds
    notes := "Restated per Miles's ruling (QUESTIONS.md Q35): aliasing that the caller creates by passing one object twice is accepted; the package only must not create aliasing from disjoint inputs (noalias-node-ctor, noalias-operator-methods, noalias-parse-expression, noalias-expression-operator). The former refutation showed Node(op, x, x) stores x twice (src/Node.jl:407-430, 235-254)." },
  { id := "noalias-promoted-ctor"
    juliaFile := "src/Node.jl"
    juliaFns := ["Node", "set_children!"]
    statement := "The typed constructor N{T}(; op, children) whose differently typed children are converted when stored succeeds and returns an alias-free tree: kept children must be alias-free, distinct and disjoint, converted children are fresh copies (so Node{Float64}(; op, children=(x32, x32)) is alias-free)."
    preconditions := "At most D children; op <= 255; kept children alias-free closed and pairwise disjoint; converted children unfold to well-formed finite trees."
    status := .proven
    prop := ``promoted_ctor_noalias
    thm := some ``promoted_ctor_noalias_holds },
  { id := "noalias-set-child"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_child!"]
    statement := "set_child!(n, child, i) succeeds and keeps every enclosing alias-free tree alias-free when child is an alias-free tree sharing no object with it, or is the object already stored in slot i."
    preconditions := "n exists with a full D-slot children tuple, 1 <= i <= D; enclosing tree alias-free and reaches n; child alias-free and either disjoint from the enclosing tree or the current slot-i child."
    status := .proven
    prop := ``set_child_noalias
    thm := some ``set_child_noalias_holds },
  { id := "noalias-set-children"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_children!"]
    statement := "set_children!(n, cs) succeeds and keeps every enclosing alias-free tree alias-free when the new children are distinct, alias-free, pairwise disjoint trees, each sharing no object with the enclosing tree or being a current child of n (writing back or reordering the current children)."
    preconditions := "n exists; at most D children; enclosing tree alias-free and reaches n; new children alias-free and pairwise disjoint, each disjoint from the enclosing tree or a current child of n."
    status := .proven
    prop := ``set_children_noalias
    thm := some ``set_children_noalias_holds },
  { id := "noalias-set-node"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_node!"]
    statement := "set_node!(t, s) succeeds and keeps every enclosing alias-free tree alias-free when s is alias-free, does not reach t, and meets the enclosing tree only inside the subtree of t (e.g. s disjoint, or s a descendant of t)."
    preconditions := "t and s exist; a constant-leaf s holds a value, a branch s has a full D-slot children tuple; enclosing tree and s alias-free; t not reachable from s; s meets the enclosing tree only below t."
    status := .proven
    prop := ``set_node_noalias
    thm := some ``set_node_noalias_holds },
  { id := "noalias-set-node-shares"
    juliaFile := "src/Node.jl"
    juliaFns := ["set_node!"]
    statement := "Exposure: set_node!(t, s) with a branch s succeeds and makes t hold the very child objects of s (documented shallow field copy), so afterwards t's and s's trees share those children."
    preconditions := "t exists; s is a branch with a full D-slot children tuple; t differs from s."
    status := .proven
    prop := ``set_node_shares_children
    thm := some ``set_node_shares_children_holds },
  { id := "noalias-copy-node"
    juliaFile := "src/base.jl"
    juliaFns := ["copy_node", "copy"]
    statement := "copy_node(tree) / copy(tree) on a plain Node returns an alias-free tree made only of new objects (sharing nothing with the source), for every finite well-formed source, even an aliased one; existing objects are unchanged."
    preconditions := "The source unfolds to a well-formed finite tree (degree <= D, op <= 255, feature <= 65535)."
    status := .proven
    prop := ``copy_node_noalias
    thm := some ``copy_node_noalias_holds },
  { id := "noalias-convert"
    juliaFile := "src/base.jl"
    juliaFns := ["convert"]
    statement := "convert(Node{T1}, tree::Node{T2}) to a different node type returns an alias-free tree of new objects; to the same type it returns the argument itself."
    preconditions := "The source unfolds to a well-formed finite tree."
    status := .proven
    prop := ``convert_node_noalias
    thm := some ``convert_node_noalias_holds },
  { id := "noalias-copy-into"
    juliaFile := "src/NodePreallocation.jl"
    juliaFns := ["copy_into!", "allocate_container"]
    statement := "copy_into!(dest, src) on a plain Node succeeds, consumes size(t) slots, and returns an alias-free tree that lives only in the consumed destination slots, changing no other object."
    preconditions := "Distinct destination slots that all exist; every reachable source node stores exactly degree children; the source unfolds within the fuel to a tree t with size(t) <= number of slots (aliased sources allowed)."
    status := .proven
    prop := ``copy_into_noalias
    thm := some ``copy_into_noalias_holds },
  { id := "noalias-operator-methods"
    juliaFile := "src/OperatorEnumConstruction.jl"
    juliaFns := ["@extend_operators", "OperatorEnum"]
    statement := "Every generated Node operator method (unary, binary, node-scalar, scalar-node, n-ary incl. chained fallback and all-constant folding) succeeds and returns an alias-free tree made of new objects and its operands' objects, changing no existing object, when the operands it keeps are alias-free, distinct and disjoint (all-constant calls fold, so c * c needs no disjointness)."
    preconditions := "Operator index <= 255; arity fits D (n-ary: args.length <= D, or D >= 2 and binary index <= 255 for the chained fallback); node operands are alias-free closed trees; operands are pairwise distinct and disjoint unless all of them are constant leaves; a constant-leaf operand holds a value."
    status := .proven
    prop := ``operator_methods_noalias
    thm := some ``operator_methods_noalias_holds },
  { id := "noalias-operator-stores-operands"
    juliaFile := "src/OperatorEnumConstruction.jl"
    juliaFns := ["@extend_operators"]
    statement := "Exposure: a generated binary method applied to a non-constant left operand succeeds and returns a new node whose children are the operand objects themselves (no copy), so the result shares its subtrees with the operands."
    preconditions := "Operator index <= 255; D >= 2; the left operand exists and is not a constant leaf."
    status := .proven
    prop := ``operator_stores_operands
    thm := some ``operator_stores_operands_holds },
  { id := "noalias-promote-binary"
    juliaFile := "src/OperatorEnumConstruction.jl"
    juliaFns := ["@extend_operators"]
    statement := "The mixed-type operator converter f(l::Node{T1}, r::Node{T2}) succeeds and returns an alias-free tree: converted operands are fresh copies, kept operands must be alias-free, distinct and disjoint."
    preconditions := "Operator index <= 255; D >= 2; both operands unfold within the fuel to well-formed finite trees; kept (unconverted) operands are alias-free closed and disjoint."
    status := .proven
    prop := ``promote_binary_noalias
    thm := some ``promote_binary_noalias_holds },
  { id := "noalias-simplify-tree"
    juliaFile := "src/Simplify.jl"
    juliaFns := ["simplify_tree!"]
    statement := "simplify_tree! succeeds, returns the same root, and keeps an alias-free tree alias-free using only objects of the input tree."
    preconditions := "The input unfolds within the fuel to a well-formed tree (degree <= D, operator indices within the enum, features in 1..nf) and is alias-free."
    status := .proven
    prop := ``simplify_tree_noalias
    thm := some ``simplify_tree_noalias_holds
    notes := "Success comes from the Simplify slice's simplify-tree-matches-spec." },
  { id := "noalias-combine-operators"
    juliaFile := "src/Simplify.jl"
    juliaFns := ["combine_operators!"]
    statement := "combine_operators! succeeds and returns an alias-free root that uses only objects of the input tree, changing nothing outside the input tree."
    preconditions := "Node{T,2} input that unfolds within the fuel to a well-formed binary tree and is alias-free."
    status := .proven
    prop := ``combine_operators_noalias
    thm := some ``combine_operators_noalias_holds
    notes := "Success comes from the Simplify slice's simplify-combine-matches-spec. combine_operators! (renamed from combine_operators by PR #251, src/Simplify.jl:29-126) mutates its input in place by design; when it returns a different root (tree = below, src/Simplify.jl:68,73) the caller must use the returned tree (simplify-combine-input-mutated)." },
  { id := "noalias-set-scalar-constants"
    juliaFile := "src/NodeUtils.jl"
    juliaFns := ["set_scalar_constants!"]
    statement := "set_scalar_constants! succeeds, writes only value fields, changes no child reference and keeps every alias-free tree alias-free."
    preconditions := "As many constants as refs; every ref names an existing node; the tree is alias-free."
    status := .proven
    prop := ``set_scalar_constants_noalias
    thm := some ``set_scalar_constants_noalias_holds },
  { id := "noalias-parse-expression"
    juliaFile := "src/Parse.jl"
    juliaFns := ["parse_expression", "@parse_expression", "parse_leaf"]
    statement := "parse_expression succeeds and returns an alias-free tree when the pre-built nodes embedded in the expression are alias-free, distinct and disjoint: each variable and literal gets a new leaf and each operator call (including chained +,-,*) a new branch."
    preconditions := "Valid expression (operator indices <= 255, call arity <= D, chained calls with >= 2 arguments and D >= 2, feature indices <= 65535); embedded pre-built nodes alias-free closed and pairwise disjoint; evaluate_on functions not used."
    status := .proven
    prop := ``parse_expression_noalias
    thm := some ``parse_expression_noalias_holds },
  { id := "noalias-expression-operator"
    juliaFile := "src/ExpressionAlgebra.jl"
    juliaFns := ["@declare_expression_operator"]
    statement := "The Expression operator methods succeed and build an alias-free tree when the argument expressions' trees are alias-free, distinct and disjoint; scalars become new leaves; the result contains the argument trees themselves (no copy)."
    preconditions := "The operator is found at the call's degree (index <= 255, arity <= D), or for a missing chainable + / * with more than two arguments it is found at degrees n-1 and 2; argument trees alias-free closed and pairwise disjoint."
    status := .proven
    prop := ``expression_operator_noalias
    thm := some ``expression_operator_noalias_holds },
  { id := "noalias-expression-operator-stores-trees"
    juliaFile := "src/ExpressionAlgebra.jl"
    juliaFns := ["@declare_expression_operator"]
    statement := "Exposure: an Expression operator applied to two expressions succeeds and returns a tree whose children are the operands' live trees (no copy), so the result shares nodes with both operands."
    preconditions := "The operator is found at degree 2 with index <= 255; D >= 2."
    status := .proven
    prop := ``expression_operator_stores_trees
    thm := some ``expression_operator_stores_trees_holds },
  { id := "noalias-precompile-workload-copy"
    juliaFile := "src/precompile.jl"
    juliaFns := ["test_functions_on_trees", "copy_node"]
    statement := "The precompile workload succeeds and builds the intended expression, and its consumer copy_node(tree) (src/precompile.jl:126) returns an alias-free tree with the same expression."
    preconditions := "1 <= number of unary operators <= 255; 1 <= number of binary operators <= 255."
    status := .proven
    prop := ``precompile_workload_copy_noalias
    thm := some ``precompile_workload_copy_noalias_holds
    notes := "The workload tree itself is aliased (a5 = Node(i_bin, x, x), src/precompile.jl:118; recorded under noalias-node-ctor-repeated-child); its only consumer copy_node removes the aliasing. convert(Node{T}, tree) at src/precompile.jl:125 returns the argument when T equals the loop's last T1." }
]

end DynExpr.NoAlias
