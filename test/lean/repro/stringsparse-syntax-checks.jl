using DynamicExpressions
twice(x) = x + x
ops = OperatorEnum(1 => (-, twice), 2 => (+, -, *, ^); define_helper_functions=false)
for value in (1.0, -1.5, 1.0e-20, 1.0e20, 1.0 + 2.0im)
    text = string_tree(Node(; val=value), ops)
    parsed = parse_expression(text; operators=ops, variable_names=["x1", "x2"])
    @assert get_tree(parsed).degree == 0
    @assert isequal(get_tree(parsed).val, value)
end
suffix = parse_expression("1.25f0"; operators=ops, variable_names=["x1"])
@assert get_tree(suffix).val isa Float32
@assert get_tree(suffix).val == 1.25f0
display32 = parse_expression(string_tree(Node(; val=1.25f0), ops); operators=ops)
@assert get_tree(display32).val == 1.25f0

left = Node(; op=1, children=(Node(; feature=1), Node(; val=2.0)))
right = Node(; op=2, children=(Node(; feature=2), Node(; val=3.0)))
tree = Node(; op=3, children=(left, right))
text = string_tree(tree, ops; variable_names=["x1", "x2"])
@assert text == "(x1 + 2.0) * (x2 - 3.0)"
parsed = parse_expression(text; operators=ops, variable_names=["x1", "x2"])
@assert get_tree(parsed) == tree
X = [1.0 2.0; 4.0 5.0]
@assert parsed(X) == tree(X, ops)
prefix = Node(; op=2, children=(tree,))
parsed_prefix = parse_expression(
    string_tree(prefix, ops; variable_names=["x1", "x2"]);
    operators=ops,
    variable_names=["x1", "x2"],
)
@assert get_tree(parsed_prefix) == prefix

shared = GraphNode(; feature=1)
graph = GraphNode(; op=1, children=(shared, shared))
@assert string_tree(graph, ops; variable_names=["x1"]) == "x1 + {x1}"
shared_branch = GraphNode(; op=3, children=(GraphNode(; feature=1), GraphNode(; feature=2)))
shared_root = GraphNode(; op=1, children=(shared_branch, shared_branch))
@assert string_tree(shared_root, ops; variable_names=["x1", "x2"]) ==
    "(x1 * x2) + {(x1 * x2)}"

macro_parsed = @parse_expression(x1 + x2, operators = ops, variable_names = ["x1", "x2"])
@assert get_tree(macro_parsed).degree == 2
@assert macro_parsed(X) == [5.0, 7.0]
@assert string_tree(Node(; feature=1), ops; varMap=["alpha"]) == "alpha"
ordinary = Node(; feature=1)
converted_branch = parse_expression(
    Expr(:call, +, ordinary, 2.0); operators=ops, variable_names=["x1"], node_type=GraphNode
)
@assert get_tree(converted_branch) isa GraphNode
@assert get_child(get_tree(converted_branch), 1) isa GraphNode
converted_external = parse_expression(
    Expr(:call, identity, ordinary);
    operators=ops,
    variable_names=["x1"],
    node_type=GraphNode,
    evaluate_on=[identity],
)
@assert get_tree(converted_external) isa GraphNode
@assert get_tree(converted_external) !== ordinary

ternary_ops = OperatorEnum(3 => (+,); define_helper_functions=false)
ternary = parse_expression(
    "x1 + x2 + x3";
    operators=ternary_ops,
    variable_names=["x1", "x2", "x3"],
    node_type=Node{Float64,3},
)
@assert get_tree(ternary).degree == 3
@assert get_tree(ternary).op == 1
@assert [get_child(get_tree(ternary), i).feature for i in 1:3] == [1, 2, 3]

println(
    "VERIFIED StringsParse finite, complex, prefix, infix, sharing, macro, and legacy syntax",
)
