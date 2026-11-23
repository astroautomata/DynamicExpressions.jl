using DynamicExpressions
ops = GenericOperatorEnum(2 => (+,); define_helper_functions=false)
node = Node(; feature=1)
parsed_node = parse_expression(node; operators=ops, variable_names=["x1", "x2"])
@assert get_tree(parsed_node) === node
node.feature = 2
@assert get_tree(parsed_node).feature == 2

array = [1.0, 2.0]
parsed_array = parse_expression(array; operators=ops, variable_names=["x1"])
@assert get_tree(parsed_array).val === array
@assert Base.mightalias(get_tree(parsed_array).val, array)
array[1] = 9.0
@assert get_tree(parsed_array).val[1] == 9.0

module StringsParseObjectModule
const data = [3.0, 4.0]
getdata() = data
end
for surface in (:data, :(getdata()))
    parsed = parse_expression(
        surface; operators=ops, variable_names=["x1"], eval_module=StringsParseObjectModule
    )
    @assert get_tree(parsed).val === StringsParseObjectModule.data
    @assert Base.mightalias(get_tree(parsed).val, StringsParseObjectModule.data)
end
StringsParseObjectModule.data[2] = 8.0
parsed_global = parse_expression(
    :data; operators=ops, variable_names=["x1"], eval_module=StringsParseObjectModule
)
@assert get_tree(parsed_global).val[2] == 8.0

external_node = parse_expression(
    Expr(:call, identity, node);
    operators=ops,
    variable_names=["x1", "x2"],
    evaluate_on=[identity],
)
@assert get_tree(external_node) === node

names = ["alpha", "beta"]
names_snapshot = copy(names)
text = string_tree(node, ops; variable_names=names)
@assert names == names_snapshot
@assert text == "beta"
@assert node.feature == 2
io = IOBuffer()
write(io, "prefix:")
io_identity = io
@assert print_tree(io, node, ops; variable_names=names) === nothing
@assert io === io_identity
@assert String(take!(io)) == "prefix:" * text * "\n"
@assert names == names_snapshot

surface = Expr(:call, +, :alpha, :beta)
args_identity = surface.args
surface_snapshot = deepcopy(surface)
parse_expression(surface; operators=ops, variable_names=names)
@assert surface.args === args_identity
@assert surface == surface_snapshot
@assert names == names_snapshot
println(
    "VERIFIED StringsParse node, array, module, external, syntax, and rendering ownership"
)
