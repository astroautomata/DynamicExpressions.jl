using DynamicExpressions

ops = OperatorEnum(2 => (+,); define_helper_functions=false)
P = reshape([10.0, 20.0], 1, 2)
vn = ["x1"]
pn = ["p1"]
p = ParametricNode(; val=0.0)
p.constant = false
p.is_parameter = true
p.parameter = 1
f = ParametricNode{Float64}(; feature=1)
tree = ParametricNode(; op=1, children=(p, f))
ex = ParametricExpression(
    tree; operators=ops, parameters=P, variable_names=vn, parameter_names=pn
)
@assert get_contents(ex) === tree
@assert get_tree(ex) === tree
@assert get_metadata(ex).parameters === P
@assert get_metadata(ex).variable_names === vn
@assert get_metadata(ex).parameter_names === pn
values, refs = get_scalar_constants(ex)
@assert refs.parameter_refs === P
@assert !Base.mightalias(values, P)
values[1] = -1.0
@assert P[1] == 10.0
refs.parameter_refs[1] = 11.0
@assert get_scalar_constants(ex)[1][1] == 11.0

constex = ParametricExpression(ParametricNode(; val=7.0); operators=ops, parameters=P)
cv, cr = get_scalar_constants(constex)
cv[1] = -1.0
@assert get_tree(constex).val == 7.0
cr.constant_refs[1][].val = 8.0
@assert get_tree(constex).val == 8.0

changed_contents = with_contents(ex, ParametricNode{Float64}(; feature=1))
@assert get_metadata(changed_contents) === get_metadata(ex)
changed_metadata = with_metadata(ex; parameter_names=["new-name"])
@assert get_contents(changed_metadata) === get_contents(ex)
@assert get_metadata(changed_metadata).parameters === P

copied = copy(ex)
@assert !Base.mightalias(get_metadata(copied).parameters, P)
@assert get_metadata(copied).variable_names !== vn
@assert get_metadata(copied).parameter_names !== pn
source_nodes = collect(get_tree(ex))
copied_nodes = collect(get_tree(copied))
@assert all(a -> all(b -> a !== b, source_nodes), copied_nodes)
@assert length(Set(objectid.(copied_nodes))) == length(copied_nodes)
get_metadata(copied).parameters[1] = 99.0
get_metadata(copied).variable_names[1] = "different"
@assert P[1] == 11.0 && vn == ["x1"]

converted = convert(Node, ex)
@assert all(a -> all(b -> a !== b, source_nodes), collect(converted))
@assert length(Set(objectid.(collect(converted)))) == length(collect(converted))
parsed_node = DynamicExpressions.ParametricExpressionModule.parse_leaf(
    p, nothing, ParametricNode, ParametricExpression; parameter_names=["p1"]
)
@assert parsed_node === p

same_names = ["shared"]
e_names = ParametricExpression(
    ParametricNode{Float64}(; feature=1);
    operators=ops,
    parameters=P,
    variable_names=same_names,
    parameter_names=same_names,
)
c_names = copy(e_names)
@assert get_metadata(c_names).variable_names !== get_metadata(c_names).parameter_names
@assert get_metadata(c_names).variable_names !== same_names
@assert get_metadata(c_names).parameter_names !== same_names

other = ParametricExpression(
    ParametricNode{Float64}(; feature=1);
    operators=ops,
    parameters=P,
    variable_names=vn,
    parameter_names=pn,
)
structure = nt -> nt.a
structured = StructuredExpression((a=ex, b=other); structure, variable_names=vn)
@assert get_contents(structured).a === ex
@assert get_tree(structured) === get_tree(ex)
@assert get_metadata(structured).structure === structure
sv, sr = get_scalar_constants(structured)
@assert !Base.mightalias(sv, P)
sv[1] = -1.0
@assert P[1] == 11.0
scopy = copy(structured)
@assert get_metadata(scopy).structure === structure
ca, cb = get_contents(scopy).a, get_contents(scopy).b
@assert !Base.mightalias(get_metadata(ca).parameters, get_metadata(cb).parameters)
@assert !Base.mightalias(get_metadata(ca).parameters, P)
@assert !Base.mightalias(get_metadata(cb).parameters, P)
@assert get_metadata(scopy).variable_names !== vn
@assert get_metadata(ca).variable_names !== get_metadata(cb).variable_names
get_metadata(ca).parameters[1] = 123.0
@assert get_metadata(cb).parameters[1] == 11.0 && P[1] == 11.0

container = DynamicExpressions.allocate_container(ex)
first_result = DynamicExpressions.copy_into!(container, ex)
@assert get_metadata(first_result).parameters === container.parameters
@assert !Base.mightalias(container.parameters, P)
@assert all(a -> all(b -> a !== b, source_nodes), collect(get_tree(first_result)))
next_source = copy(ex)
get_metadata(next_source).parameters .= [31.0 41.0]
second_result = DynamicExpressions.copy_into!(container, next_source)
@assert get_metadata(second_result).parameters === get_metadata(first_result).parameters
@assert get_scalar_constants(first_result)[1] == [31.0, 41.0]
@assert P == [11.0 20.0]

X = [1.0 2.0]
P_before, X_before = copy(P), copy(X)
output, complete = eval_tree_array(ex, X, [2, 1])
@assert complete
@assert !Base.mightalias(output, X)
@assert !Base.mightalias(output, P)
output[1] = -999.0
@assert P == P_before && X == X_before
println("PARAMSTRUCT ALIAS CHECKS PASSED")
