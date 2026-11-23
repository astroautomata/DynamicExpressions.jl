using DynamicExpressions
const U = DynamicExpressions.UtilsModule
input = [1.0, 2.0]
filled = U.fill_similar(3.0, input)
@assert filled !== input && !Base.mightalias(filled, input)
filled[1] = 7.0
@assert input == [1.0, 2.0]
payload = [1.0]
object_filled = U.fill_similar(payload, [[0.0], [0.0]])
@assert object_filled[1] === object_filled[2] === payload
object_filled[1][1] = 5.0
@assert payload == [5.0] && object_filled[2] == [5.0]
nullable = U.Nullable(false, input)
@assert nullable[] === input
@assert convert(U.Nullable{Vector{Float64}}, nullable)[] === input
result = U.ResultOk(input, true)
result2 = U.ResultOk2(input, input, true)
@assert result.x === input && result2.x === result2.dx === input
out = [0.0, 0.0]
U.set_invalid!(out)
@assert all(isnan, out) && input == [1.0, 2.0]
left = Node(; val=1.0)
right = Node(; val=2.0)
tree = Node(; op=1, children=(left, right))
values, refs = get_scalar_constants(tree)
values2, refs2 = get_scalar_constants(tree)
@assert refs[1] !== refs2[1] && refs[1][] === refs2[1][]
@assert !Base.mightalias(values, values2)
@assert refs[1][] === left && refs[2][] === right
values[1] = 7.0
@assert left.val == 1.0
supplied = [3.0, 4.0]
set_scalar_constants!(tree, supplied, refs)
supplied[1] = 8.0
@assert get_scalar_constants(tree)[1] == [3.0, 4.0]
@assert left !== right
storage = DynamicExpressions.allocate_container(tree)
@assert length(unique(objectid.(storage))) == length(storage)
@assert all(slot !== node for slot in storage for node in tree)
copied = DynamicExpressions.copy_into!(storage, tree)
@assert copied === storage[end]
@assert all(copy_node !== source_node for copy_node in copied for source_node in tree)
copied.l.val = 10.0
@assert tree.l.val == 3.0
indexed = index_constant_nodes(tree)
@assert all(index_node !== source_node for index_node in indexed for source_node in tree)
indexed.l.val = UInt16(12)
@assert tree.l.val == 3.0
shared = GraphNode(; val=1.0)
graph = GraphNode(; op=1, children=(shared, shared))
gstorage = DynamicExpressions.allocate_container(graph)
gcopy = DynamicExpressions.copy_into!(gstorage, graph)
@assert gcopy.l === gcopy.r && gcopy.l !== shared
mutable struct AssignedScalar <: Number
    value::Float64
end
assigned = AssignedScalar(2.0)
scalar_tree = Node{AssignedScalar}(; val=AssignedScalar(1.0))
_, scalar_refs = get_scalar_constants(scalar_tree)
scalar_input = [assigned]
set_scalar_constants!(scalar_tree, scalar_input, scalar_refs)
@assert scalar_tree.val === scalar_input[1]
assigned.value = 4.0
@assert scalar_tree.val.value == 4.0
println("CHECKED nodeutils-aliasing")
