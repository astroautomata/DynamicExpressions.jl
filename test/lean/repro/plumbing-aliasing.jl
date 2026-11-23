using DynamicExpressions
const DE = DynamicExpressions

# Numeric values are snapshots. Ref vectors and wrappers are freshly allocated,
# but each Ref deliberately borrows its source node.
a = Node(Float64; val=1.0)
b = Node(Float64; val=2.0)
t = Node(; op=1, children=(a, b))
values1, refs1 = DE.get_constants(t)
values2, refs2 = DE.get_constants(t)
@assert values1 !== values2 && !Base.mightalias(values1, values2)
@assert refs1 !== refs2 && !Base.mightalias(refs1, refs2)
@assert !Base.mightalias(values1, refs1)
@assert refs1[1] !== refs2[1] && refs1[1][] === a && refs2[1][] === a
values1[1] = 99.0
@assert a.val == 1.0 && DE.get_constants(t)[1] == [1.0, 2.0]
refs1[1][].val = 3.0
@assert a.val == 3.0 && DE.get_constants(t)[1] == [3.0, 2.0]
new_values = [4.0, 5.0]
new_values_before = copy(new_values)
@assert DE.set_constants!(t, new_values, refs1) === t
@assert new_values == new_values_before && refs1[1][] === a && refs1[2][] === b
@assert DE.get_constants(t)[1] == [4.0, 5.0]
refs1[1][] = Node(Float64; val=99.0)
@assert refs2[1][] === a && t.l === a && DE.get_constants(t)[1] == [4.0, 5.0]

# Indexed trees are fresh roots and fresh child objects, independent of nodes.
i1 = DE.index_constants(t)
i2 = DE.index_constants(t)
@assert i1 !== i2 && i1.l !== i2.l && i1.r !== i2.r
old_a = a.val
i1.l.val = 17
@assert i2.l.val == 1 && a.val == old_a

# Constructors retain live mutable values and live supplied children.
shared_value = [1.0, 2.0]
legacy_leaf = Node(1, true, shared_value)
@assert legacy_leaf.val === shared_value
shared_value[1] = 9.0
@assert legacy_leaf.val[1] == 9.0
for N in (Node, GraphNode)
    x = N(Float64; feature=1)
    c = N(Float64; val=2.0)
    unary_root = N(1, false, nothing, 0, 1, x)
    binary_root = N(2, false, nothing, 0, 1, x, c)
    @assert unary_root !== x && unary_root.l === x
    @assert binary_root !== x && binary_root !== c
    @assert binary_root.l === x && binary_root.r === c
end

# Both keyword enum flavours retain operator objects and their captured state.
state = Ref(0)
f = x -> (state[] += 1; x)
for E in (OperatorEnum, GenericOperatorEnum)
    enum = E(; unary_operators=(f,), define_helper_functions=false)
    @assert enum.ops[1][1] === f
    before = state[]
    enum.ops[1][1](1.0)
    @assert state[] == before + 1
end

# Deprecated simplify_tree is in-place and returns the original root.
ops = OperatorEnum(1 => (sin,), 2 => (+,); define_helper_functions=false)
root = Node(; op=1, children=(Node(Float64; val=2.0), Node(Float64; val=3.0)))
@assert DE.simplify_tree(root, ops) === root
@assert root.degree == 0 && root.val == 5.0
println(
    "CHECKED plumbing fresh arrays, borrowed refs/values/children/operators, index copies, setter/simplifier identities",
)
