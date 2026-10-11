# Run in a subprocess by the "ArenaNode edits with capacity do not allocate" testitem.
using Test
using DynamicExpressions
using DynamicExpressions: Arena, ArenaNode
using DynamicExpressions.ArenaNodeModule: push_constant!, _copy_to_arena!
using DynamicExpressions.NodePreallocationModule: allocate_container, copy_into!
using Preferences: load_preference

@test load_preference(DynamicExpressions, "dispatch_doctor_mode") == "disable"

# `Vararg{Any,N}` forces specialization; with plain `args...` the call is dynamic, and on
# Julia 1.10 the returned `ArenaNode` (an immutable holding a reference) is then boxed.
function allocations(f::F, args::Vararg{Any,N}) where {F,N}
    f(args...)
    return @allocated f(args...)
end

operators = OperatorEnum(1 => (sin, cos), 2 => (+, -, *, /))
x1 = Expression(Node{Float64}(; feature=1); operators, variable_names=["x1"])
tree = get_tree(sin(x1) + x1 * 3.2 + cos(x1))
atree = convert(ArenaNode{Float64}, tree)

@test allocations(push_constant!, Arena{Float64,2}(; capacity=2), 1.0) == 0

parent = copy_into!(allocate_container(atree, 16), atree)
child = convert(ArenaNode{Float64}, get_tree(x1 * 3.2))
@test allocations(set_child!, parent, child, 1) == 0

arena = Arena{Float64,2}(; capacity=4 * length(atree))
@test allocations(_copy_to_arena!, arena, tree) == 0
@test allocations(_copy_to_arena!, arena, atree) == 0

dest = allocate_container(atree)
@test allocations(copy_into!, dest, atree) == 0
@test allocations(copy_into!, dest, atree.l) == 0
