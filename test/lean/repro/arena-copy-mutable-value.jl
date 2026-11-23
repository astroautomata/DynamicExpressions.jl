include("arena-pr.jl")

plain = Node{BigInt,2}(; val=big(1))
arena = ArenaNode{BigInt,2}(; val=big(1))
plain_copy = copy(plain)
arena_copy = copy(arena)
@assert plain_copy.val !== plain.val
@assert arena_copy.val === arena.val
Base.GMP.MPZ.add!(arena_copy.val, big(2))
@assert arena.val == 3
println("REPRODUCED arena-copy-mutable-value")
