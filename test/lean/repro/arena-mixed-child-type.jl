include("arena-pr.jl")

children = (Node{Float32,2}(; val=1.0f0), Node{Float64,2}(; val=2.0))
plain = Node{Float64,2}(; op=1, children)
@assert plain.l.val === 1.0 && plain.r.val === 2.0

result = try
    ArenaNode{Float64,2}(; op=1, children)
catch err
    err
end
@assert result isa ArgumentError
@assert occursin("ArenaNode children must be", result.msg)
println("REPRODUCED arena-mixed-child-type")
