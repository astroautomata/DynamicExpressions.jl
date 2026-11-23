using DynamicExpressions
using TOML
using Test
const DE = DynamicExpressions
@assert DE.PACKAGE_VERSION ==
    VersionNumber(TOML.parsefile(joinpath(pkgdir(DE), "Project.toml"))["version"]) ==
    v"2.14.0"
# Check each re-export against the named source submodule, including macros.
lines = readlines(joinpath(pkgdir(DE), "src", "DynamicExpressions.jl"))
for i in eachindex(lines)
    m = match(r"^@reexport import \.(\w+)(.*)$", lines[i])
    isnothing(m) && continue
    mod = getfield(DE, Symbol(m.captures[1]))
    tail = m.captures[2]
    startswith(tail, ":") || continue
    namestr = tail[2:end]
    j = i + 1
    while j <= length(lines) && startswith(lines[j], "    ")
        namestr *= lines[j]
        j += 1
    end
    for name in split(namestr, ',')
        sym = Symbol(strip(name))
        isempty(string(sym)) && continue
        @assert isdefined(mod, sym) && isdefined(DE, sym)
        @assert getfield(DE, sym) === getfield(mod, sym)
    end
end
ops = OperatorEnum(1 => (sin,), 2 => (+,); define_helper_functions=false)
for N in (Node, GraphNode, ParametricNode)
    x = N(Float64; feature=1)
    c = N(Float64; val=2.0)
    t = N(; op=1, children=(x, c))
    for fixture in (x, c, t)
        for (name, check) in pairs(DE.InterfacesModule.ni_components.mandatory)
            @assert last(check)(fixture) "Node check $N $name"
        end
    end
end
ex = Expression(Node(Float64; feature=1); operators=ops, variable_names=["x"])
pex = ParametricExpression(
    ParametricNode(Float64; feature=1);
    operators=ops,
    variable_names=["x"],
    parameters=ones(1, 1),
    parameter_names=["p"],
)
sex = StructuredExpression((a=ex,); structure=nt -> nt.a)
for fixture in (ex, pex, sex)
    for (name, check) in pairs(DE.InterfacesModule.ei_components.mandatory)
        @assert last(check)(fixture) "Expression check $(typeof(fixture)) $name"
    end
end
for N in (Node, GraphNode)
    x = N(Float64; feature=1)
    c = N(Float64; val=2.0)
    @assert N(1, true, 2.0) == c
    @assert N(Float64, 1, true, 2) == c
    @assert N(Float64, 1, false, nothing, 1) == x
    @assert N(1, false, nothing, 0, 1, x) == N(; op=1, children=(x,))
    @assert N(2, false, nothing, 0, 1, x, c) == N(; op=1, children=(x, c))
    @test_throws AssertionError N(0, true, 2.0)
    @test_throws AssertionError N(Float64, 1, true, nothing, 1)
    @test_throws InexactError N(Int, 1, true, 1.5)
    @test_throws InexactError N(Int; val=1.5)
end
for E in (OperatorEnum, GenericOperatorEnum)
    @assert E(;
        unary_operators=[sin], binary_operators=(+,), define_helper_functions=false
    ).ops == E(1 => (sin,), 2 => (+,); define_helper_functions=false).ops
    @assert E(; define_helper_functions=false).ops == ((), ())
end
t = Node(; op=1, children=(Node(Float64; val=2.0), Node(Float64; feature=1)))
@assert DE.count_constants(t) == count_constant_nodes(t)
function index_snapshot(n)
    return if n.degree == 0
        (0, n.val)
    else
        (n.degree, map(index_snapshot, get_children(n, n.degree)))
    end
end
@assert index_snapshot(DE.index_constants(t)) == index_snapshot(index_constant_nodes(t))
oldvals, refs = DE.get_constants(t)
@assert oldvals == get_scalar_constants(t)[1]
DE.set_constants!(t, [3.0], refs)
@assert get_scalar_constants(t)[1] == [3.0]
@assert DE.simplify_tree(copy(t), ops) == simplify_tree!(copy(t), ops)
@assert DE.EquationModule === DE.NodeModule
@assert DE.EquationUtilsModule === DE.NodeUtilsModule
@assert DE.EvaluateEquationModule === DE.EvaluateModule
@assert DE.EvaluateEquationDerivativeModule === DE.EvaluateDerivativeModule
@assert DE.SimplifyEquationModule === DE.SimplifyModule
@assert DE.EvalOptions === DE.EvalContext
@test_deprecated DE.count_constants(t)
@test_deprecated DE.index_constants(t)
@test_deprecated DE.get_constants(t)
@test_deprecated DE.set_constants!(t, [3.0], refs)
@test_deprecated DE.simplify_tree(copy(t), ops)
@test_deprecated Node(1, true, 2.0)
@test_deprecated GraphNode(1, true, 2.0)
@test_deprecated OperatorEnum(;
    unary_operators=(sin,), binary_operators=(+,), define_helper_functions=false
)
@test_deprecated GenericOperatorEnum(;
    unary_operators=(sin,), binary_operators=(+,), define_helper_functions=false
)
DE.do_precompilation(; mode=:precompile)
DE.do_precompilation(; mode=:compile)
@test_throws ErrorException("Invalid value for mode: :invalid") DE.do_precompilation(;
    mode=:invalid
)
println("CHECKED plumbing assembly, interfaces, legacy forwarding, version, workload modes")
