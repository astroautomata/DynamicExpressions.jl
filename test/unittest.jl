using SafeTestsets: @safetestset
using TestItems: @testitem

@testitem "Test Aqua.jl" begin
    include("test_aqua.jl")
end

@safetestset "Initial error handling test" begin
    include("test_initial_errors.jl")
end

# Trigger extensions:
using Zygote, SymbolicUtils, LoopVectorization, Optim

@safetestset "Test deprecations" begin
    include("test_deprecations.jl")
end

include("test_optim.jl")

@testitem "Test tree construction and scoring" begin
    include("test_tree_construction.jl")
end

@testitem "Test SymbolicUtils interface" begin
    include("test_symbolic_utils.jl")
end

@testitem "Test derivatives" begin
    include("test_derivatives.jl")
end

@testitem "Zero requested gradients" begin
    using DynamicExpressions: eval_grad_tree_array
    using DispatchDoctor: allow_unstable

    operators = OperatorEnum(; binary_operators=(+,))
    x = Node{Float64}(; feature=1)
    c = Node{Float64}(; val=2.0)
    X = ones(1, 2)
    X0 = zeros(0, 2)
    for input in (X, view(X, :, :), transpose(permutedims(X)))
        for tree in (x, Node{Float64}(; op=1, children=(x, x)))
            values, gradient, complete = allow_unstable() do
                eval_grad_tree_array(tree, input, operators; variable=false)
            end
            @test complete
            @test size(gradient) == (0, 2)
            @test values == fill(tree.degree == 0 ? 1.0 : 2.0, 2)
        end
    end
    for input in (X0, view(X0, :, :), transpose(permutedims(X0)))
        values, gradient, complete = allow_unstable() do
            eval_grad_tree_array(c, input, operators; variable=true)
        end
        @test complete
        @test size(gradient) == (0, 2)
        @test values == fill(2.0, 2)
    end
end

@testitem "Directional completion checks values and derivatives" begin
    using DynamicExpressions: eval_diff_tree_array

    operators = OperatorEnum(; binary_operators=(/,), unary_operators=(sqrt,))
    x = Node{Float64}(; feature=1)
    for (tree, X, expected) in (
        (Node{Float64}(; val=Inf), ones(1, 2), false),
        (Node{Float64}(; val=NaN), ones(1, 2), false),
        (x, fill(Inf, 1, 2), false),
        (Node{Float64}(; op=1, children=(x, Node{Float64}(; val=0.0))), ones(1, 2), false),
        (Node{Float64}(; op=1, children=(x,)), zeros(1, 2), false),
        (Node{Float64}(; op=1, children=(x,)), ones(1, 2), true),
        (Node{Float64}(; val=Inf), zeros(1, 0), true),
        (Node{Float64}(; val=floatmax(Float64)), ones(1, 2), true),
    )
        values, derivative, complete = eval_diff_tree_array(tree, X, operators, 1)
        @test complete == expected
        @test complete == (all(isfinite, values) && all(isfinite, derivative))
    end
end

@testitem "Test chain rules" begin
    include("test_chainrules.jl")
end

@testitem "Empty sample pullback" begin
    using ChainRulesCore: ChainRulesCore, NoTangent

    operators = OperatorEnum(; binary_operators=(+,))
    x = Node{Float64}(; feature=1)
    c = Node{Float64}(; val=2.0)
    for tree in (c, x, Node{Float64}(; op=1, children=(c, x)))
        X = zeros(1, 0)
        (values, complete), pullback = ChainRulesCore.rrule(
            eval_tree_array, tree, X, operators
        )
        @test isempty(values) && complete
        dfunction, dtree, dX, doperators = pullback((Float64[], NoTangent()))
        @test dfunction == NoTangent()
        @test doperators == NoTangent()
        @test dtree.tree === tree
        @test dtree.gradient == zeros(length(first(get_scalar_constants(tree))))
        @test size(dX) == size(X)
    end
end

@testitem "Test undefined derivatives" begin
    include("test_undefined_derivatives.jl")
end

@testitem "Test simplification" begin
    include("test_simplification.jl")
end

@testitem "Test printing" begin
    include("test_print.jl")
end

include("test_evaluation.jl")
include("test_buffered_evaluation.jl")

@testitem "Test validity of integer expression evaluation" begin
    include("test_integer_evaluation.jl")
end

@testitem "Test NaN detection in evaluator" begin
    include("test_nan_detection.jl")
end

@testitem "Test OperatorEnum with non-number type" begin
    include("test_non_number_eval_tree_array.jl")
end

@testitem "Test hash of tree" begin
    include("test_hash.jl")
end

@testitem "Test sharing-preserving copy" begin
    include("test_graphs.jl")
end

@testitem "Test equation utils" begin
    include("test_utils.jl")
end

@testitem "Test generic operators" begin
    include("test_generic_operators.jl")
end

@testitem "Test tensor operators" begin
    include("test_tensor_operators.jl")
end

@testitem "Test error handling" begin
    include("test_error_handling.jl")
end

@testitem "Test equality operator" begin
    include("test_equality.jl")
end

@testitem "Test operators within module" begin
    include("test_custom_operators.jl")
end

@testitem "Test precompilation" begin
    include("test_precompilation.jl")
end

@testitem "Test Base" begin
    include("test_base.jl")
end
include("test_base_2.jl")
include("test_copy_inplace.jl")

@testitem "Test extra node fields" begin
    include("test_extra_node_fields.jl")
end

@testitem "Test containers preserved" begin
    include("test_container_preserved.jl")
end

@testitem "Test helpers break upon redefining" begin
    include("test_safe_helpers.jl")
end

@testitem "Test custom node type" begin
    include("test_custom_node_type.jl")
end

@testitem "Test random sampling" begin
    include("test_random.jl")
end

@testitem "NodeSampler rejects negative and non-finite weights" begin
    operators = OperatorEnum(; binary_operators=[+, -, *, /], unary_operators=[cos, sin])
    x = GraphNode(Float64; feature=1)
    tree = cos(x) + x

    for weight in (-1.0, -Inf, Inf, NaN)
        @test_throws "finite and nonnegative" rand(
            NodeSampler(; tree, weighting=_ -> weight)
        )
    end
    @test_throws ArgumentError rand(
        NodeSampler(; tree, weighting=node -> node === x ? -1.0 : 1.0)
    )
end

include("test_expressions.jl")
include("test_multi_expression.jl")
include("test_parse.jl")
include("test_parametric_expression.jl")
include("test_operator_construction_edgecases.jl")
include("test_node_interface.jl")
include("test_expression_math.jl")
include("test_structured_expression.jl")
include("test_zygote_gradient_wrapper.jl")
include("test_supposition_consistency.jl")
include("test_n_arity_nodes.jl")
include("test_arenanode.jl")
