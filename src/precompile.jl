import PrecompileTools: @compile_workload, @setup_workload

# COV_EXCL_START

macro ignore_domain_error(ex)
    return esc(
        quote
            try
                $ex
            catch e
                if !(e isa DomainError)
                    rethrow(e)
                end
            end
        end,
    )
end

"""
    test_all_combinations(; binary_operators, unary_operators, turbo, types)

Test all combinations of the given operators and types. Useful for precompilation.
"""
function test_all_combinations(; binary_operators, unary_operators, turbo, types)
    for binops in binary_operators,
        unaops in unary_operators,
        use_turbo in turbo,
        T in types

        length(binops) == 0 && length(unaops) == 0 && continue
        T == Float16 && use_turbo isa Val{true} && continue

        X = rand(T, 3, 10)
        operators = OperatorEnum(1 => unaops, 2 => binops; define_helper_functions=false)
        x = Node(T; feature=1)
        c = Node(T; val=one(T))

        # Trivial:
        for l in (x, c)
            @ignore_domain_error eval_tree_array(
                l, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )
        end

        # Binary operators
        for i in eachindex(binops), l in (x, c), r in (x, c)
            tree = Node(i, l, r)
            tree = convert(Node{T}, tree)
            @ignore_domain_error eval_tree_array(
                tree, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )
        end

        # Unary operators
        for j in eachindex(unaops), k in eachindex(unaops), l in (x, c)
            tree = Node(j, l)
            tree = convert(Node{T}, tree)
            @ignore_domain_error eval_tree_array(
                tree, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )

            tree = Node(j, Node(k, l))
            tree = convert(Node{T}, tree)
            @ignore_domain_error eval_tree_array(
                tree, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )
        end

        # Both operators
        for i in eachindex(binops),
            j1 in eachindex(unaops),
            j2 in eachindex(unaops),
            l in (x, c),
            r in (x, c)

            tree = Node(i, Node(j1, l), Node(j2, r))
            tree = convert(Node{T}, tree)
            @ignore_domain_error eval_tree_array(
                tree, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )

            tree = Node(j1, Node(i, l, r))
            tree = convert(Node{T}, tree)
            @ignore_domain_error eval_tree_array(
                tree, X, operators; eval_context=EvalContext(; turbo=use_turbo)
            )
        end
    end
    return nothing
end

function test_functions_on_trees(::Type{T}, operators) where {T}
    local x, c
    tree = Node(T; feature=1)
    num_unaops = length(operators.unaops)
    num_binops = length(operators.binops)
    @assert num_unaops > 0 && num_binops > 0

    for T1 in [Float32, Float64]
        x = Node(T1; feature=1)
        c = Node(T1; val=T1(1.0))

        i_una = 1
        i_bin = 1

        # Here, we just cycle through the operators and build
        # a more complex expression.
        a1 = Node(i_una, x)
        i_una = (i_una % num_unaops) + 1
        a2 = Node(i_bin, c, a1)
        i_bin = (i_bin % num_binops) + 1
        a3 = Node(i_bin, x, c)
        i_bin = (i_bin % num_binops) + 1
        a4 = Node(i_bin, a3, a2)
        i_bin = (i_bin % num_binops) + 1
        a5 = Node(i_bin, x, x)
        i_bin = (i_bin % num_binops) + 1
        a6 = Node(i_una, a5)
        i_una = (i_una % num_unaops) + 1
        a7 = Node(i_una, a6)
        i_una = (i_una % num_unaops) + 1
        a8 = Node(i_una, a4)
        i_una = (i_una % num_unaops) + 1
        tree = Node(i_bin, a8, a7)
    end
    tree = convert(Node{T}, tree)
    tree = copy_node(tree)
    set_node!(tree, tree)

    string_tree(tree, operators)
    count_nodes(tree)
    count_constant_nodes(tree)
    count_depth(tree)
    index_constant_nodes(tree)
    has_operators(tree)
    has_constants(tree)
    set_scalar_constants!(tree, get_scalar_constants(tree)...)
    combine_operators!(tree, operators)
    simplify_tree!(tree, operators)
    return nothing
end

"""Construct operator enums with helper functions, then restore the global state this sets."""
function test_operator_enum_construction(unary_operators, binary_operators)
    (; LATEST_OPERATORS, LATEST_OPERATORS_TYPE, LATEST_OPERATOR_MAPPING) =
        OperatorEnumConstructionModule
    latest_operators = LATEST_OPERATORS.x
    latest_operators_type = LATEST_OPERATORS_TYPE.x
    mapping = Dict(k => copy(v) for (k, v) in LATEST_OPERATOR_MAPPING)

    pairs = Base.inferencebarrier((1 => unary_operators, 2 => binary_operators))
    OperatorEnum(pairs...)
    GenericOperatorEnum(pairs...; define_helper_functions=false)
    precompile(GenericOperatorEnum, map(typeof, pairs))

    LATEST_OPERATORS.x = latest_operators
    LATEST_OPERATORS_TYPE.x = latest_operators_type
    for k in collect(keys(LATEST_OPERATOR_MAPPING))
        haskey(mapping, k) || delete!(LATEST_OPERATOR_MAPPING, k)
    end
    for (k, v) in mapping
        merge!(empty!(LATEST_OPERATOR_MAPPING[k]), v)
    end
    return nothing
end

"""
Precompile the runtime-dispatched calls that record operators in the global mappings.
"""
function precompile_operator_mappings()
    (; ALREADY_DEFINED_OPERATORS, OP_FIELDTYPE) = OperatorEnumConstructionModule
    precompile(haskey, (Dict{Any,Bool}, Function))
    for defined in values(ALREADY_DEFINED_OPERATORS.operator_enum[Number]),
        func in keys(defined)

        precompile(setindex!, (Dict{Any,OP_FIELDTYPE}, Int, typeof(func)))
    end
    return nothing
end

"""
Precompile the macros still used in generated function bodies, such as the derivative
evaluators.
"""
function precompile_generated_function_macros()
    C = Base.Cartesian
    precompile(C.var"@nexprs", (LineNumberNode, Module, Int, Expr))
    precompile(C.var"@ntuple", (LineNumberNode, Module, Int, Any))
    if isdefined(C, :lreplace!) && isdefined(C, :LReplace) && C.LReplace isa UnionAll
        precompile(C.lreplace!, (QuoteNode, C.LReplace{String}))
    end
    return nothing
end

function test_functions_on_expressions(::Type{T}, operators) where {T}
    variable_names = ["x1", "x2"]
    x1 = Base.inferencebarrier(Expression(Node{T}(; feature=1); operators, variable_names))
    x2 = Base.inferencebarrier(Expression(Node{T}(; feature=2); operators, variable_names))
    ex = x1 * cos(x2 - T(3.2))
    ex = 2.0 * sin(ex) / 1 + (x1 - 0.5) + (1 - x2)
    ex = copy(ex)
    ex(rand(T, 2, 10))
    repr(ex)
    string_tree(ex; pretty=true)
    string_tree(Base.inferencebarrier(Expression(Node{T}(; feature=1); operators)))
    return nothing
end

macro maybe_setup_workload(mode, ex)
    precompile_ex = Expr(
        :macrocall, Symbol("@setup_workload"), LineNumberNode(@__LINE__), ex
    )
    return quote
        if $(esc(mode)) == :compile
            $(esc(ex))
        elseif $(esc(mode)) == :precompile
            $(esc(precompile_ex))
        else
            error("Invalid value for mode: " * repr($(esc(mode))))
        end
    end
end

macro maybe_compile_workload(mode, ex)
    precompile_ex = Expr(
        :macrocall, Symbol("@compile_workload"), LineNumberNode(@__LINE__), ex
    )
    return quote
        if $(esc(mode)) == :compile
            $(esc(ex))
        elseif $(esc(mode)) == :precompile
            $(esc(precompile_ex))
        else
            error("Invalid value for mode: " * repr($(esc(mode))))
        end
    end
end

"""`mode=:precompile` will use `@precompile_*` directives; `mode=:compile` runs."""
function do_precompilation(; mode=:precompile)
    @maybe_setup_workload mode begin
        binary_operators = ((+, -, *, /),)
        unary_operators = ((sin, cos), (exp, log, sqrt, abs))
        turbo = (Val(false),)
        types = (Float32, Float64)
        @maybe_compile_workload mode begin
            test_all_combinations(;
                binary_operators=binary_operators,
                unary_operators=unary_operators,
                turbo=turbo,
                types=types,
            )
        end
        @maybe_compile_workload mode begin
            test_operator_enum_construction(unary_operators[1], binary_operators[1])
        end
        precompile_operator_mappings()
        precompile_generated_function_macros()
        operators = OperatorEnum(
            1 => unary_operators[1], 2 => binary_operators[1]; define_helper_functions=false
        )
        # Want to precompile all above calls.
        types = [Float32, Float64]
        for T in types
            @maybe_compile_workload mode begin
                test_functions_on_trees(T, operators)
                test_functions_on_expressions(T, operators)
            end
        end
    end
end

# COV_EXCL_STOP
