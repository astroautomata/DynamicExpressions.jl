@testmodule ArenaTreeGen begin
    using DynamicExpressions
    using DynamicExpressions: ArenaNode, Arena
    using DynamicExpressions.ArenaNodeModule: is_compact, _append_subtree!
    using Random: AbstractRNG

    export random_tree

    function random_leaf(rng, ::Type{T}, ::Val{D}, nfeat, const_p) where {T,D}
        if rand(rng) < const_p
            return Node{T,D}(; val=randn(rng, T))
        else
            return Node{T,D}(; feature=rand(rng, 1:nfeat))
        end
    end

    """Grow a random `Node{T,D}` tree to `n` nodes. `arity_cdf[d]` is the
    cumulative probability of expanding a leaf to degree `d`; `nops[d]` is the
    number of degree-`d` operators in the testitem's `OperatorEnum`."""
    function random_tree(
        rng::AbstractRNG,
        n;
        T=Float64,
        D=2,
        nfeat=3,
        nops=(2, 4),
        arity_cdf=(0.3, 1.0),
        const_p=0.5,
    )
        leaf() = random_leaf(rng, T, Val(D), nfeat, const_p)
        tree = leaf()
        while count_nodes(tree) < n
            node = rand(rng, filter(t -> t.degree == 0, tree))
            r = rand(rng)
            d = something(findfirst(>=(r), arity_cdf), D)
            node.degree = d
            node.op = rand(rng, 1:nops[d])
            set_children!(node, ntuple(_ -> leaf(), d))
            node.constant = false
            node.val = zero(T)
        end
        return tree
    end

    """True unless `root`'s arena is flagged compact without holding exactly
    `root`'s tree in the canonical postfix layout (root last) that the flat fast
    paths assume."""
    function compact_flag_is_honest(root::ArenaNode{T,D}) where {T,D}
        arena = root.arena
        is_compact(arena) || return true
        root.idx == length(arena) || return false
        relaid = Arena{T,D}(; capacity=length(arena))
        _append_subtree!(relaid, arena.nodes, root.idx)
        return relaid.nodes == arena.nodes
    end
end

@testsnippet ExprLeaves begin
    using DynamicExpressions

    operators = OperatorEnum(1 => (sin, cos), 2 => (+, -, *, /))
    x1, x2 = [
        Expression(Node{Float64}(; feature=i); operators, variable_names=["x1", "x2"]) for
        i in 1:2
    ]
end

@testitem "ArenaNode NodeInterface" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode, NodeInterface
    using Interfaces: Interfaces

    @test Interfaces.test(
        NodeInterface,
        ArenaNode,
        [
            convert(ArenaNode{Float64}, get_tree(sin(x1) + x1 * 3.2)),
            convert(ArenaNode{Float64}, get_tree(sin(x1))),
            convert(ArenaNode{Float64}, get_tree(x1)),
            convert(ArenaNode{Float64}, Node{Float64}(; val=1.0)),
        ],
    )
end

@testitem "ArenaNode NodeInterface on n-arity nodes" begin
    using DynamicExpressions
    using DynamicExpressions: ArenaNode, NodeInterface
    using Interfaces: Interfaces

    for D in (3, 4, 5)
        x = [Node{Float64,D}(; feature=i) for i in 1:3]
        tree = Node{Float64,D}(; op=2, children=(x[1], x[2]))
        tree = Node{Float64,D}(; op=1, children=(tree, x[1], x[2]))
        if D > 3
            tree = Node{Float64,D}(; op=1, children=(tree, x[1], x[2], x[3]))
        end
        trees = [tree, x[1], Node{Float64,D}(; val=1.0)]
        @test Interfaces.test(
            NodeInterface, ArenaNode, [convert(ArenaNode{Float64,D}, t) for t in trees]
        )
    end
end

@testitem "ArenaNode round-trips through Node" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree(sin(x1) + x1 * 3.2)
    atree = convert(ArenaNode{Float64}, tree)
    @test atree isa ArenaNode{Float64,2}
    @test count_nodes(atree) == count_nodes(tree)
    @test string_tree(atree, operators) == string_tree(tree, operators)
    @test tree_mapreduce(_ -> 1, +, atree, Int) == count_nodes(atree)
    @test convert(Node, atree) == tree
end

@testitem "ArenaNode child accessors" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode, Nullable
    using DynamicExpressions.NodeModule: unsafe_get_children

    atree = convert(ArenaNode{Float64}, get_tree(sin(x1) + x1 * 3.2))
    @test unsafe_get_children(atree) isa NTuple{2,Nullable{ArenaNode{Float64,2}}}
    @test length(get_children(atree, atree.degree)) == 2
    @test first(collect(atree; break_sharing=Val(true))).idx == atree.idx
end

@testitem "ArenaNode evaluates like Node" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree(sin(x1) + x1 * 3.2)
    atree = convert(ArenaNode{Float64}, tree)
    X = randn(Float64, 1, 50)
    y_tree, ok_tree = eval_tree_array(tree, X, operators)
    y_atree, ok_atree = eval_tree_array(atree, X, operators)
    @test ok_tree && ok_atree
    @test y_atree ≈ y_tree
end

@testitem "ArenaNode constant edits change evaluation" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    atree = convert(ArenaNode{Float64}, get_tree(sin(x1) + x1 * 3.2))
    only(filter(t -> t.degree == 0 && t.constant, atree)).val = 10.0
    X = randn(Float64, 1, 50)
    y, ok = eval_tree_array(atree, X, operators)
    @test ok
    @test y ≈ sin.(X[1, :]) .+ X[1, :] .* 10.0
    y_node, ok_node = eval_tree_array(convert(Node, atree), X, operators)
    @test ok_node
    @test y_node ≈ y
end

@testitem "ArenaNode copy is independent" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    atree = convert(ArenaNode{Float64}, tree)
    @test is_compact_root(atree)
    for c in (copy(atree), copy_node(atree))
        @test c.arena !== atree.arena
        @test c == atree
        @test convert(Node, c) == tree
        c.l.l.r.val = 99.0
        @test c != atree
        @test convert(Node, atree) == tree
    end
end

@testitem "ArenaNode subtree copy is compact" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    atree = convert(ArenaNode{Float64}, tree)
    @test !is_compact_root(atree.l)
    sub = copy(atree.l)
    @test is_compact_root(sub)
    @test convert(Node, sub) == tree.l
end

@testitem "ArenaNode set_node!" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    target = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    source = convert(ArenaNode{Float64}, get_tree(x1 * 3.2))
    set_node!(target, source)
    @test string_tree(target, operators) == string_tree(source, operators)
end

@testitem "ArenaNode default constructor and setters" begin
    using DynamicExpressions: ArenaNode

    default = ArenaNode{Float64,2}()
    @test default.degree == 0
    @test default.constant
    @test default.val == 0.0
    default.val = 2
    default.feature = 1
    default.op = 2
    default.constant = false
    default.degree = 0
    @test default.val == 2.0
    @test default.feature == 1
    @test default.op == 2
    @test !default.constant
    @test_throws ArgumentError default.foo = 1
end

@testitem "ArenaNode set_child! copies a foreign child" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    parent = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    child = convert(ArenaNode{Float64}, get_tree(x1 * 3.2))
    set_child!(parent, child, 1)
    @test get_child(parent, 1).arena === parent.arena
    child.r.val = 99.0
    X = randn(Float64, 1, 50)
    y, ok = eval_tree_array(parent, X, operators)
    @test ok
    @test y ≈ sin.(X[1, :] .* 3.2)
end

@testitem "ArenaNode set_child! rejects bad input" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    parent = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    child = convert(ArenaNode{Float64}, get_tree(x1 * 3.2))
    n_before = length(parent.arena)
    @test_throws BoundsError set_child!(parent, child, 3)
    @test length(parent.arena) == n_before
    @test_throws ArgumentError set_child!(parent, Node{Float32}(; val=1.0f0), 1)
end

@testitem "ArenaNode set_children!" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode, Nullable

    rewritten = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    set_children!(rewritten, (convert(ArenaNode{Float64}, get_tree(x1 * 2.0)),))
    @test get_child(rewritten, 1).arena === rewritten.arena
    @test string_tree(rewritten, operators) == "sin(x1 * 2.0)"

    bad_children = (Nullable(true, Node{Float64}(; val=0.0)), Node{Float32}(; val=1.0f0))
    @test_throws ArgumentError set_children!(rewritten, bad_children)

    leaf = convert(ArenaNode{Float64}, get_tree(x1))
    @test_throws ArgumentError set_children!(rewritten, (leaf, leaf, leaf))
    @test string_tree(rewritten, operators) == "sin(x1 * 2.0)"
end

@testitem "ArenaNode keyword constructor" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    home_child = convert(ArenaNode{Float64}, get_tree(x1 * 3.2))
    copied_child = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    built = ArenaNode{Float64,2}(; op=1, children=(home_child, copied_child))
    @test built.arena === home_child.arena
    @test get_child(built, 2).arena === built.arena
    @test string_tree(built, operators) == "(x1 * 3.2) + sin(x1)"

    home_child.r.val = 4.0
    @test string_tree(built, operators) == "(x1 * 4.0) + sin(x1)"
    set_child!(copied_child, convert(ArenaNode{Float64}, get_tree(x1 * 2.0)), 1)
    @test string_tree(built, operators) == "(x1 * 4.0) + sin(x1)"

    from_nodes = ArenaNode{Float64,2}(;
        op=3, children=(get_tree(x1), Node{Float64}(; val=2.0))
    )
    @test from_nodes isa ArenaNode{Float64,2}
    @test string_tree(from_nodes, operators) == "x1 * 2.0"
end

@testitem "ArenaNode simplify_tree! folds constants" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    two_plus_three = Node{Float64}(;
        op=1, children=(Node{Float64}(; val=2.0), Node{Float64}(; val=3.0))
    )
    atree = convert(ArenaNode{Float64}, two_plus_three)
    simplify_tree!(atree, operators)
    @test atree.degree == 0
    @test atree.constant
    @test atree.val == 5.0
end

@testitem "ArenaNode combine_operators like Node" setup = [ExprLeaves, ArenaTreeGen] begin
    using DynamicExpressions: ArenaNode
    using Random: MersenneTwister

    # One case per rewrite rule; each folds its two constants into one.
    rule_cases = map(
        get_tree,
        [
            (x1 + 1.0) + 2.0,
            (3.0 * x1) * 2.0,
            (1.0 - x1) - 2.0,
            (x1 - 1.0) - 2.0,
            1.0 - (2.0 - x1),
            1.0 - (x1 - 2.0),
        ],
    )
    for tree in rule_cases
        combined = combine_operators(convert(ArenaNode{Float64}, tree), operators)
        @test count_nodes(combined) == 3
    end

    rng = MersenneTwister(0)
    random_trees = [random_tree(rng, n) for n in 3:20 for _ in 1:10]
    for tree in [rule_cases; random_trees]
        expected = combine_operators(simplify_tree!(copy(tree), operators), operators)
        actual = combine_operators(
            simplify_tree!(convert(ArenaNode{Float64}, tree), operators), operators
        )
        @test actual isa ArenaNode{Float64,2}
        @test string_tree(actual, operators) == string_tree(expected, operators)
    end
end

@testitem "Expression with ArenaNode" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode, ExpressionInterface
    using Interfaces: test

    for ex in (sin(x1) + x1 * 3.2, x1)
        atree = convert(ArenaNode{Float64}, get_tree(ex))
        expr = Expression(atree; operators, variable_names=["x1", "x2"])
        @test get_tree(expr) === atree
        @test test(ExpressionInterface, Expression, [expr])
    end
end

@testitem "ArenaNode derivatives through Expression" begin
    using DynamicExpressions
    using DynamicExpressions: ArenaNode
    using DifferentiationInterface: AutoZygote, gradient
    using Zygote

    operators_grad = OperatorEnum(1 => (sin, cos, exp), 2 => (+, -, *, /))
    x1 = Expression(
        convert(ArenaNode{Float64}, Node{Float64}(; feature=1));
        operators=operators_grad,
        variable_names=[:x1, :x2],
    )
    x2 = Expression(
        convert(ArenaNode{Float64}, Node{Float64}(; feature=2));
        operators=operators_grad,
        variable_names=[:x1, :x2],
    )
    expr_grad = sin(2.0 * x1 + exp(x2 + 5.0))

    Xg = rand(Float64, 2, 10) .+ 1
    expected = @. sin(2.0 * Xg[1, :] + exp(Xg[2, :] + 5.0))
    expected_dy_dx1 = @. 2.0 * cos(2.0 * Xg[1, :] + exp(Xg[2, :] + 5.0))

    result, ok = eval_tree_array(expr_grad, Xg)
    @test ok
    @test result ≈ expected

    _, grad2, ok2 = eval_grad_tree_array(expr_grad, Xg; variable=Val(true))
    @test ok2
    @test grad2[1, :] ≈ expected_dy_dx1

    grad_zygote = expr_grad'(Xg)
    @test grad_zygote[1, :] ≈ expected_dy_dx1

    operators_const = OperatorEnum(2 => (+,))
    x1c = Expression(
        convert(ArenaNode{Float64}, Node{Float64}(; feature=1));
        operators=operators_const,
        variable_names=["x1"],
    )
    expr_const = x1c + 1.5
    _, grad3, ok3 = eval_grad_tree_array(expr_const, ones(1, 5); variable=Val(false))
    @test ok3
    @test grad3[1, :] ≈ fill(1.0, 5)

    d_ex = gradient(AutoZygote(), expr_const) do ex
        return sum(ex(ones(1, 5)))
    end
    @test extract_gradient(d_ex, expr_const) ≈ [5.0]
end

@testitem "ArenaNode edits with capacity do not allocate" begin
    using DynamicExpressions
    using PerformanceTestTools: PerformanceTestTools

    # The suite's DispatchDoctor checks allocate at runtime, so measure in a fresh
    # process that has them disabled, as users do.
    prefs_env = mktempdir()
    write(
        joinpath(prefs_env, "Project.toml"),
        """
        [extras]
        DynamicExpressions = "$(Base.PkgId(DynamicExpressions).uuid)"

        [preferences.DynamicExpressions]
        dispatch_doctor_mode = "disable"
        """,
    )
    pushfirst!(LOAD_PATH, prefs_env)
    try
        PerformanceTestTools.include_foreach(
            joinpath(@__DIR__, "arenanode_allocations_subprocess.jl"),
            [Dict{String,String}()],
        )
    finally
        popfirst!(LOAD_PATH)
    end
end

@testitem "ArenaNode set_child! clears compact flag" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact, is_compact_root

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    mutated = convert(ArenaNode{Float64}, tree)
    set_child!(mutated, convert(ArenaNode{Float64}, get_tree(cos(x2))), 2)
    @test !is_compact(mutated.arena)
    expected = copy(tree)
    set_child!(expected, get_tree(cos(x2)), 2)
    @test convert(Node, mutated) == expected
    @test count_nodes(mutated) == count_nodes(expected)
    @test has_constants(mutated) == has_constants(expected)

    recompacted = copy(mutated)
    @test is_compact_root(recompacted)
    @test count_nodes(recompacted) == count_nodes(expected)
end

@testitem "ArenaNode degree edit clears compact flag" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    atree = convert(ArenaNode{Float64}, tree)
    node = atree.r
    node.degree = 0
    node.constant = true
    node.val = 1.0
    @test !is_compact(atree.arena)
    expected = copy(tree)
    expected.r = Node{Float64}(; val=1.0)
    @test convert(Node, atree) == expected
    @test count_nodes(atree) == count_nodes(expected)
    @test has_constants(atree) == has_constants(expected)
end

@testitem "ArenaNode copy_into! reuses a container" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.NodePreallocationModule: allocate_container, copy_into!

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    atree = convert(ArenaNode{Float64}, tree)
    dest = allocate_container(atree)
    ref = Ref(-1)
    out = copy_into!(dest, atree; ref)
    @test out.arena === dest
    @test convert(Node, out) == tree
    @test ref[] == length(atree)
    out2 = copy_into!(dest, atree; ref)
    @test convert(Node, out2) == tree
    @test ref[] == length(atree)

    same_ref = Ref(-1)
    same = copy_into!(out2.arena, out2; ref=same_ref)
    @test same === out2
    @test same_ref[] == length(out2)
end

@testitem "ArenaNode copy_into! copies a subtree" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root
    using DynamicExpressions.NodePreallocationModule: allocate_container, copy_into!

    tree = get_tree((x1 + cos(x2)) * 0.5)
    atree = convert(ArenaNode{Float64}, tree)
    sub = atree.l
    @test !is_compact_root(sub)
    dest = allocate_container(atree)
    ref = Ref(-1)
    out = copy_into!(dest, sub; ref)
    @test out.arena === dest
    @test is_compact_root(out)
    @test out == copy(sub)
    @test convert(Node, out) == tree.l
    @test ref[] == length(tree.l)
    @test convert(Node, atree) == tree
end

@testitem "ArenaNode copy_into! its own arena" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root
    using DynamicExpressions.NodePreallocationModule: copy_into!

    tree = get_tree((x1 + cos(x2)) * 0.5)
    atree = convert(ArenaNode{Float64}, tree)
    sub = atree.l
    expected = copy(sub)
    ref = Ref(-1)
    out = copy_into!(atree.arena, sub; ref)
    @test out.arena === atree.arena
    @test is_compact_root(out)
    @test out == expected
    @test convert(Node, out) == tree.l
    @test ref[] == length(tree.l)
end

@testitem "Expression copy_into! with ArenaNode" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.NodePreallocationModule: allocate_container, copy_into!

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    ex = Expression(
        convert(ArenaNode{Float64}, tree); operators, variable_names=["x1", "x2"]
    )
    ex2 = copy_into!(allocate_container(ex), ex)
    @test convert(Node, get_tree(ex2)) == tree
end

@testitem "ArenaNode feature leaf has no constants" begin
    using DynamicExpressions
    using DynamicExpressions: ArenaNode

    leaf = convert(ArenaNode{Float64}, Node{Float64}(; feature=1))
    @test !has_constants(leaf)
    @test count_constant_nodes(leaf) == 0
end

@testitem "ArenaNode scalar constants use arena indices" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree(sin(x1 * 3.2 - 0.9) + x2 * (x1 - 0.5))
    atree = convert(ArenaNode{Float64}, tree)
    vals, refs = get_scalar_constants(atree)
    @test refs isa Vector{Int32}
    @test count_scalar_constants(atree) == length(vals)
    @test vals == first(get_scalar_constants(tree))
    @test set_scalar_constants!(atree, vals .* 2, refs) === atree
    @test first(get_scalar_constants(atree)) == vals .* 2

    flat_copy = copy(atree)
    set_scalar_constants!(flat_copy, vals, refs)
    @test first(get_scalar_constants(flat_copy)) == vals

    sub = atree.l
    vsub, rsub = get_scalar_constants(sub)
    @test rsub isa Vector{Int32}
    @test vsub == first(get_scalar_constants(convert(Node, sub)))
    set_scalar_constants!(sub, vsub .+ 1, rsub)
    @test first(get_scalar_constants(sub)) == vsub .+ 1
end

@testitem "ArenaNode set_scalar_constants! converts eltype" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    atree = convert(ArenaNode{Float64}, get_tree(x1 + 9.0))
    _, refs = get_scalar_constants(atree)
    set_scalar_constants!(atree, Float32[2.5], refs)
    @test first(get_scalar_constants(atree)) == [2.5]
end

@testitem "Arena array interface tracks compactness" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: ArenaEntry, _replace, is_compact_root

    tree = get_tree(sin(x1 * 3.2) + 0.5)
    atree = convert(ArenaNode{Float64}, tree)
    a = atree.arena
    @test a isa AbstractVector{ArenaEntry{Float64,2}}
    @test length(a) == count_nodes(tree)

    a[1] = _replace(a[1]; val=42.0)
    @test is_compact_root(atree)

    vals, refs = get_scalar_constants(atree)
    set_scalar_constants!(atree, vals .* 2, refs)
    @test is_compact_root(atree)

    bi = findfirst(e -> e.degree == 0x02, collect(a))
    a[bi] = _replace(a[bi]; degree=0x00)
    @test !a.compact

    b = convert(ArenaNode{Float64}, tree).arena
    copyto!(b, reverse(collect(b)))
    @test !b.compact

    c = convert(ArenaNode{Float64}, tree).arena
    copyto!(c, collect(c))
    @test c.compact
end

@testitem "ArenaNode in a multi-root arena" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode, Arena
    using DynamicExpressions.ArenaNodeModule: is_compact_root, push_constant!, push_feature!

    arena = Arena{Float64,2}()
    push_constant!(arena, 1.0)
    feature_leaf = ArenaNode(arena, push_feature!(arena, 2))
    @test !is_compact_root(feature_leaf)
    @test count_nodes(feature_leaf) == 1
    X = [1.0 2.0 3.0; 0.5 1.5 2.5]
    y, ok = eval_tree_array(feature_leaf, X, operators)
    @test ok
    @test y == X[2, :]
end

@testitem "ArenaNode missing children throw" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.NodeUtilsModule: is_constant

    @test_throws UndefRefError get_child(convert(ArenaNode{Float64}, get_tree(x1)), 1)
    @test_throws BoundsError ArenaNode{Float64,1}().r

    half_built = convert(ArenaNode{Float64}, get_tree(x1))
    half_built.degree = 1
    half_built.op = 1
    @test_throws UndefRefError is_constant(half_built)
    @test_throws UndefRefError any(_ -> false, half_built)
end

@testitem "ArenaNode == across eltypes and Node" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree((x1 + cos(x2)) * 0.5)
    a64 = convert(ArenaNode{Float64}, tree)
    a32 = convert(ArenaNode{Float32}, tree)
    @test promote_type(ArenaNode{Float32,2}, ArenaNode{Float64,2}) == ArenaNode{Float64,2}
    @test a64 == tree
    @test tree == a64
    @test a32 == tree
    @test a32 == a64
    @test a64 == a32
    @test convert(ArenaNode{Float32}, get_tree(x1 + x2)) != a64
end

@testitem "ArenaNode == compares node degrees" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root

    unary_chain = convert(ArenaNode{Float64}, get_tree(sin(sin(x1))))
    binary = convert(ArenaNode{Float64}, get_tree(x1 + x2))
    @test is_compact_root(unary_chain) && is_compact_root(binary)
    @test length(unary_chain) == length(binary)
    @test unary_chain != binary
    @test convert(Node, unary_chain) != convert(Node, binary)
end

@testitem "ArenaNode children property matches Node" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree((x1 + cos(x2)) * 0.5)
    atree = convert(ArenaNode{Float64}, tree)
    @test map(c -> convert(Node, c[]), atree.children) == map(c -> c[], tree.children)
end

@testitem "ArenaNode unknown property throws like Node" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree(x1 * 0.5)
    @test_throws r"no field .?not_a_field" tree.not_a_field
    @test_throws r"no field .?not_a_field" convert(ArenaNode{Float64}, tree).not_a_field
end

@testitem "ArenaNode l/r assignment matches set_child!" setup = [ExprLeaves] begin
    using DynamicExpressions: ArenaNode

    tree = get_tree((x1 + cos(x2)) * 0.5)
    via_property = convert(ArenaNode{Float64}, tree)
    via_set_child = convert(ArenaNode{Float64}, tree)
    new_l = convert(ArenaNode{Float64}, get_tree(x2))
    new_r = convert(ArenaNode{Float64}, get_tree(sin(x1)))
    via_property.l = new_l
    via_property.r = new_r
    set_child!(via_set_child, new_l, 1)
    set_child!(via_set_child, new_r, 2)
    @test via_property == via_set_child
    @test convert(Node, via_property) == get_tree(x2 * sin(x1))
end

@testitem "ArenaNode supposition invariants" setup = [ArenaTreeGen] begin
    using Supposition
    using Supposition: @check, Data
    using DynamicExpressions
    using DynamicExpressions: ArenaNode
    using DynamicExpressions.ArenaNodeModule: is_compact_root
    using DynamicExpressions.NodeUtilsModule: is_constant

    include("supposition_utils.jl")

    const T = Float64
    const N_FEATURES = 5
    const OPERATORS = OperatorEnum(1 => (abs, cos), 2 => (+, -, *, /))

    expr_gen = make_expression_generator(
        T; num_features=N_FEATURES, max_layers=8, operators=OPERATORS
    )
    tree_gen = map(get_tree, expr_gen)
    input_gen = make_input_matrix_generator(T; n_features=N_FEATURES)

    # Round-trip and read-only properties are representation-independent.
    roundtrip = @check function arena_roundtrip(tree=tree_gen)
        atree = convert(ArenaNode{T,2}, tree)
        back = convert(Node, atree)
        return back == tree &&
               string_tree(atree, OPERATORS) == string_tree(tree, OPERATORS) &&
               count_nodes(atree) == count_nodes(tree) &&
               count_constant_nodes(atree) == count_constant_nodes(tree) &&
               count_depth(atree) == count_depth(tree) &&
               hash(atree) == hash(tree) &&
               has_constants(atree) == has_constants(tree) &&
               has_operators(atree) == has_operators(tree) &&
               copy(atree) == atree
    end
    @test something(roundtrip.result) isa Supposition.Pass

    function evals_match(tree, atree, X)
        # ArenaNode eval takes the same generic path as Node, so both the
        # values and the `ok` flag must match exactly.
        yn, okn = eval_tree_array(copy(tree), X, OPERATORS)
        ya, oka = eval_tree_array(atree, X, OPERATORS)
        okn == oka || return false
        okn && !(yn ≈ ya) && return false
        return true
    end

    evals = @check function arena_eval_matches_node(tree=tree_gen, X=input_gen)
        return evals_match(tree, convert(ArenaNode{T,2}, tree), X)
    end
    @test something(evals.result) isa Supposition.Pass

    # Valid mutations applied identically to both representations keep them
    # equivalent. Mutations are specified positionally (preorder index).
    mutation_gen = map(
        (kind, i, value, op, feature) -> if kind == 1
            (:set_val, i, value)
        elseif kind == 2
            (:set_op, i, op)
        elseif kind == 3
            (:to_leaf, i, value)
        elseif kind == 4
            (:to_feature, i, feature)
        else
            (:set_child, i, value)
        end,
        Data.SampledFrom(1:5),
        Data.Integers(1, 64),
        Data.Floats{T}(; nans=false, infs=false),
        Data.Integers(1, 4),
        Data.Integers(1, N_FEATURES),
    )

    function apply_mutation!(tree, (kind, i, x))
        nodes = collect(tree)
        node = nodes[mod1(i, length(nodes))]
        if kind == :set_val
            if node.degree == 0 && node.constant
                node.val = x
            end
        elseif kind == :set_op
            if node.degree == 2
                node.op = mod1(x, 4)
            elseif node.degree == 1
                node.op = mod1(x, 2)
            end
        elseif kind == :to_leaf
            node.degree = 0
            node.constant = true
            node.val = x
        elseif kind == :to_feature
            node.degree = 0
            node.constant = false
            node.feature = x
        elseif kind == :set_child
            if node.degree > 0
                set_child!(node, Node{T,2}(; val=x), 1)
            end
        end
        return tree
    end

    mutations = @check function arena_mutation_matches_node(
        tree0=tree_gen, X=input_gen, muts=Data.Vectors(mutation_gen; min_size=1, max_size=5)
    )
        tree = copy(tree0)
        atree = convert(ArenaNode{T,2}, tree0)
        for mut in muts
            apply_mutation!(tree, mut)
            apply_mutation!(atree, mut)
        end
        return ArenaTreeGen.compact_flag_is_honest(atree) &&
               string_tree(atree, OPERATORS) == string_tree(tree, OPERATORS) &&
               count_nodes(atree) == count_nodes(tree) &&
               count_constant_nodes(atree) == count_constant_nodes(tree) &&
               has_constants(atree) == has_constants(tree) &&
               is_constant(atree) == is_constant(tree) &&
               first(get_scalar_constants(atree)) == first(get_scalar_constants(tree)) &&
               convert(Node, atree) == tree &&
               evals_match(tree, atree, X)
    end
    @test something(mutations.result) isa Supposition.Pass

    # Re-compacting after mutation (via copy) preserves the tree and re-enables
    # the flat fast paths.
    recompact = @check function arena_copy_recompacts(
        tree0=tree_gen, X=input_gen, muts=Data.Vectors(mutation_gen; min_size=1, max_size=3)
    )
        tree = copy(tree0)
        atree = convert(ArenaNode{T,2}, tree0)
        for mut in muts
            apply_mutation!(tree, mut)
            apply_mutation!(atree, mut)
        end
        compacted = copy(atree)
        return is_compact_root(compacted) &&
               ArenaTreeGen.compact_flag_is_honest(compacted) &&
               compacted == atree &&
               hash(compacted) == hash(atree) &&
               evals_match(tree, compacted, X)
    end
    @test something(recompact.result) isa Supposition.Pass
end
