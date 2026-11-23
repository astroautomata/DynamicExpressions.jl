using DynamicExpressions, Zygote, ChainRulesCore
const DE = DynamicExpressions
operators = OperatorEnum(; binary_operators=[+, *])
feature() = Node{Float64}(; feature=1)
constant() = Node{Float64}(; val=2.0)
trees = [
    feature(),
    constant(),
    Node{Float64}(; op=1, children=(feature(), feature())),
    Node{Float64}(; op=2, children=(constant(), feature())),
]
for X in (
    reshape([3.0, 4.0], 1, 2),
    view(reshape([3.0, 4.0], 1, 2), :, :),
    transpose(reshape([3.0, 4.0], 2, 1)),
)
    for tree in trees
        before = copy(X)
        y, d, complete = eval_diff_tree_array(tree, X, operators, 1)
        @assert complete && X == before
        @assert !Base.mightalias(y, X) && !Base.mightalias(d, X) && !Base.mightalias(y, d)
        saved_y, saved_d = copy(y), copy(d)
        eval_diff_tree_array(constant(), X, operators, 1)
        @assert y == saved_y && d == saved_d
        y[1] = 99.0
        @assert d == saved_d && X == before
        for mode in (true, false, Val(:both))
            # Generic zero-gradient branch storage is malformed and the fused kernel
            # performs unchecked out-of-bounds reads; its dedicated reproducer uses bounds checks.
            if !(X isa Array) &&
                mode === false &&
                tree.degree > 0 &&
                count_constant_nodes(tree) == 0
                continue
            end
            y, g, complete = eval_grad_tree_array(tree, X, operators; variable=mode)
            @assert complete && X == before
            @assert !Base.mightalias(y, X) &&
                !Base.mightalias(g, X) &&
                !Base.mightalias(y, g)
            saved_y, saved_g = copy(y), copy(g)
            eval_grad_tree_array(constant(), X, operators; variable=mode)
            @assert y == saved_y && g == saved_g
            y[1] = 99.0
            @assert g == saved_g && X == before
            if !isempty(g)
                g[1] = 77.0
                @assert y[1] == 99.0 && X == before
            end
        end
    end
end

X = reshape([3.0, 4.0], 1, 2)
tree = Node{Float64}(; op=2, children=(constant(), feature()))
source_gradient = [1.0]
tangent = NodeTangent(tree, source_gradient)
@assert tangent.tree === tree && tangent.gradient === source_gradient
@assert extract_gradient(tangent, tree) === source_gradient
source_gradient[1] = 8.0
@assert extract_gradient(tangent, tree)[1] == 8.0
for result in (tangent + tangent, 2.0 * tangent, tangent * 2.0)
    @assert result.tree === tree
    @assert !Base.mightalias(result.gradient, source_gradient)
    result.gradient[1] = -1.0
    @assert source_gradient[1] == 8.0
end

(primal, complete), pullback = rrule(eval_tree_array, tree, X, operators)
@assert complete &&
    pullback.tree === tree &&
    pullback.X === X &&
    pullback.operators === operators
dY = [2.0, 3.0]
_, dtree, dX, _ = pullback((dY, NoTangent()))
@assert dtree.tree === tree
for a in (dtree.gradient, dX)
    @assert !Base.mightalias(a, X) && !Base.mightalias(a, dY) && !Base.mightalias(a, primal)
end
@assert !Base.mightalias(dtree.gradient, dX)
input_before, cotangent_before = copy(X), copy(dY)
dX[1] = -10.0
dtree.gradient[1] = -20.0
@assert X == input_before && dY == cotangent_before
_, dtree2, dX2, _ = pullback((dY, NoTangent()))
@assert !Base.mightalias(dX2, dX) && !Base.mightalias(dtree2.gradient, dtree.gradient)

arena = DE.EvaluateModule.ArrayBuffer(zeros(2, 2), Ref(0))
context = EvalContext(; buffer=arena)
(primal, complete), _ = rrule(
    eval_tree_array, constant(), X, operators; eval_context=context
)
@assert complete && Base.mightalias(primal, arena.array) && !Base.mightalias(primal, X)
@assert primal == [2.0, 2.0]
DE.EvaluateModule.reset_index!(arena)
rrule(eval_tree_array, Node{Float64}(; val=9.0), X, operators; eval_context=context)
@assert primal == [9.0, 9.0] && X == input_before
DE.EvaluateModule.reset_index!(arena)
(invalid_primal, complete), _ = rrule(
    eval_tree_array,
    Node{Float64}(; op=2, children=(Node{Float64}(; val=Inf), feature())),
    X,
    operators;
    eval_context=context,
)
@assert !complete &&
    all(isnan, invalid_primal) &&
    Base.mightalias(invalid_primal, arena.array)
@assert X == input_before
println("ALIAS CHECKS PASSED Deriv")
