# Aliasing observations for the evaluator (no bug claimed; prints facts that
# the Lean properties eval-alias-fresh, eval-alias-slots, eval-alias-successive
# and eval-generic-exposure state).
using DynamicExpressions
using DynamicExpressions: ArrayBuffer
using DynamicExpressions.EvaluateModule: reset_index!
ops = OperatorEnum(1 => (inv, -), 2 => (+, /))
x1 = Node{Float64}(; feature=1)
x2 = Node{Float64}(; feature=2)
X = [1.0 2.0 3.0; 4.0 5.0 6.0]
X0 = copy(X)

# Unbuffered output of a feature leaf is a copy: mutating it leaves X intact.
y, _ = eval_tree_array(x1, X, ops)
println("leaf output aliases X: ", Base.mightalias(y, X))
y .= 99.0
println("X unchanged after mutating output: ", X == X0)

# In-place kernels write into their own cumulators, never into X.
for t in (
    Node(; op=1, children=(x1, x2)), Node(; op=2, children=(Node(; op=1, children=(x1,)),))
)
    for fused in (true, false)
        eval_tree_array(t, X, ops; eval_context=EvalContext(; use_fused=fused))
    end
end
println("X unchanged after evaluations: ", X == X0)

# A failed evaluation fills its own output with NaN, not X.
bad = Node(; op=1, children=(Node{Float64}(; val=NaN), x1))
z = bad(X, ops)
println("failed call output all NaN: ", all(isnan, z), "; X unchanged: ", X == X0)

# Buffered outputs: successive calls without reset use different slots.
buf = ArrayBuffer(zeros(8, 3), Ref(0))
ctx = EvalContext(; buffer=buf)
a, _ = eval_tree_array(Node(; op=1, children=(x1, x2)), X, ops; eval_context=ctx)
b, _ = eval_tree_array(Node(; op=1, children=(x2, x2)), X, ops; eval_context=ctx)
println("successive buffered outputs alias: ", Base.mightalias(a, b), " a=", a, " b=", b)
# After reset_index! the next call reuses slot 1 and overwrites `a` (documented borrow).
reset_index!(buf)
eval_tree_array(Node(; op=1, children=(x1, x1)), X, ops; eval_context=ctx)
println("after reset, earlier output overwritten: ", a)

# The fused branch reserves a slot before checking the inner constant pair.
using Test: @test, @test_throws
pair = Node(; op=2, children=(Node{Float64}(; val=1.0), Node{Float64}(; val=0.0)))
fused_tree = Node(; op=1, children=(pair, x1))
one_slot = ArrayBuffer(zeros(1, size(X, 2)), Ref(0))
@test_throws BoundsError eval_tree_array(
    fused_tree, X, ops; eval_context=EvalContext(; buffer=one_slot)
)
enough_slots = ArrayBuffer(zeros(count_nodes(fused_tree), size(X, 2)), Ref(0))
_, complete = eval_tree_array(
    fused_tree, X, ops; eval_context=EvalContext(; buffer=enough_slots)
)
@test !complete
@test enough_slots.index[] == 2

# Generic evaluator: leaves return the input element / tree constant itself.
gops = GenericOperatorEnum(1 => (inv,), 2 => (+,))
xv = [[1.0, 2.0], [3.0]]
yv, _ = eval_tree_array(Node{Vector{Float64}}(; feature=1), xv, gops)
println("generic feature leaf === input element: ", yv === xv[1])
c = Node{Vector{Float64}}(; val=[5.0])
yc, _ = eval_tree_array(c, xv, gops)
println("generic constant leaf === tree constant: ", yc === c.val)
Xm = reshape([[1.0], [2.0]], 1, 2)
ym, _ = eval_tree_array(c, Xm, gops)
println(
    "generic matrix constant fill elements === tree constant: ", all(e -> e === c.val, ym)
)
