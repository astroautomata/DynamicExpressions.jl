module ExpressionAlgebraModule

using ..NodeModule: AbstractExpressionNode
using ..ExpressionModule:
    AbstractExpression,
    get_operators,
    get_contents,
    get_metadata,
    with_contents,
    constructorof

@inline function insert_operator_index(
    op::Integer,
    @nospecialize(exprs::Tuple),
    @nospecialize(example_expr::AbstractExpression)
)
    N, T = node_and_value_types(example_expr)
    return _insert_operator_index(op, exprs, example_expr, N, T)
end
function node_and_value_types(
    ::E
) where {T,N<:AbstractExpressionNode{T},E<:AbstractExpression{T,N}}
    return (N, T)
end
@inline function _insert_operator_index(
    op::Integer,
    @nospecialize(exprs::Tuple),
    @nospecialize(example_expr::AbstractExpression),
    ::Type{N},
    ::Type{T},
) where {T,N<:AbstractExpressionNode{T}}
    first_expr = _as_expression(exprs[1], example_expr, N, T)
    num_exprs = length(exprs)
    trees_vec = Vector{N}(undef, num_exprs)
    trees_vec[1] = get_contents(first_expr)::N
    for i in 2:num_exprs
        trees_vec[i] = get_contents(_as_expression(exprs[i], example_expr, N, T))::N
    end
    trees = ntuple(i -> trees_vec[i], num_exprs)
    output_tree = constructorof(N)(; children=trees, op)::N
    return with_contents(first_expr, output_tree)
end
@inline function _as_expression(
    @nospecialize(expr),
    @nospecialize(example_expr::AbstractExpression),
    ::Type{N},
    ::Type{T},
) where {T,N<:AbstractExpressionNode{T}}
    if expr isa AbstractExpression
        # Assume the contents are an expression; otherwise, this
        # needs a custom method!
        return expr
    else
        return with_contents(copy(example_expr), constructorof(N)(T; val=expr)::N)
    end
end

struct MissingOperatorError
    msg::String
end

function Base.showerror(io::IO, e::MissingOperatorError)
    return print(io, e.msg)
end

"""
    declare_operator_alias(op, ::Val{arity})

Define how an internal operator should be matched against user-provided operators in expression trees.

By default, operators match themselves. Override this method to specify that an internal operator
should match a different operator when searching the operator lists in expressions.

For example, to make `safe_sqrt` match `sqrt` user-space:

```julia
DynamicExpressions.declare_operator_alias(safe_sqrt, Val(1)) = sqrt
```

Which would allow a user to write `sqrt(x::Expression)`
and have it match the operator `safe_sqrt` stored in the binary operators
of the expression.
"""
declare_operator_alias(@nospecialize(op), _) = op

allow_chaining(@nospecialize(op)) = false
allow_chaining(::typeof(+)) = true
allow_chaining(::typeof(*)) = true

@inline function apply_operator(@nospecialize(op::Function), @nospecialize(args...))
    D = length(args)
    idx = nothing
    for i in 1:D
        if args[i] isa AbstractExpression
            idx = i
            break
        end
    end
    example_expr = args[idx::Int]::AbstractExpression
    E = typeof(example_expr)
    for arg in args
        @assert !(arg isa AbstractExpression) || typeof(arg) === E
    end
    operators = get_operators(example_expr, nothing)

    op_idx = nothing
    if length(operators) >= D
        degree_ops = operators[D]
        for i in 1:length(degree_ops)
            if declare_operator_alias(degree_ops[i], Val(D)) == op
                op_idx = i
                break
            end
        end
    end
    if isnothing(op_idx)
        if allow_chaining(op) && D > 2
            # These operators might get chained by Julia, so we check
            # downward for any matching arity.
            inner = op(args[1:(end - 1)]...)
            return apply_operator(op, inner, args[end])
        end
        throw(
            MissingOperatorError(
                "Operator $op not found in operators for expression type " *
                "$(E) with $(D)-degree operators $(length(operators) >= D ? operators[D] : ())",
            ),
        )
    end
    return insert_operator_index(op_idx, args, example_expr)
end

"""
    @declare_expression_operator(op, arity)

Declare an operator function for `AbstractExpression` types.

This macro generates methods for the given operator `op` that work with
`AbstractExpression` arguments.  The `arity` parameter specifies the number
of arguments the operator takes.
"""
macro declare_expression_operator(op, arity)
    syms = [Symbol('x', i) for i in 1:arity]
    AE = :($(AbstractExpression))
    macrocall(name, arg) = Expr(:macrocall, GlobalRef(Base, name), __source__, arg)
    nospecialize(arg) = macrocall(Symbol("@nospecialize"), arg)
    inline(fn) = macrocall(Symbol("@inline"), fn)
    if arity == 1
        return esc(inline(:(function $op($(nospecialize(:($(only(syms))::$(AE)))))
            return $(apply_operator)($op, $(only(syms)))
        end)))
    end

    wrappers = (AE, :($(AE){T}), :T, :Number)
    methods = Expr(:block)

    for types in Iterators.product(ntuple(_ -> wrappers, arity)...)
        has_expr = any(
            t -> t == AE || (t isa Expr && t.head == :curly && t.args[1] == AE), types
        )
        has_plain_T = any(==(:T), types)
        has_abstract_expr_T = any(
            t -> t isa Expr && t.head == :curly && t.args[1] == AE && :T in t.args, types
        )
        has_abstract_expr_plain = any(==(AE), types)
        if any((
            !has_expr,
            # ^At least one arg must be an AbstractExpression (avoid type‑piracy)
            has_abstract_expr_plain && has_abstract_expr_T,
            # ^If a plain `T` appears, ensure an `AbstractExpression{T}` is also present
            has_plain_T ⊻ has_abstract_expr_T,
            # ^Do not mix bare `AbstractExpression` with `AbstractExpression{T}`
        ))
            continue
        end

        arglist = [
            if t == AE || (t isa Expr && t.head == :curly && t.args[1] == AE)
                nospecialize(Expr(:(::), s, t))
            else
                Expr(:(::), s, t)
            end for (s, t) in zip(syms, types)
        ]
        signature = Expr(:call, op, arglist...)
        if any(t -> t == :T || (t isa Expr && t.head == :curly && :T in t.args), types)
            signature = Expr(:where, signature, :(T))
        end

        body = Expr(:block, :(return $(apply_operator)($op, $(syms...))))

        fn = Expr(:function, signature, body)

        push!(methods.args, inline(fn))
    end

    return esc(methods)
end

#! format: off
for op in (
    :sin, :cos, :tan, :sinh, :cosh, :tanh, :asin, :acos,
    :asinh, :acosh, :atanh, :sec, :csc, :cot, :asec, :acsc, :acot, :sech, :csch,
    :coth, :asech, :acsch, :acoth, :sinc, :cosc, :cosd, :cotd, :cscd, :secd,
    :sinpi, :cospi, :sind, :tand, :acosd, :acotd, :acscd, :asecd, :asind,
    :log, :log2, :log10, :log1p, :exp, :exp2, :exp10, :expm1, :frexp, :exponent,
    :float, :abs, :real, :imag, :conj, :unsigned,
    :nextfloat, :prevfloat, :transpose, :significand,
    :modf, :rem, :floor, :ceil, :round, :trunc,
    :inv, :sqrt, :cbrt, :abs2, :angle, :factorial,
    :(!), :-, :+, :sign, :identity,
)
    @eval @declare_expression_operator Base.$(op) 1
end
for op in (
    :*, :/, :+, :-, :^, :÷, :mod, :log,
    :atan, :atand, :copysign, :flipsign,
    :&, :|, :⊻, ://, :\, :rem,
    :(>), :(<), :(>=), :(<=), :max, :min,
)
    @eval @declare_expression_operator Base.$(op) 2
end
for op in (
    :*, :+, :clamp, :max, :min, :fma, :muladd,
)
    @eval @declare_expression_operator Base.$(op) 3
end
#! format: on

end
