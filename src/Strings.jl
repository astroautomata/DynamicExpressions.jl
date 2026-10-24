module StringsModule

using ..UtilsModule: deprecate_varmap, nif_expr
using ..OperatorEnumModule: AbstractOperatorEnum
using ..NodeModule: AbstractExpressionNode, tree_mapreduce, max_degree

function dispatch_op_name(
    ::Val{deg}, ::Nothing, idx, pretty::Bool
)::Vector{Char} where {deg}
    return vcat(collect(
        if deg == 1
            "unary_operator["
        elseif deg == 2
            "binary_operator["
        else
            "operator_deg$deg["
        end,
    ), collect(string(idx)), [']'])
end
function dispatch_op_name(
    ::Val{deg}, @nospecialize(operators::AbstractOperatorEnum), idx, pretty::Bool
) where {deg}
    op = operators[deg][idx]
    return collect((pretty ? get_pretty_op_name(op) : get_op_name(op))::String)
end

# Names are looked up once per distinct operator, since the lookup is dynamically
# dispatched to avoid compiling it for every operator set.
struct OpNameDispatcher{D} <: Function
    operators::Union{AbstractOperatorEnum,Nothing}
    pretty::Bool
    names::Dict{Tuple{Int,Int},Vector{Char}}
end
function OpNameDispatcher{D}(
    @nospecialize(operators::Union{AbstractOperatorEnum,Nothing}), pretty::Bool
) where {D}
    return OpNameDispatcher{D}(operators, pretty, Dict{Tuple{Int,Int},Vector{Char}}())
end
@generated function (f::OpNameDispatcher{D})(branch) where {D}
    return quote
        degree = branch.degree
        key = (Int(degree), Int(branch.op))
        name = get(f.names, key, nothing)
        if name === nothing
            name = $(nif_expr(
                D,
                :degree,
                d -> :(dispatch_op_name(Val($d), f.operators, branch.op, f.pretty)),
            ))::Vector{Char}
            f.names[key] = name
        end
        return name
    end
end

const OP_NAME_CACHE = (; x=Dict{UInt64,String}(), lock=Threads.SpinLock())

function get_op_name(@nospecialize(op))
    # Only singleton callables have a fixed name.
    Base.issingletontype(typeof(op)) && return @lock OP_NAME_CACHE.lock get!(
        () -> _get_op_name(op), OP_NAME_CACHE.x, objectid(op)
    )
    return _get_op_name(op)
end
function _get_op_name(@nospecialize(op))
    if op isa Broadcast.BroadcastFunction
        base_op_s = string(op.f)
        if length(base_op_s) == 1 && first(base_op_s) in ('+', '-', '*', '/', '^')
            # Like `.+`
            return string('.', base_op_s)
        else
            # Like `cos.`
            return string(base_op_s, '.')
        end
    else
        return string(op)
    end
end
function get_pretty_op_name(@nospecialize(op))
    return get_op_name(op)
end

@inline function strip_brackets(s::Vector{Char})
    if first(s) == '(' && last(s) == ')'
        return s[(begin + 1):(end - 1)]
    else
        return s
    end
end

# Can overload these for custom behavior:
# COV_EXCL_START
needs_brackets(val::Real) = false
needs_brackets(val::AbstractArray) = false
needs_brackets(val::Complex) = true
needs_brackets(val) = true
# COV_EXCL_STOP

function string_constant(val)
    if needs_brackets(val)
        '(' * string(val) * ')'
    else
        string(val)
    end
end

function string_variable(feature, variable_names)
    if variable_names === nothing ||
        feature > lastindex(variable_names) ||
        feature < firstindex(variable_names)
        return 'x' * string(feature)
    else
        return variable_names[feature]
    end
end

# Vector of chars is faster than strings, so we use that.
function combine_op_with_inputs(op, args::Vararg{Any,D})::Vector{Char} where {D}
    if D == 2 && (first(op) in ('+', '-', '*', '/', '^', '.', '>', '<', '=') || op == "!=")
        # "(l op r)"
        out = ['(']
        # `-a ^ b` parses as `-(a ^ b)`, so a negative base needs brackets.
        signed_base = last(op) == '^' && first(args[1]) == '-'
        signed_base && push!(out, '(')
        append!(out, args[1])
        signed_base && push!(out, ')')
        push!(out, ' ')
        append!(out, op)
        push!(out, ' ')
        append!(out, args[2])
        push!(out, ')')
    else
        # "op(l, r)"
        out = copy(op)
        push!(out, '(')
        for i in 1:(D - 1)
            append!(out, strip_brackets(args[i]))
            push!(out, ',')
            push!(out, ' ')
        end
        append!(out, strip_brackets(args[D]))
        push!(out, ')')
        return out
    end
end

"""
    string_tree(
        tree::AbstractExpressionNode{T},
        operators::Union{AbstractOperatorEnum,Nothing}=nothing;
        f_variable::F1=string_variable,
        f_constant::F2=string_constant,
        variable_names::Union{Array{String,1},Nothing}=nothing,
        # Deprecated
        varMap=nothing,
    )::String where {T,F1<:Function,F2<:Function}

Convert an equation to a string.

# Arguments
- `tree`: the tree to convert to a string
- `operators`: the operators used to define the tree

# Keyword Arguments
- `f_variable`: (optional) function to convert a variable to a string, with arguments `(feature::UInt8, variable_names)`.
- `f_constant`: (optional) function to convert a constant to a string, with arguments `(val,)`
- `variable_names::Union{Array{String, 1}, Nothing}=nothing`: (optional) what variables to print for each feature.
"""
Base.@nospecializeinfer function string_tree(
    tree::AbstractExpressionNode{T},
    @nospecialize(operators::Union{AbstractOperatorEnum,Nothing} = nothing);
    f_variable::F1=string_variable,
    f_constant::F2=string_constant,
    variable_names=nothing,
    pretty::Union{Bool,Nothing}=nothing, # Not used, but can be used by other types
    # Deprecated
    raw::Union{Bool,Nothing}=nothing,
    varMap=nothing,
)::String where {T,F1<:Function,F2<:Function}
    if !isnothing(raw)
        Base.depwarn("`raw` is deprecated; use `pretty` instead", :string_tree)  # COV_EXCL_LINE
    end
    pretty = @something(pretty, _not(raw), false)
    variable_names = deprecate_varmap(variable_names, varMap, :string_tree)
    raw_output = tree_mapreduce(
        let f_constant = f_constant,
            f_variable = f_variable,
            variable_names = variable_names

            (leaf,) -> if leaf.constant
                collect(f_constant(leaf.val))::Vector{Char}
            else
                collect(f_variable(leaf.feature, variable_names))::Vector{Char}
            end
        end,
        OpNameDispatcher{max_degree(tree)}(operators, pretty),
        combine_op_with_inputs,
        tree,
        Vector{Char};
        f_on_shared=(c, is_shared) -> if is_shared
            out = ['{']
            append!(out, c)
            push!(out, '}')
            out
        else
            c
        end,
    )
    return String(strip_brackets(raw_output))
end

# Print an equation
for io in ((), (:(io::IO),))
    @eval function print_tree(
        $(io...),
        tree::AbstractExpressionNode,
        @nospecialize(operators::Union{AbstractOperatorEnum,Nothing} = nothing);
        f_variable::F1=string_variable,
        f_constant::F2=string_constant,
        variable_names=nothing,
        pretty::Union{Bool,Nothing}=nothing, # Not used, but can be used by other types
        # Deprecated
        raw::Union{Bool,Nothing}=nothing,
        varMap=nothing,
    ) where {F1<:Function,F2<:Function}
        !isnothing(raw) &&
            Base.depwarn("`raw` is deprecated; use `pretty` instead", :print_tree)
        pretty = @something(pretty, _not(raw), false)
        variable_names = deprecate_varmap(variable_names, varMap, :print_tree)
        return println(
            $(io...),
            string_tree(tree, operators; f_variable, f_constant, variable_names, pretty),
        )
    end
end
_not(::Nothing) = nothing  # COV_EXCL_LINE
_not(x) = !x  # COV_EXCL_LINE

end
