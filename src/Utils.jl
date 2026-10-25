"""Useful functions to be used throughout the library."""
module UtilsModule

using MacroTools: postwalk, @capture, splitdef, combinedef
using DispatchDoctor: @unstable
import ..ValueInterfaceModule: invalid_value

# Returns two arrays
macro return_on_false2(flag, retval, retval2)
    :(
        if !$(esc(flag))
            return ($(esc(retval)), $(esc(retval2)), false)
        end
    )
end

@inline function fill_similar(value::T, array, args...) where {T}
    out_array = similar(array, args...)
    fill!(out_array, value)
    return out_array
end

function deprecate_varmap(variable_names, varMap, func_name)
    if varMap !== nothing
        Base.depwarn("`varMap` is deprecated; use `variable_names` instead", func_name)
        @assert variable_names === nothing "Cannot pass both `varMap` and `variable_names`"
        variable_names = varMap
    end
    return variable_names
end

# Whether values of a type are immutable all the way down, so copying can share them.
# Taken from BorrowChecker.jl's `is_static`.
@inline function _is_static(::Type{T})::Bool where {T}
    if isbitstype(T)
        return true
    elseif T isa UnionAll || T === Union{}
        return false
    elseif isstructtype(T) && ismutabletype(T)
        return false
    elseif T isa Union
        return _is_static(T.a) && _is_static(T.b)
    elseif !(T isa DataType)
        return false
    elseif Base.datatype_fieldcount(T) === nothing
        return false
    else
        return all(_is_static, fieldtypes(T))
    end
end
_is_static(::Type{<:Type}) = true
_is_static(::Type{Symbol}) = true
_is_static(::Type{String}) = true
_is_static(::Type{Module}) = true
_is_static(::T) where {T} = _is_static(T)

# These are marked unstable due to issues discussed on
# https://github.com/JuliaLang/julia/issues/55147
@unstable counttuple(::Type{<:NTuple{N,Any}}) where {N} = N

"""
    nif_expr(n, index, branch)

Build the expression of `Base.Cartesian.@nif(n, i -> i == index, branch)`, where
`branch(i)` returns the expression for `i`.
"""
function nif_expr(n::Integer, index::Symbol, branch::F) where {F}
    ex = branch(n)
    for i in (n - 1):-1:1
        ex = Expr(:if, :($i == $index), branch(i), ex)
    end
    return ex
end

"""
    Undefined

Just a type like `Nothing` to differentiate from a literal `Nothing`.
"""
struct Undefined end

"""
    ResultOk{A}

Stores the result of an evaluation and whether
any errors occured during the evaluation. This
is used to quit early, so that we do not pass
`Inf` to `cos` (for example).
"""
struct ResultOk{A}
    x::A
    ok::Bool
end

struct ResultOk2{A<:AbstractArray,B<:AbstractArray}
    x::A
    dx::B
    ok::Bool
end

struct Nullable{T}
    null::Bool
    x::T
end
@inline function Base.getindex(x::Nullable)
    x.null && throw(UndefRefError())
    return x.x
end
@inline function Base.convert(::Type{Nullable{T}}, x::Nullable) where {T}
    return Nullable(x.null, convert(T, x.x))
end

function set_invalid!(out)
    fill!(out, invalid_value(eltype(out)))
    return nothing
end

end
