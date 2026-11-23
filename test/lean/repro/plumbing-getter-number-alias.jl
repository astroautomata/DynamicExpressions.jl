using DynamicExpressions

mutable struct PlumbingMutableNumber <: Number
    value::Float64
end
Base.isfinite(x::PlumbingMutableNumber) = isfinite(x.value)
Base.zero(::Type{PlumbingMutableNumber}) = PlumbingMutableNumber(0.0)

# This is an alias-free one-leaf tree with a finite numeric value. The returned
# vector is new, but the mutable Number inside it is the original value object.
original = PlumbingMutableNumber(2.0)
tree = Node(PlumbingMutableNumber; val=original)
values, refs = DynamicExpressions.get_constants(tree)
@assert length(values) == 1 && length(refs) == 1
@assert values[1] === tree.val === original
values[1].value = 7.0
@assert tree.val.value == 7.0 && original.value == 7.0
println("CHECKED plumbing mutable-number getter element exposure")
