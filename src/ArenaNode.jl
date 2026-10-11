module ArenaNodeModule

using DispatchDoctor: @unstable

using ..UtilsModule: Nullable, Undefined

import ..NodeModule:
    AbstractNode,
    AbstractExpressionNode,
    Node,
    unsafe_get_children,
    get_child,
    set_child!,
    set_children!,
    count_nodes,
    copy_node,
    tree_mapreduce,
    inner_is_equal,
    node_factory,
    default_allocator,
    defines_eltype,
    max_degree,
    constructorof
import ..NodeUtilsModule: count_constant_nodes, get_scalar_constants, set_scalar_constants!
import ..NodePreallocationModule: allocate_container, copy_into!
import ..ValueInterfaceModule: get_number_type

"""All per-node fields packed into a single isbits struct.

Storing nodes as one `Vector{ArenaEntry}` (array-of-structs) makes whole-tree
operations flat array operations: `copy` is a single `memcpy`, and traversals
touch one contiguous stream of memory.

Indices are `Int32` and are 1-based. A child index of `0` indicates an empty slot.
"""
struct ArenaEntry{T<:Number,D}
    val::T
    children::NTuple{D,Int32}
    feature::UInt16
    degree::UInt8
    op::UInt8
    constant::Bool
end

function _replace(
    entry::ArenaEntry{T,D};
    val=entry.val,
    children=entry.children,
    feature=entry.feature,
    degree=entry.degree,
    op=entry.op,
    constant=entry.constant,
) where {T,D}
    return ArenaEntry{T,D}(val, children, feature, degree, op, constant)
end

"""Array-backed arena storing the nodes of a tree contiguously.

This is an *experimental* arena-backed representation with a `Node`-like facade
(`ArenaNode`) that supports existing tree algorithms that are written against
`AbstractExpressionNode`.

The `compact` flag tracks whether `nodes` is exactly one postfix-ordered tree
(children stored before parents, root last, no orphaned nodes and no shared
subtrees). Trees built via `convert`/`copy` are compact; structural mutations
through the facade may clear the flag, in which case whole-tree operations fall
back to generic traversals. A structural `copy` re-compacts.

`Arena` implements the (1-based, linear) array interface over its entries, and
`setindex!` is how entries are mutated: it compares the old and new entry and
automatically clears `compact` whenever the structural fields (`degree`,
`children`) change. Non-structural writes (`val`/`op`/`feature`/`constant`)
preserve the flag, which keeps constant optimization on the fast paths. Only
this file's bulk copies and value-only updates write `arena.nodes` directly.
"""
mutable struct Arena{T<:Number,D} <: AbstractVector{ArenaEntry{T,D}}
    nodes::Vector{ArenaEntry{T,D}}
    compact::Bool
    # Exact buffer length; Base pads the growth of small vectors 3-4x.
    capacity::Int

    function Arena{T,D}(; capacity::Integer=0) where {T,D}
        return new{T,D}(_new_nodes(ArenaEntry{T,D}, capacity), true, capacity)
    end
end

# `Vector{E}(undef, n)` is the one Base constructor with an exact buffer size.
_new_nodes(::Type{E}, capacity) where {E} = resize!(Vector{E}(undef, capacity), 0)

# Single-entry pushes grow geometrically; subtree appends grow to the exact size.
function _reserve!(arena::Arena{T,D}, needed) where {T,D}
    needed <= arena.capacity && return arena
    return _grow!(arena, max(needed, arena.capacity + arena.capacity ÷ 2))
end
function _grow!(arena::Arena{T,D}, capacity) where {T,D}
    nodes = _new_nodes(ArenaEntry{T,D}, capacity)
    resize!(nodes, length(arena.nodes))
    copyto!(nodes, arena.nodes)
    arena.nodes = nodes
    arena.capacity = capacity
    return arena
end

# Mark/clear the one-postfix-tree invariant (root last, no orphans):
mark_compact!(arena::Arena) = (arena.compact = true; arena)
invalidate_compact!(arena::Arena) = (arena.compact = false; arena)
is_compact(arena::Arena) = arena.compact

Base.size(arena::Arena) = size(arena.nodes)
Base.IndexStyle(::Type{<:Arena}) = IndexLinear()
Base.@propagate_inbounds Base.getindex(arena::Arena, i::Integer) = arena.nodes[i]
Base.@propagate_inbounds function Base.setindex!(
    arena::Arena{T,D}, entry::ArenaEntry{T,D}, i::Integer
) where {T,D}
    nodes = arena.nodes
    old = nodes[i]
    if entry.degree != old.degree || entry.children != old.children
        invalidate_compact!(arena)
    end
    nodes[i] = entry
    return arena
end
function Base.push!(arena::Arena{T,D}, entry::ArenaEntry{T,D}) where {T,D}
    _reserve!(arena, length(arena.nodes) + 1)
    nodes = arena.nodes
    # A single leaf in a fresh arena is a valid tree; any further append breaks
    # the one-postfix-tree invariant until a builder re-establishes it.
    isempty(nodes) || invalidate_compact!(arena)
    push!(nodes, entry)
    return arena
end

"""A lightweight facade for a node stored in an [`Arena`](@ref).

This wrapper is intentionally minimal: it stores an arena reference and an index.
Core fields are accessed and mutated via `getproperty`/`setproperty!`.

!!! warning
    Unlike `Node`, attaching a child from a *different* arena
    (`set_child!`/`set_children!`) copies the subtree into the parent's arena:
    the original handle stays attached to its own arena, so later mutations
    through it do not affect the new parent. Same-arena attachments keep
    reference semantics. Keyword construction (`ArenaNode(; op, children)`, and
    so operator overloads like `a + b`) places the new node in the arena of its
    first `ArenaNode` child, so that child attaches by reference and the others
    are copied. That arena grows with every node built on top of it, and building
    from one `ArenaNode` on several threads at once is a data race.
"""
struct ArenaNode{T<:Number,D} <: AbstractExpressionNode{T,D}
    arena::Arena{T,D}
    idx::Int32

    # Typed `arena`, so it does not overlap the generic two-argument constructors
    # such as `(::Type{N})(op::Integer, l::AbstractExpressionNode)`.
    function ArenaNode{T,D}(arena::Arena{T,D}, idx::Integer) where {T,D}
        return new{T,D}(arena, idx)
    end
end

ArenaNode(arena::Arena{T,D}, idx::Integer) where {T,D} = ArenaNode{T,D}(arena, idx)

# The generic `constructorof` leaves `T` unbounded, violating `T<:Number`. Generating
# the bounded type makes it a compile-time constant rather than a per-call allocation.
@generated function constructorof(::Type{N}) where {N<:ArenaNode}
    return ArenaNode{T,max_degree(N)} where {T<:Number}
end

# The only sanctioned `getfield` sites: internal code uses these instead of
# property access so that functions reachable from `getproperty` (e.g.
# `get_child` via the `:l`/`:r` branches) do not cycle back into it.
get_arena(node::ArenaNode) = getfield(node, :arena)
get_index(node::ArenaNode) = getfield(node, :idx)

# Entry behind a facade. A zero index is a poison facade (an unset child
# slot); accessing it throws like reading an undefined `Node` field.
function _load_entry(arena::Arena, idx::Int32)
    iszero(idx) && throw(UndefRefError())
    return @inbounds arena.nodes[idx]
end

# True when the arena contents *are* `tree`: compact, rooted at the last entry.
function is_compact_root(tree::ArenaNode)
    arena = get_arena(tree)
    return is_compact(arena) && get_index(tree) == length(arena.nodes)
end

_zero_children(::Val{D}) where {D} = ntuple(_ -> Int32(0), Val(D))

function _push_node!(
    arena::Arena{T,D};
    degree=0,
    constant=false,
    val=zero(T),
    feature=0,
    op=0,
    children=_zero_children(Val(D)),
) where {T,D}
    push!(arena, ArenaEntry{T,D}(val, children, feature, degree, op, constant))
    return Int32(length(arena))
end

push_constant!(arena::Arena, value) = _push_node!(arena; constant=true, val=value)
push_feature!(arena::Arena, feature::Integer) = _push_node!(arena; feature)

# Default node: a zero constant leaf in its own fresh arena.
function ArenaNode{T,D}() where {T,D}
    arena = Arena{T,D}(; capacity=1)
    idx = push_constant!(arena, zero(T))
    return ArenaNode{T,D}(arena, idx)
end

Base.@constprop :aggressive @inline function Base.getproperty(
    node::ArenaNode{T}, property_name::Symbol
) where {T}
    if property_name === :arena
        return get_arena(node)
    elseif property_name === :idx
        return get_index(node)
    elseif property_name === :children
        return unsafe_get_children(node)
    elseif property_name === :l
        return get_child(node, 1)
    elseif property_name === :r
        return get_child(node, 2)
    end
    entry = _load_entry(get_arena(node), get_index(node))
    if property_name === :degree
        return entry.degree
    elseif property_name === :constant
        return entry.constant
    elseif property_name === :val
        return entry.val::T
    elseif property_name === :feature
        return entry.feature
    elseif property_name === :op
        return entry.op
    else
        return getfield(node, property_name)
    end
end

@inline function Base.setproperty!(node::ArenaNode, property_name::Symbol, value)
    arena = get_arena(node)
    i = get_index(node)
    entry = _load_entry(arena, i)
    if property_name === :degree
        @inbounds arena[i] = _replace(entry; degree=value)
    elseif property_name === :constant
        @inbounds arena[i] = _replace(entry; constant=value)
    elseif property_name === :val
        @inbounds arena[i] = _replace(entry; val=value)
    elseif property_name === :feature
        @inbounds arena[i] = _replace(entry; feature=value)
    elseif property_name === :op
        @inbounds arena[i] = _replace(entry; op=value)
    elseif property_name === :l
        set_child!(node, value, 1)
    elseif property_name === :r
        set_child!(node, value, 2)
    else
        throw(ArgumentError("Unsupported field $property_name for ArenaNode"))
    end
    return value
end

function _nullable_child(
    node::ArenaNode{T,D}, child_idx::Int32
)::Nullable{ArenaNode{T,D}} where {T,D}
    child = ArenaNode{T,D}(get_arena(node), child_idx)
    return Nullable{ArenaNode{T,D}}(iszero(child_idx), child)
end

# Children as `Nullable` wrappers; unused slots are poison nodes (like `Node`),
# so accessing them throws an `UndefRefError`.
@generated function unsafe_get_children(node::ArenaNode{T,D}) where {T,D}
    quote
        $(Expr(:meta, :inline))
        children = _load_entry(get_arena(node), get_index(node)).children
        return Base.Cartesian.@ntuple($D, j -> _nullable_child(node, children[j]))
    end
end

function get_child(node::ArenaNode{T,D}, i::Int) where {T,D}
    # Avoid routing through getproperty here: the :l/:r property branches call
    # get_child, and the resulting inference cycle widens property access.
    arena = get_arena(node)
    entry = _load_entry(arena, get_index(node))
    child_idx = entry.children[i]  # bounds-checked: i > D must throw, not crash
    iszero(child_idx) && throw(UndefRefError())
    return ArenaNode{T,D}(arena, child_idx)
end

# Same-arena children attach by index; anything else is copied into `node`'s
# arena, since arenas cannot link across each other.
function _resolve_child_index!(node::ArenaNode{T,D}, child) where {T,D}
    child isa AbstractExpressionNode{T,D} || throw(
        ArgumentError(
            "ArenaNode children must be AbstractExpressionNode{$T,$D} (got $(typeof(child)))",
        ),
    )
    if child isa ArenaNode{T,D} && get_arena(child) === get_arena(node)
        return get_index(child)
    else
        return _copy_to_arena!(get_arena(node), child)
    end
end

function set_child!(node::ArenaNode{T,D}, child::AbstractNode{D}, i::Int) where {T,D}
    arena = get_arena(node)
    entry = @inbounds arena[get_index(node)]
    1 <= i <= D || throw(BoundsError(entry.children, i))
    idx = _resolve_child_index!(node, child)
    if @inbounds(entry.children[i]) != idx
        @inbounds arena[get_index(node)] = _replace(
            entry; children=Base.setindex(entry.children, idx, i)
        )
    end
    return ArenaNode{T,D}(arena, idx)
end

function set_children!(
    node::ArenaNode{T,D}, children::Union{Tuple,AbstractVector{<:AbstractNode{D}}}
) where {T,D}
    D2 = length(children)
    idxs = _zero_children(Val(D))
    @inbounds for i in 1:min(D, D2)
        child = children[i]
        if child isa Nullable
            child.null && continue
            child = child[]
        end
        idxs = Base.setindex(idxs, _resolve_child_index!(node, child), i)
    end

    arena = get_arena(node)
    entry = @inbounds arena[get_index(node)]
    @inbounds arena[get_index(node)] = _replace(entry; children=idxs)
    return nothing
end

# An operator node built from children (`ArenaNode(; op, children)`) lives in
# the arena of its first `ArenaNode` child, so that child attaches by reference
# (as with `Node`) and only the remaining children are copied in. A custom
# allocator keeps the generic path.
@inline function node_factory(
    ::Type{N},
    ::Type,
    ::Nothing,
    ::Nothing,
    op::Integer,
    children::Union{Tuple,AbstractVector},
    ::typeof(default_allocator),
) where {N<:ArenaNode}
    T = defines_eltype(N) ? eltype(N) : promote_type(map(eltype, children)...)
    defines_eltype(N) && @assert T === promote_type(T, map(eltype, children)...)
    D = max_degree(N)
    D2 = length(children)
    @assert D2 <= D
    arena = _home_arena(ArenaNode{T,D}, children)
    idx = _push_node!(arena; degree=D2, op)
    node = ArenaNode{T,D}(arena, idx)
    set_children!(node, children)
    return node
end
function _home_arena(::Type{ArenaNode{T,D}}, children) where {T,D}
    for child in children
        child isa ArenaNode{T,D} && return get_arena(child)
    end
    return Arena{T,D}(; capacity=D + 1)
end

# Append `idx`'s subtree (children first, root last) to `dest`, returning the
# root's new index. Works directly on entries, without facade traversal, so
# copying out of a non-compact arena stays an array operation. `dest` must
# already have room for the subtree at `cursor + 1` onward.
# `@unstable` (here and below): DispatchDoctor's check cannot fold inside recursion.
@unstable function _write_subtree!(
    dest::Vector{ArenaEntry{T,D}}, src::Vector{ArenaEntry{T,D}}, idx, cursor
) where {T,D}
    iszero(idx) && throw(UndefRefError())  # unset child slot, like Node
    entry = @inbounds src[idx]
    if !iszero(entry.degree)
        children = _zero_children(Val(D))
        @inbounds for j in 1:(entry.degree)
            child_idx, cursor = _write_subtree!(dest, src, entry.children[j], cursor)
            children = Base.setindex(children, child_idx, j)
        end
        entry = _replace(entry; children)
    end
    cursor += 1
    @inbounds dest[cursor] = entry
    return Int32(cursor), cursor
end

@unstable function _subtree_count(src::Vector{<:ArenaEntry}, idx)
    iszero(idx) && throw(UndefRefError()) # unset child slot, like Node
    entry = @inbounds src[idx]
    n = 1
    @inbounds for j in 1:(entry.degree)
        n += _subtree_count(src, entry.children[j])
    end
    return n
end

# `src` may be `dest`'s own entries: reads are below the original length and
# writes at or above `cursor`, so the regions never overlap (and `_grow!`
# leaves the old buffer intact for reading if it reallocates).
function _append_subtree!(
    dest::Arena{T,D}, src::Vector{ArenaEntry{T,D}}, idx, n=_subtree_count(src, idx)
) where {T,D}
    cursor = length(dest.nodes)
    cursor + n > dest.capacity && _grow!(dest, cursor + n)
    nodes = dest.nodes
    resize!(nodes, cursor + n)
    root_idx, _ = _write_subtree!(nodes, src, idx, cursor)
    return root_idx
end

# Flat copy of a compact arena: child indices stay valid verbatim.
function _copy_entries!(dest::Arena, src_nodes)
    _reserve!(dest, length(src_nodes))
    resize!(dest.nodes, length(src_nodes))
    copyto!(dest.nodes, src_nodes)
    return mark_compact!(dest)
end

# Copies and preallocated containers leave room for one more operator node
# with its leaves (`D + 1` entries), so one in-place edit after a copy does not
# reallocate.
_edit_headroom(n::Integer, ::Val{D}) where {D} = n + D + 1

# Compact arenas copy as one flat array copy; otherwise the subtree is appended
# entry-by-entry into a fresh arena, which also re-compacts. Overloads
# `copy_node` (not `Base.copy`) since that is the generic entry point.
function copy_node(tree::ArenaNode{T,D}; break_sharing::Val{BS}=Val(false)) where {T,D,BS}
    arena = get_arena(tree)
    if is_compact_root(tree)
        n = length(arena.nodes)
        dest = Arena{T,D}(; capacity=_edit_headroom(n, Val(D)))
        _copy_entries!(dest, arena.nodes)
        return ArenaNode{T,D}(dest, get_index(tree))
    end
    n = _subtree_count(arena.nodes, get_index(tree))
    dest = Arena{T,D}(; capacity=_edit_headroom(n, Val(D)))
    idx = _append_subtree!(dest, arena.nodes, get_index(tree), n)
    return ArenaNode{T,D}(dest, idx)
end

# Preallocated arena for `copy_into!`, enabling zero-allocation copies.
function allocate_container(
    prototype::ArenaNode{T,D}, num_nodes::Union{Nothing,Integer}=nothing
) where {T,D}
    return Arena{T,D}(;
        capacity=_edit_headroom(@something(num_nodes, length(prototype)), Val(D))
    )
end

# Reuses `dest`'s storage, so a copy allocates nothing once `dest` is large enough.
function copy_into!(
    dest::Arena{T,D},
    src::ArenaNode{T,D};
    ref::Union{Nothing,Base.RefValue{<:Integer}}=nothing,
) where {T,D}
    set_ref!(n) = ref === nothing ? nothing : (ref[] = n)
    if dest === get_arena(src)
        # Container reuse: the tree already lives in `dest`. A compact root is
        # a no-op; otherwise compact through a temporary copy.
        if is_compact_root(src)
            set_ref!(length(src))
            return src
        end
        src = copy_node(src)
    end
    if is_compact_root(src)
        _copy_entries!(dest, get_arena(src).nodes)
        set_ref!(length(src))
        return ArenaNode{T,D}(dest, get_index(src))
    end
    empty!(dest.nodes)
    idx = _append_subtree!(dest, get_arena(src).nodes, get_index(src))
    mark_compact!(dest)
    set_ref!(length(dest.nodes))
    return ArenaNode{T,D}(dest, idx)
end

function _copy_to_arena!(arena::Arena{T,D}, tree::ArenaNode{T,D}) where {T,D}
    invalidate_compact!(arena)
    return _append_subtree!(arena, get_arena(tree).nodes, get_index(tree))
end
# Shared subtrees are copied once per parent, since arena trees do not share.
function _copy_to_arena!(
    arena::Arena{T,D}, tree::AbstractExpressionNode{<:Any,D}
) where {T,D}
    return tree_mapreduce(
        leaf -> _push_leaf!(arena, leaf),
        identity,
        (branch, children...) -> _push_branch!(arena, branch, children),
        tree,
        Int32;
        break_sharing=Val(true),
    )
end
function _push_leaf!(arena::Arena, leaf)
    leaf.constant && return push_constant!(arena, leaf.val)
    return push_feature!(arena, leaf.feature)
end
function _push_branch!(arena::Arena{T,D}, branch, children::Tuple) where {T,D}
    padded = ntuple(i -> get(children, i, Int32(0)), Val(D))
    return _push_node!(arena; degree=length(children), op=branch.op, children=padded)
end

# Copy the tree into a fresh arena, in postfix (children-first) order.
function Base.convert(
    ::Type{ArenaNode{T,D}}, tree::AbstractExpressionNode{<:Any,D}
) where {T,D}
    arena = Arena{T,D}(; capacity=length(tree; break_sharing=Val(true)))
    idx = _copy_to_arena!(arena, tree)
    mark_compact!(arena)
    return ArenaNode{T,D}(arena, idx)
end
Base.convert(::Type{ArenaNode{T,D}}, tree::ArenaNode{T,D}) where {T,D} = tree

# Cross-representation comparisons (`==` promotes its arguments) promote
# toward the arena representation.
function Base.promote_rule(::Type{ArenaNode{T1,D}}, ::Type{Node{T2,D}}) where {T1,T2,D}
    return ArenaNode{promote_type(T1, T2),D}
end
function Base.promote_rule(::Type{ArenaNode{T1,D}}, ::Type{ArenaNode{T2,D}}) where {T1,T2,D}
    return ArenaNode{promote_type(T1, T2),D}
end

################################################################################
# Flat whole-tree operations
#
# For a compact arena the node array *is* the tree, so tree-wide reductions
# become linear array scans with no pointer chasing. Each of these falls back
# to the generic traversal-based implementation when the invariant doesn't hold.
################################################################################

# The single iteration driver for order-free whole-tree visits.
# `visit(node, entry)` receives the facade and the already-loaded entry, and
# returns true to stop early (the driver then returns true).
function _foreach_node(visit::F, tree::ArenaNode) where {F<:Function}
    arena = get_arena(tree)
    if is_compact_root(tree)
        return _foreach_in_storage_order(visit, arena, get_index(tree))
    else
        return _foreach_preorder(visit, arena, get_index(tree))
    end
end

# A compact arena is the tree, so it is walked as an array (leaves first).
function _foreach_in_storage_order(visit::F, arena::Arena, root::Int32) where {F<:Function}
    @inbounds for i in Base.OneTo(root)
        @inline(visit(ArenaNode(arena, i), arena.nodes[i])) && return true
    end
    return false
end

# Unrolled per degree like the generic `any`, so the walk stays as fast as Node's.
@generated function _foreach_preorder(
    visit::F, arena::Arena{T,D}, root::Int32
) where {F<:Function,T,D}
    quote
        entry = _load_entry(arena, root)
        @inline(visit(ArenaNode(arena, root), entry)) && return true
        degree = entry.degree
        iszero(degree) && return false
        children = entry.children
        return Base.Cartesian.@nif(
            $D,
            i -> degree == i,  # COV_EXCL_LINE
            i -> Base.Cartesian.@nany(  # COV_EXCL_LINE
                i,
                j -> _foreach_preorder(visit, arena, children[j])  # COV_EXCL_LINE
            ),
        )
    end
end

# `val` is compared with `==` (not bitwise) to keep the -0.0 == 0.0 and
# NaN != NaN semantics of the structural fallback.
function _entries_equal(a::ArenaEntry, b::ArenaEntry)
    a.degree == b.degree || return false
    if iszero(a.degree)
        return a.constant == b.constant &&
               (a.constant ? a.val == b.val : a.feature == b.feature)
    else
        return a.op == b.op && a.children == b.children
    end
end

# Equal compact trees have identical entry vectors (same layout, same child
# indices), so equality is a flat field-compare.
function Base.:(==)(a::ArenaNode{T,D}, b::ArenaNode{T,D})::Bool where {T,D}
    if is_compact_root(a) && is_compact_root(b)
        nodes_a = get_arena(a).nodes
        nodes_b = get_arena(b).nodes
        length(nodes_a) == length(nodes_b) || return false
        @inbounds for i in eachindex(nodes_a)
            _entries_equal(nodes_a[i], nodes_b[i]) || return false
        end
        return true
    end
    return inner_is_equal(a, b, nothing)  # preserve_sharing is false
end

function count_nodes(tree::ArenaNode; break_sharing::Val{BS}=Val(false)) where {BS}
    is_compact_root(tree) && return length(get_arena(tree).nodes)
    return tree_mapreduce(Returns(1), +, tree, Int)
end

function count_constant_nodes(tree::ArenaNode)
    if is_compact_root(tree)
        return count(entry -> iszero(entry.degree) && entry.constant, get_arena(tree).nodes)
    end
    return invoke(count_constant_nodes, Tuple{AbstractExpressionNode}, tree)
end

# Reads each entry once. Recursive so that `f_leaf`/`f_branch` run parent-first,
# siblings left to right, as with Node. Sharing kwargs are ignored, since
# ArenaNode never shares.
function tree_mapreduce(
    f_leaf::F1,
    f_branch::F2,
    op::G,
    tree::ArenaNode{T,D},
    result_type::Type{RT}=Undefined;
    f_on_shared::H=(result, is_shared) -> result,
    break_sharing::Val{BS}=Val(false),
) where {T,D,F1<:Function,F2<:Function,G<:Function,H<:Function,RT,BS}
    return _entry_mapreduce(f_leaf, f_branch, op, get_arena(tree), get_index(tree))
end

@generated function _entry_mapreduce(
    f_leaf::F1, f_branch::F2, op::G, arena::Arena{T,D}, idx::Int32
) where {F1<:Function,F2<:Function,G<:Function,T,D}
    quote
        entry = _load_entry(arena, idx)
        node = ArenaNode{T,D}(arena, idx)
        degree = entry.degree
        iszero(degree) && return @inline(f_leaf(node))
        branch = @inline(f_branch(node))
        return Base.Cartesian.@nif(
            $D,
            i -> degree == i,  # COV_EXCL_LINE
            i -> @inline(  # COV_EXCL_LINE
                op(
                    branch,
                    Base.Cartesian.@ntuple(
                        i,
                        j -> _entry_mapreduce(  # COV_EXCL_LINE
                            f_leaf,
                            f_branch,
                            op,
                            arena,
                            entry.children[j],
                        )
                    )...,
                )
            ),
        )
    end
end

function Base.any(f::F, tree::ArenaNode{T,D}) where {F<:Function,T,D}
    return _foreach_node((node, _) -> @inline(f(node)), tree)
end

# Constants as plain Int32 arena indices (also valid in flat copies). Both
# walks visit leaves left to right, so the order matches Node's.
function get_scalar_constants(
    tree::ArenaNode{T}, ::Type{BT}=get_number_type(T)
) where {T<:Number,BT}
    arena = get_arena(tree)
    refs = Int32[]
    _foreach_node(tree) do node, entry
        if iszero(entry.degree) && entry.constant
            push!(refs, get_index(node))
        end
        return false
    end
    vals = T[@inbounds(arena[i].val) for i in refs]
    return vals, refs
end

function set_scalar_constants!(
    tree::ArenaNode{T}, constants, refs::AbstractVector{Int32}
) where {T<:Number}
    # Val-only writes cannot change structure, so they go to the entries
    # directly, skipping `setindex!`'s degree/children diff.
    nodes = get_arena(tree).nodes
    @inbounds for j in eachindex(refs, constants)
        i = refs[j]
        nodes[i] = _replace(nodes[i]; val=constants[j])
    end
    return tree
end

end
