import DynExpr.Arena.Storage

namespace DynExpr.Arena

-- iszero(idx) && throw(UndefRefError())
-- entry = @inbounds src[idx]
-- n = 1
-- @inbounds for j in 1:(entry.degree)
--     n += _subtree_count(src, entry.children[j])
-- end
-- return n
/-- `465d0ec1:src/ArenaNode.jl:366-374`. Fuel is the source length: on an
acyclic input no path can visit more distinct entries. -/
def subtreeCount (src : Store T) : Nat → Int32 → Jl Nat
  | 0, _ => .error (.undefinedBehavior "arena cycle")
  | fuel + 1, i => do
    let e ← loadEntry src i
    let children ← e.active
    children.foldlM (fun n j => do return n + (← subtreeCount src fuel j)) 1

-- entry = @inbounds src[idx]
-- if !iszero(entry.degree)
--     children = _zero_children(Val(D))
--     @inbounds for j in 1:(entry.degree)
--         child_idx, cursor = _write_subtree!(dest, src, entry.children[j], cursor)
--         children = Base.setindex(children, child_idx, j)
--     end
--     entry = _replace(entry; children)
-- end
-- cursor += 1
-- @inbounds dest[cursor] = entry
-- return Int32(cursor), cursor
/-- `465d0ec1:src/ArenaNode.jl:348-364`. Only branch entries have their child
slots rewritten. Child slots of copied leaves are inactive. -/
def writeSubtree (src : Store T) (d : Nat) : Nat → Int32 →
    Array (Option (Entry T)) → Nat → Jl (Array (Option (Entry T)) × Int32 × Nat)
  | 0, _, _, _ => .error (.undefinedBehavior "arena cycle")
  | fuel + 1, i, dest, cursor => do
    let e ← loadEntry src i
    let (dest, cursor, e) ← if e.degree == 0 then pure (dest, cursor, e) else do
      let children ← e.active
      let (dest, cursor, children) ← children.zipIdx.foldlM
        (fun (dst, pos, slots) (j, k) => do
          let (dst, j', pos) ← writeSubtree src d fuel j dst pos
          if k ≥ slots.size then throw (.boundsError)
          return (dst, pos, slots.set! k j')) (dest, cursor, zeros d)
      pure (dest, cursor, { e with children })
    if cursor ≥ dest.size then throw (.undefinedBehavior "arena destination")
    let j ← checkedIndex (cursor + 1 : Nat)
    return (dest.set! cursor (some e), j, cursor + 1)

-- cursor = length(dest.nodes)
-- cursor + n > dest.capacity && _grow!(dest, cursor + n)
-- nodes = dest.nodes
-- resize!(nodes, cursor + n)
-- root_idx, _ = _write_subtree!(nodes, src, idx, cursor)
-- return root_idx
/-- `465d0ec1:src/ArenaNode.jl:376-385`. Source denotes the vector captured before
possible destination growth. Same-arena copying first snapshots the source. -/
def appendSubtree (dest src : Store T) (d : Nat) (i : Int32) (count : Option Nat := none) :
    Jl (Store T × Int32) := do
  let n ← match count with
    | some n => pure n
    | none => subtreeCount src src.nodes.size i
  let cursor := dest.nodes.size
  let dest := if cursor + n > dest.capacity then grow dest (cursor + n) else dest
  let (nodes, i, _) ← writeSubtree src d src.nodes.size i
    (dest.nodes ++ Array.replicate n none) cursor
  return ({ dest with nodes }, i)

-- _reserve!(dest, length(src_nodes))
-- resize!(dest.nodes, length(src_nodes))
-- copyto!(dest.nodes, src_nodes)
-- return mark_compact!(dest)
/-- `465d0ec1:src/ArenaNode.jl:387-392`. Bulk copy of the entry vector. -/
def copyEntries (dest src : Store T) : Store T :=
  { reserve dest src.nodes.size with nodes := src.nodes, compact := true }

/-- `465d0ec1:src/ArenaNode.jl:394`. -/
def editHeadroom (n d : Nat) : Nat := n + d + 1

-- if is_compact_root(tree)
--     n = length(arena.nodes)
--     dest = Arena{T,D}(; capacity=_edit_headroom(n, Val(D)))
--     _copy_entries!(dest, arena.nodes)
--     return ArenaNode{T,D}(dest, get_index(tree))
-- end
-- n = _subtree_count(arena.nodes, get_index(tree))
-- dest = Arena{T,D}(; capacity=_edit_headroom(n, Val(D)))
-- idx = _append_subtree!(dest, arena.nodes, get_index(tree), n)
-- return ArenaNode{T,D}(dest, idx)
/-- `465d0ec1:src/ArenaNode.jl:396-408`. The fresh result arena has its own object
identity, supplied by the caller. Neither path copies individual scalar values. -/
def copyNode (src : Store T) (d : Nat) (i : Int32) (_breakSharing : Bool := false) :
    Jl (Store T × Int32) := do
  if compactRoot src i then
    return (copyEntries { capacity := editHeadroom src.nodes.size d } src, i)
  let n ← subtreeCount src src.nodes.size i
  appendSubtree { capacity := editHeadroom n d } src d i (some n)

/-- `465d0ec1:src/ArenaNode.jl:410-416`. The omitted count is evaluated lazily. -/
def allocateContainer (count : Option Nat) (length : Unit → Jl Nat) (d : Nat) : Jl (Store T) := do
  let n ← match count with | some n => pure n | none => length ()
  return { capacity := editHeadroom n d }

-- if dest === get_arena(src)
--     if is_compact_root(src)
--         set_ref!(length(src))
--         return src
--     end
--     src = copy_node(src)
-- end
-- if is_compact_root(src)
--     _copy_entries!(dest, get_arena(src).nodes)
--     set_ref!(length(src))
--     return ArenaNode{T,D}(dest, get_index(src))
-- end
-- empty!(dest.nodes)
-- idx = _append_subtree!(dest, get_arena(src).nodes, get_index(src))
-- mark_compact!(dest)
-- set_ref!(length(dest.nodes))
-- return ArenaNode{T,D}(dest, idx)
/-- `465d0ec1:src/ArenaNode.jl:418-441`. The third result is the count assigned
when an output ref is supplied. -/
def copyInto (dest src : Store T) (d : Nat) (i : Int32) (sameArena : Bool) :
    Jl (Store T × Int32 × Nat) := do
  if sameArena && compactRoot src i then return (src, i, src.nodes.size)
  let (src, i) ← if sameArena then copyNode src d i else pure (src, i)
  if compactRoot src i then return (copyEntries dest src, i, src.nodes.size)
  let (dest, idx) ← appendSubtree { dest with nodes := #[] } src d i
  return ({ dest with compact := true }, idx, dest.nodes.size)

-- leaf.constant && return push_constant!(arena, leaf.val)
-- return push_feature!(arena, leaf.feature)
-- padded = ntuple(i -> get(children, i, Int32(0)), Val(D))
-- return _push_node!(arena; degree=length(children), op=branch.op, children=padded)
/-- `465d0ec1:src/ArenaNode.jl:447-466`. The generic transfer runs an unfolding
postorder map-reduce on the source Node. `scalar` is Julia's dispatched conversion. -/
def copyTreeInto (zero : T) (scalar : U → Jl T) (d : Nat) :
    Tree U → Store T → Jl (Store T × Int32)
  | .const x, dest => do
    let v ← scalar x
    push dest { val := v, children := zeros d, constant := true }
  | .feature f, dest => do
    if f > 65535 then throw (.userError "InexactError")
    push dest { val := zero, children := zeros d, feature := UInt16.ofNat f }
  | .branch op cs, dest => do
    let (dest, children) ← cs.attach.foldlM (fun (dest, ids) child => do
      let (dest, i) ← copyTreeInto zero scalar d child.val dest
      return (dest, ids.push i)) (dest, #[])
    if op > 255 || cs.length > 255 then throw (.userError "InexactError")
    let slots := (Array.range d).map (fun i => children[i]?.getD 0)
    push dest {
      val := zero
      children := slots
      degree := UInt8.ofNat cs.length
      op := UInt8.ofNat op }
termination_by tree _ => sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem child.property
  simp only [Tree.branch.sizeOf_spec]
  omega

-- arena = Arena{T,D}(; capacity=length(tree; break_sharing=Val(true)))
-- idx = _copy_to_arena!(arena, tree)
-- mark_compact!(arena)
-- return ArenaNode{T,D}(arena, idx)
/-- `465d0ec1:src/ArenaNode.jl:468-476`. Equal arena types use Julia's identity
conversion, represented by the original handle rather than this fresh conversion. -/
def fromTree (zero : T) (scalar : U → Jl T) (d : Nat) (t : Tree U) : Jl (Store T × Int32) := do
  let (s, idx) ← copyTreeInto zero scalar d t { capacity := t.size }
  return ({ s with compact := true }, idx)

end DynExpr.Arena
