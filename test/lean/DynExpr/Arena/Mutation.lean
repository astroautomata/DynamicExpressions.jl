import DynExpr.Arena.Transfer

namespace DynExpr.Arena

/-- `465d0ec1:src/ArenaNode.jl:272-283`. Compatibility records Julia's
`AbstractExpressionNode{T,D}` check, independent of the value's convertibility. -/
inductive Child (T : Type) where
  | arena (id : Nat) (store : Store T) (index : Int32)
  | plain (tree : Tree T)
  | incompatible

-- if child isa ArenaNode{T,D} && get_arena(child) === get_arena(node)
--     return get_index(child)
-- else
--     return _copy_to_arena!(get_arena(node), child)
-- end
/-- `465d0ec1:src/ArenaNode.jl:272-283,443-458`. Same-arena descendants use
reference semantics; all others are copied into the parent's vector. -/
def resolveChild (zero : T) (d : Nat) (s : Store T) (parent : Handle) :
    Child T → Jl (Store T × Int32)
  | .arena id src i => if id == parent.arena then .ok (s, i)
    else appendSubtree { s with compact := false } src d i
  | .plain t => copyTreeInto zero .ok d t s
  | .incompatible => .error (.argumentError "ArenaNode children must have identical type parameters")

-- arena = get_arena(node)
-- entry = @inbounds arena[get_index(node)]
-- 1 <= i <= D || throw(BoundsError(entry.children, i))
-- idx = _resolve_child_index!(node, child)
-- if @inbounds(entry.children[i]) != idx
--     @inbounds arena[get_index(node)] = _replace(
--         entry; children=Base.setindex(entry.children, idx, i)
--     )
-- end
-- return ArenaNode{T,D}(arena, idx)
/-- `465d0ec1:src/ArenaNode.jl:285-296`. The returned handle always refers to the
parent's arena. The degree does not change. -/
def setChild (zero : T) (d : Nat) (s : Store T) (p : Handle) (child : Child T)
    (i : Nat) : Jl (Store T × Handle) := do
  let e ← rawEntry s p.idx
  if i == 0 || i > d then throw .boundsError
  let (s, idx) ← resolveChild zero d s p child
  let some current := e.children[i - 1]? | throw (.undefinedBehavior "arena child slot")
  let s ← if current == idx then pure s
    else storeEntry s p.idx { e with children := e.children.set! (i - 1) idx }
  return (s, { p with idx })

-- D2 = length(children)
-- D2 > D &&
--     throw(ArgumentError("Cannot store $D2 children in a node of maximum degree $D."))
-- idxs = _zero_children(Val(D))
-- @inbounds for i in 1:D2
--     child = children[i]
--     if child isa Nullable
--         child.null && continue
--         child = child[]
--     end
--     idxs = Base.setindex(idxs, _resolve_child_index!(node, child), i)
-- end
-- arena = get_arena(node)
-- entry = @inbounds arena[get_index(node)]
-- @inbounds arena[get_index(node)] = _replace(entry; children=idxs)
-- return nothing
/-- `465d0ec1:src/ArenaNode.jl:298-318`. `none` represents a null incoming child. -/
def setChildren (zero : T) (d : Nat) (s : Store T) (p : Handle)
    (cs : List (Option (Child T))) : Jl (Store T) := do
  if cs.length > d then throw (.argumentError "Too many children")
  let (s, slots) ← cs.zipIdx.foldlM (fun (s, slots) (child, i) => do
    let some child := child | pure (s, slots)
    let (s, idx) ← resolveChild zero d s p child
    return (s, slots.set! i idx)) (s, zeros d)
  let e ← rawEntry s p.idx
  storeEntry s p.idx { e with children := slots }

-- tree.degree = new_tree.degree
-- if new_tree.degree == 0
--     set_leaf!(tree, new_tree)
-- else
--     set_branch!(tree, new_tree)
-- end
-- return nothing
/-- `465d0ec1:src/Node.jl:490-512`, using the facade setters from
`465d0ec1:src/ArenaNode.jl:225-247,298-318`. The branch source's nullable
slots are transferred, including any initialized inactive slots. -/
def setNode (zero : T) (d : Nat) (dest src : Store T) (p q : Handle) : Jl (Store T) := do
  let e ← loadEntry src q.idx
  let dest ← setField dest p.idx (.degree e.degree)
  if e.degree == 0 then
    let dest ← setField dest p.idx (.constant e.constant)
    setField dest p.idx (if e.constant then .val e.val else .feature e.feature)
  else
    let dest ← setField dest p.idx (.op e.op)
    let cs ← unsafeChildren (if p.arena == q.arena then dest else src) q
    setChildren zero d dest p (cs.toList.map (Option.map fun c => .arena c.arena src c.idx))

-- for child in children
--     child isa ArenaNode{T,D} && return get_arena(child)
-- end
-- return Arena{T,D}(; capacity=D + 1)
/-- `465d0ec1:src/ArenaNode.jl:340-345`. `fresh` identifies the new arena when
there is no ArenaNode of the selected type among the children. -/
def homeArena (d fresh : Nat) : List (Child T) → Nat × Store T
  | [] => (fresh, { capacity := d + 1 })
  | .arena id s _ :: _ => (id, s)
  | _ :: cs => homeArena d fresh cs

-- T = defines_eltype(N) ? eltype(N) : promote_type(map(eltype, children)...)
-- defines_eltype(N) && @assert T === promote_type(T, map(eltype, children)...)
-- D = max_degree(N)
-- D2 = length(children)
-- @assert D2 <= D
-- arena = _home_arena(ArenaNode{T,D}, children)
-- idx = _push_node!(arena; degree=D2, op)
-- node = ArenaNode{T,D}(arena, idx)
-- set_children!(node, children)
-- return node
/-- `465d0ec1:src/ArenaNode.jl:320-339`. Type dispatch has chosen T, with
`promotionOK` the result of Julia's assertion for an explicitly requested T. -/
def branchFactory (zero : T) (d fresh op : Nat) (promotionOK : Bool) (children : List (Child T)) :
    Jl (Store T × Handle) := do
  if !promotionOK then throw (.assertionError "inconsistent promotion")
  if children.length > d then throw (.assertionError "too many children")
  let (id, s) := homeArena d fresh children
  if children.length > 255 || op > 255 then throw (.userError "InexactError")
  let (s, i) ← push s {
    val := zero
    children := zeros d
    degree := UInt8.ofNat children.length
    op := UInt8.ofNat op }
  let p : Handle := ⟨id, i⟩
  let s ← setChildren zero d s p (children.map some)
  return (s, p)

end DynExpr.Arena
