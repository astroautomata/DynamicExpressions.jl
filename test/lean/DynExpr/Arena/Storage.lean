import DynExpr.Model.Tree
import DynExpr.Runtime.Errors

namespace DynExpr.Arena

/-- `465d0ec1:src/ArenaNode.jl:36-43`. UInt fields are stored at their Julia widths.
Child tuples have the enclosing arena's arity. -/
structure Entry (T : Type) where
  val : T
  children : Array Int32
  feature : UInt16 := 0
  degree : UInt8 := 0
  op : UInt8 := 0
  constant : Bool := false
  deriving Repr

/-- `465d0ec1:src/ArenaNode.jl:76-86`. `none` is an uninitialized resize slot. -/
structure Store (T : Type) where
  nodes : Array (Option (Entry T)) := #[]
  compact : Bool := true
  capacity : Nat := 0
  deriving Repr

/-- `465d0ec1:src/ArenaNode.jl:143-159`. Julia identity compares the arena object
and the index. The arena object is named by its allocation identifier. -/
structure Handle where
  arena : Nat
  idx : Int32
  deriving Repr, DecidableEq

/-- `465d0ec1:src/ArenaNode.jl:147-149,183,363`. Checked conversions to Int32. -/
def checkedIndex (n : Int) : Jl Int32 :=
  if -2147483648 ≤ n ∧ n ≤ 2147483647 then .ok (Int32.ofInt n)
  else .error (.userError "InexactError")

/-- `465d0ec1:src/ArenaNode.jl:107,161-164`. The vector offset is one less than
its Julia index. Zero is checked by `_load_entry`, not by raw indexing. -/
def rawEntry (s : Store T) (i : Int32) : Jl (Entry T) :=
  if i.toInt ≤ 0 then .error (.undefinedBehavior "arena index")
  else match s.nodes[i.toInt.toNat - 1]? with
    | none => .error (.undefinedBehavior "arena index")
    | some none => .error .undefRefError
    | some (some e) => .ok e

def loadEntry (s : Store T) (i : Int32) : Jl (Entry T) :=
  if i == 0 then .error .undefRefError else rawEntry s i

/-- `465d0ec1:src/ArenaNode.jl:92-99`. Reallocation copies the vector and keeps its indices. -/
def grow (s : Store T) (capacity : Nat) : Store T := { s with capacity }

-- needed <= arena.capacity && return arena
-- return _grow!(arena, max(needed, arena.capacity + arena.capacity ÷ 2))
/-- `465d0ec1:src/ArenaNode.jl:88-91`. -/
def reserve (s : Store T) (needed : Nat) : Store T :=
  if needed ≤ s.capacity then s else grow s (max needed (s.capacity + s.capacity / 2))

-- old = nodes[i]
-- if entry.degree != old.degree || entry.children != old.children
--     invalidate_compact!(arena)
-- end
-- nodes[i] = entry
-- return arena
/-- `465d0ec1:src/ArenaNode.jl:108-118`. The facade uses this unchecked form. -/
def storeEntry (s : Store T) (i : Int32) (entry : Entry T) : Jl (Store T) := do
  let old ← rawEntry s i
  return { s with
    compact := if entry.degree != old.degree || entry.children != old.children then false else s.compact
    nodes := s.nodes.set! (i.toInt.toNat - 1) (some entry) }

-- _reserve!(arena, length(arena.nodes) + 1)
-- nodes = arena.nodes
-- isempty(nodes) || invalidate_compact!(arena)
-- push!(nodes, entry)
-- return arena
/-- `465d0ec1:src/ArenaNode.jl:119-125,173-187`. The returned index is one-based. -/
def push (s : Store T) (e : Entry T) : Jl (Store T × Int32) := do
  let dest := reserve s (s.nodes.size + 1)
  let nodes := dest.nodes.push (some e)
  let i ← checkedIndex nodes.size
  return ({ dest with nodes, compact := dest.compact && dest.nodes.isEmpty }, i)

/-- `465d0ec1:src/ArenaNode.jl:171`. -/
def zeros (d : Nat) : Array Int32 := Array.replicate d 0

/-- `465d0ec1:src/ArenaNode.jl:189-193`. Default allocator returns a zero constant. -/
def defaultNode (zero : T) (d : Nat) : Jl (Store T × Int32) :=
  push { capacity := 1 } { val := zero, children := zeros d, constant := true }

-- return is_compact(arena) && get_index(tree) == length(arena.nodes)
/-- `465d0ec1:src/ArenaNode.jl:166-169`. -/
def compactRoot (s : Store T) (i : Int32) : Bool := s.compact && i.toInt == (s.nodes.size : Int)

/-- `465d0ec1:src/ArenaNode.jl:249-262`. Each zero slot becomes a null handle. -/
def unsafeChildren (s : Store T) (p : Handle) : Jl (Array (Option Handle)) := do
  let e ← loadEntry s p.idx
  return e.children.map fun i => if i == 0 then none else some { p with idx := i }

-- arena = get_arena(node)
-- entry = _load_entry(arena, get_index(node))
-- child_idx = entry.children[i]
-- iszero(child_idx) && throw(UndefRefError())
-- return ArenaNode{T,D}(arena, child_idx)
/-- `465d0ec1:src/ArenaNode.jl:264-270`. The tuple check precedes the null check. -/
def getChild (s : Store T) (p : Handle) (i : Nat) : Jl Handle := do
  let entry ← loadEntry s p.idx
  if i == 0 then throw .boundsError
  let some idx := entry.children[i - 1]? | throw .boundsError
  if idx == 0 then throw .undefRefError
  return { p with idx }

/-- `465d0ec1:src/ArenaNode.jl:195-247`. Core fields exposed by the facade. -/
inductive Field (T : Type) where
  | val (v : T) | degree (d : UInt8) | constant (c : Bool)
  | op (o : UInt8) | feature (f : UInt16) | unsupported (name : String)

/-- `465d0ec1:src/ArenaNode.jl:225-247`. Assignment to `l`/`r` is `setChild`. -/
def setField (s : Store T) (idx : Int32) (f : Field T) : Jl (Store T) := do
  let e ← loadEntry s idx
  match f with
  | .val v => storeEntry s idx { e with val := v }
  | .degree d => storeEntry s idx { e with degree := d }
  | .constant c => storeEntry s idx { e with constant := c }
  | .op o => storeEntry s idx { e with op := o }
  | .feature i => storeEntry s idx { e with feature := i }
  | .unsupported n => throw (.argumentError ("Unsupported field " ++ n ++ " for ArenaNode"))

/-- Only these slots may be dereferenced by tree algorithms. A leaf can retain
inactive fields from a previous shape. `465d0ec1:src/ArenaNode.jl:352-358`. -/
def Entry.active (e : Entry T) : Jl (List Int32) :=
  if e.degree.toNat ≤ e.children.size then .ok (e.children.toList.take e.degree.toNat)
  else .error (.undefinedBehavior "arena child slot")

end DynExpr.Arena
