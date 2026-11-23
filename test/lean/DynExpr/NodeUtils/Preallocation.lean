import DynExpr.NodeUtils.Nodes

namespace DynExpr.NodeUtils

/-- src/NodePreallocation.jl:22-26: allocate initialized empty node identities.
`n` is the explicit size, or the caller's length(prototype) result. -/
def allocateContainer (g : Graph T) : Nat → List Addr × Graph T
  | 0 => ([],g)
  | n + 1 =>
      let (a,h) := g.alloc ⟨0,false,none,0,0,[]⟩
      let (as,k) := allocateContainer h n
      (a :: as,k)

/-- src/NodePreallocation.jl:45,48 consume the next one-based unchecked slot. -/
def destinationSlot (dest : List Addr) (cursor : Nat) : Jl Addr :=
  match dest[cursor]? with
  | none => .error (.undefinedBehavior "preallocated destination index out of bounds")
  | some a => .ok a

/-- src/NodePreallocation.jl:53-65: leaves copy their active fields, branches
replace only degree/op/children, preserving other destination fields. A
constant leaf stores `copy_value(src.val)` (src/NodePreallocation.jl:55),
which returns isbits values unchanged (src/ValueInterface.jl:82); values
here are carried by value, so the leaf's value is stored as is. -/
def writeCopiedCell (g : Graph T) (dest : Addr) (src : Cell T) (cs : List Addr) : Jl (Graph T) := do
  let old ← g.read dest
  let cell := if src.degree = 0 then src else
    { old with degree := cs.length, op := src.op, children := cs }
  g.write dest cell

/-- src/NodePreallocation.jl:35-51 and src/base.jl:123-155.
Source and destination heaps describe disjoint storage. This covers the documented
allocate_container/copy_into! workflow; source-destination aliases are excluded.
Children are copied before their parent. A GraphNode cache preserves source sharing.
The cursor is reset to zero by copyInto, including a caller-supplied ref. -/
def copyWalk (source : Graph T) (sharing : Bool) (dest : List Addr) :
    Nat → Addr → Graph T → Nat → List (Addr × Addr) → Jl (Addr × Graph T × Nat × List (Addr × Addr))
  | 0, _, _, _, _ => .error (.errorException "traversal fuel exhausted")
  | fuel + 1, root, out, cursor, cache => do
      match if sharing then cache.lookup root else none with
      | some result => return (result,out,cursor,cache)
      | none =>
          let c ← source.read root
          let (children,h,j,cache') ←
            if c.degree = 0 then pure ([],out,cursor,cache)
            else c.children.foldlM (fun (as,g,i,m) a => do
              let (b,h,j,m') ← copyWalk source sharing dest fuel a g i m
              return (as ++ [b],h,j,m')) ([],out,cursor,cache)
          let a ← destinationSlot dest j
          let h' ← writeCopiedCell h a c children
          return (a,h',j + 1,if sharing then (root,a) :: cache' else cache')

def copyInto (source : Graph T) (sharing : Bool) (dest : List Addr) (out : Graph T)
    (fuel root : Nat) := copyWalk source sharing dest fuel root out 0 []

private theorem containerLength (g : Graph T) (n : Nat) : (allocateContainer g n).1.length = n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [allocateContainer, ih]

def ContainerCapacity : Prop := ∀ (g : Graph Nat) n,
  (allocateContainer g n).1.length = n

theorem containerCapacity_proven : ContainerCapacity := containerLength

def sourceLeaf (v : Nat) : Graph Nat := (Heap.empty.alloc (constantCell v)).2

def emptySlots (n : Nat) := allocateContainer (Heap.empty : Graph Nat) n

def sourcePair (a b : Nat) : Graph Nat :=
  let h := (Heap.empty.alloc (constantCell a)).2
  let k := (h.alloc (constantCell b)).2
  (k.alloc (operatorCell 1 [0,1])).2

/-- A cached GraphNode identity reuses its copied node without writes or cursor
advancement (src/base.jl:127-130). -/
theorem copyWalk_cacheHit (source out : Graph T) (dest : List Addr) (fuel root cursor : Nat)
    (cache : List (Addr × Addr)) (copied : Addr) (hc : cache.lookup root = some copied) :
    copyWalk source true dest (fuel + 1) root out cursor cache = .ok (copied,out,cursor,cache) := by
  simp [copyWalk, hc, Pure.pure, Except.pure]

example : (copyInto aliasGraph true (emptySlots 2).1 (emptySlots 2).2 2 1).map
    (fun (_,g,cursor,_) => ((g.cells 1).map (fun c => c.children),cursor)) =
    .ok (some [0,0],2) := rfl

end DynExpr.NodeUtils
