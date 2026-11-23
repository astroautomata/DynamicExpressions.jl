import DynExpr.Arena.Mutation

namespace DynExpr.Arena

-- entry = _load_entry(arena, idx)
-- node = ArenaNode{T,D}(arena, idx)
-- degree = entry.degree
-- iszero(degree) && return @inline(f_leaf(node))
-- branch = @inline(f_branch(node))
-- return Base.Cartesian.@nif(
--     $D,
--     i -> degree == i,  # COV_EXCL_LINE
--     i -> @inline(  # COV_EXCL_LINE
--         op(
--             branch,
--             Base.Cartesian.@ntuple(
--                 i,
--                 j -> _entry_mapreduce(  # COV_EXCL_LINE
--                     f_leaf,
--                     f_branch,
--                     op,
--                     arena,
--                     entry.children[j],
--                 )
--             )...,
--         )
--     ),
-- )
/-- `465d0ec1:src/ArenaNode.jl:560-601`. The callback on a branch runs
before descending; Node and ArenaNode both use the non-sharing traversal.
`Entry` is the already loaded facade data; the callbacks can throw. -/
def entryMapReduce (s : Store T) (id : Nat) (leaf : Handle → Entry T → Jl R)
    (branch : Handle → Entry T → Jl B) (op : B → List R → Jl R) : Nat → Int32 → Jl R
  | 0, _ => .error (.undefinedBehavior "arena cycle")
  | fuel + 1, idx => do
    let e ← loadEntry s idx
    let p : Handle := ⟨id, idx⟩
    if e.degree == 0 then return ← leaf p e
    let b ← branch p e
    let cs ← e.active
    let children ← cs.mapM (entryMapReduce s id leaf branch op fuel)
    op b children

/-- Constant/feature data available on a valid leaf. -/
def Entry.leaf (e : Entry T) : Tree T :=
  if e.constant then .const e.val else .feature e.feature.toNat

/-- `465d0ec1:src/base.jl:535-581`, dispatched through
`465d0ec1:src/ArenaNode.jl:560-601`. Node conversion does not preserve sharing. -/
def toTree (s : Store T) (p : Handle) : Jl (Tree T) :=
  entryMapReduce s p.arena (fun _ e => .ok e.leaf) (fun _ e => .ok e.op.toNat)
    (fun op cs => .ok (.branch op cs)) s.nodes.size p.idx

/-- `465d0ec1:src/ArenaNode.jl:548-551`. -/
def countNodes (s : Store T) (p : Handle) : Jl Nat :=
  if compactRoot s p.idx then .ok s.nodes.size else
    entryMapReduce s p.arena (fun _ _ => .ok 1) (fun _ _ => .ok ())
      (fun _ cs => .ok (1 + cs.sum)) s.nodes.size p.idx

/-- `465d0ec1:src/ArenaNode.jl:553-558`. -/
def countConstants (s : Store T) (p : Handle) : Jl Nat :=
  if compactRoot s p.idx then
    .ok (s.nodes.toList.countP (fun e => e.any (fun e => e.degree == 0 && e.constant)))
  else entryMapReduce s p.arena (fun _ e => .ok (if e.constant then 1 else 0)) (fun _ _ => .ok ())
    (fun _ cs => .ok cs.sum) s.nodes.size p.idx

/-- The leaf/branch keys hashed by `465d0ec1:src/base.jl:481-486`.
The dispatched scalar and tuple hashing is carried by the callback. -/
inductive HashKey (T : Type) where
  | const (val : T) | feature (i : UInt16) | branch (degreePlusOne : Int) (op : UInt8) (children : List UInt64)

/-- `465d0ec1:src/base.jl:467-480`, via ArenaNode's reduction at
`465d0ec1:src/ArenaNode.jl:560-601`. -/
def hashTree (hash : HashKey T → UInt64 → UInt64) (seed : UInt64) (s : Store T)
    (p : Handle) : Jl UInt64 :=
  entryMapReduce s p.arena (fun _ e => .ok (hash (if e.constant then .const e.val else .feature e.feature) seed))
    (fun _ e => .ok (e.degree.toNat, e.op))
    (fun (degree, op) cs => .ok (hash (.branch ((degree : Int) + 1) op cs) seed)) s.nodes.size p.idx

-- a.degree == b.degree || return false
-- if iszero(a.degree)
--     return a.constant == b.constant &&
--            (a.constant ? a.val == b.val : a.feature == b.feature)
-- else
--     return a.op == b.op && a.children == b.children
-- end
/-- `465d0ec1:src/ArenaNode.jl:525-533`. -/
def entriesEqual (eq : T → T → Bool) (a b : Entry T) : Bool :=
  a.degree == b.degree &&
    if a.degree == 0 then a.constant == b.constant &&
      (if a.constant then eq a.val b.val else a.feature == b.feature)
    else a.op == b.op && a.children == b.children

/-- `465d0ec1:src/base.jl:203-260`. The fallback checks corresponding active
nodes, reading the nullable tuples before comparing descendants. -/
def recursiveEqual (eq : T → T → Bool) (a b : Store T) : Nat → Int32 → Int32 → Jl Bool
  | 0, _, _ => .error (.undefinedBehavior "arena cycle")
  | fuel + 1, i, j => do
    let x ← loadEntry a i
    let y ← loadEntry b j
    if x.degree != y.degree then return false
    if x.degree == 0 then return entriesEqual eq x y
    if x.op != y.op then return false
    let xs ← x.active
    if xs.contains 0 then throw .undefRefError
    let ys ← y.active
    if ys.contains 0 then throw .undefRefError
    (xs.zip ys).allM (fun (p, q) => recursiveEqual eq a b fuel p q)

-- if is_compact_root(a) && is_compact_root(b)
--     nodes_a = get_arena(a).nodes
--     nodes_b = get_arena(b).nodes
--     length(nodes_a) == length(nodes_b) || return false
--     @inbounds for i in eachindex(nodes_a)
--         _entries_equal(nodes_a[i], nodes_b[i]) || return false
--     end
--     return true
-- end
-- return inner_is_equal(a, b, nothing)  # preserve_sharing is false
/-- `465d0ec1:src/ArenaNode.jl:535-546`. -/
def equalTree (eq : T → T → Bool) (a b : Store T) (i j : Int32) : Jl Bool :=
  if compactRoot a i && compactRoot b j then do
    if a.nodes.size != b.nodes.size then return false
    (a.nodes.toList.zip b.nodes.toList).allM fun (x, y) =>
      match x, y with
      | some x, some y => pure (entriesEqual eq x y)
      | _, _ => throw .undefRefError
  else recursiveEqual eq a b (max a.nodes.size b.nodes.size) i j

-- entry = _load_entry(arena, root)
-- @inline(visit(ArenaNode(arena, root), entry)) && return true
-- degree = entry.degree
-- iszero(degree) && return false
/-- `465d0ec1:src/ArenaNode.jl:505-523`. Short-circuit recursive visit. -/
def preorder (s : Store T) (visit : Int32 → Entry T → Jl Bool) : Nat → Int32 → Jl Bool
  | 0, _ => .error (.undefinedBehavior "arena cycle")
  | fuel + 1, i => do
    let e ← loadEntry s i
    if ← visit i e then return true
    let children ← e.active
    children.anyM (preorder s visit fuel)

/-- `465d0ec1:src/ArenaNode.jl:498-503`. Read the entry and form its index
for the callback. The loop counter is a zero-based Lean offset. -/
def storageItem (s : Store T) (k : Nat) : Jl (Int32 × Entry T) := do
  let j := Int32.ofNat (k + 1)
  let e ← rawEntry s j
  return (j, e)

-- if is_compact_root(tree)
--     return _foreach_in_storage_order(visit, arena, get_index(tree))
-- else
--     return _foreach_preorder(visit, arena, get_index(tree))
-- end
/-- `465d0ec1:src/ArenaNode.jl:489-503,603-605`. The compact path visits storage
order, while the fallback is root-first. -/
def anyNode (s : Store T) (i : Int32) (visit : Int32 → Entry T → Jl Bool) : Jl Bool :=
  if compactRoot s i then (List.range s.nodes.size).anyM fun k => do
    let (j, e) ← storageItem s k
    visit j e
  else preorder s visit s.nodes.size i

/-- `465d0ec1:src/ArenaNode.jl:607-620`. With a visitor returning false, each
constant is collected. This specializes the two visit orders to collection. -/
def scalarRefs (s : Store T) (p : Handle) : Jl (List Int32) :=
  if compactRoot s p.idx then (List.range s.nodes.size).foldlM (fun acc k => do
    let j ← checkedIndex (k + 1 : Nat)
    let e ← rawEntry s j
    return if e.degree == 0 && e.constant then acc ++ [j] else acc) []
  else entryMapReduce s p.arena (fun p e => .ok (if e.constant then [p.idx] else []))
    (fun _ _ => .ok ()) (fun _ cs => .ok cs.flatten) s.nodes.size p.idx

-- vals = T[@inbounds(arena[i].val) for i in refs]
-- return vals, refs
/-- `465d0ec1:src/ArenaNode.jl:607-620`. The argument BT is unused. -/
def getConstants (s : Store T) (p : Handle) : Jl (List T × List Int32) := do
  let refs ← scalarRefs s p
  let vals ← refs.mapM (fun i => return (← rawEntry s i).val)
  return (vals, refs)

-- nodes = get_arena(tree).nodes
-- @inbounds for j in eachindex(refs, constants)
--     i = refs[j]
--     nodes[i] = _replace(nodes[i]; val=constants[j])
-- end
-- return tree
/-- `465d0ec1:src/ArenaNode.jl:622-631`. Entries of `refs` retain arena order;
repeated references are updated repeatedly, so the last write wins. -/
def setConstants (convert : U → Jl T) (s : Store T) (refs : List Int32) (values : List U) : Jl (Store T) := do
  if refs.length != values.length then throw (.dimensionMismatch "all inputs to eachindex must have the same indices")
  (refs.zip values).foldlM (fun s (i, v) => do
    let e ← rawEntry s i
    let val ← convert v
    return { s with nodes := s.nodes.set! (i.toInt.toNat - 1) (some { e with val }) }) s

end DynExpr.Arena
