import DynExpr.NodeBase.Heap
import DynExpr.NodeBase.TreeOps

/-!
`tree_mapreduce` on the heap (`src/base.jl:77-166`), with the `GraphNode`
identity cache, and the functions built on it: `count_nodes`, `count`,
`filter_map`, `collect`, `length`, `iterate`, `==` with identity maps and
`copy_node`.
-/

namespace DynExpr.NodeBase
open DynExpr

variable {T R B G σ : Type}

/-- The `Dict{UInt,RT}` identity map keyed by `objectid` (`src/base.jl:160-166`),
most recent insertion first. -/
abbrev Cache (R : Type) := List (Addr × R)

/-- `haskey`/`getindex` on the identity map. -/
def findCache : Cache R → Addr → Option R
  | [], _ => none
  | (k, v) :: c, a => if k = a then some v else findCache c a

/-- `call_mapreducer` (`src/base.jl:123-158`). With `sharing` (identity map
present), a cached object returns `f_on_shared(result, true)`; otherwise the
raw result is computed (`f_leaf` at degree zero, else `f_branch` then `op`
on the children visited left to right), cached, and returned through
`f_on_shared(result, false)`. Fuel bounds the recursion depth; running out
models a stack overflow. -/
def tmrH (g : SGraph T) (D : Nat) (sharing : Bool)
    (fLeaf : Addr → SCell T → StateT σ Jl R) (fBranch : Addr → SCell T → StateT σ Jl B)
    (op : B → List R → StateT σ Jl R) (fos : R → Bool → R) :
    Nat → Addr → Cache R → StateT σ Jl (R × Cache R)
  | 0, _, _ => throw (.errorException "StackOverflowError")
  | fuel + 1, a, cache =>
    match (if sharing then findCache cache a else none) with
    | some r => pure (fos r true, cache)
    | none => do
      let c ← StateT.lift (g.read a)
      let (result, cache') ← (if c.degree = 0 then do
          let r ← fLeaf a c
          pure (r, cache)
        else do
          let b ← fBranch a c
          let cs ← StateT.lift (getChildren g D a (nifDeg D c.degree))
          let (rs, cache') ← cs.foldlM (fun (acc : List R × Cache R) x => do
              let (r, c2) ← tmrH g D sharing fLeaf fBranch op fos fuel x acc.2
              pure (acc.1 ++ [r], c2)) ([], cache)
          let r ← op b rs
          pure (r, cache'))
      if sharing then pure (fos result false, (a, result) :: cache')
      else pure (result, cache')

/-- `tree_mapreduce(f_leaf, f_branch, op, tree, RT; f_on_shared,
break_sharing)` (`src/base.jl:87-110`); `isGraph` is `preserve_sharing`
(`src/Node.jl:343-345`). The `sizehint!` pre-pass of `allocate_id_map` has no
observable effect and is omitted. -/
def treeMapreduceH (g : SGraph T) (D : Nat) (isGraph bs : Bool)
    (fLeaf : Addr → SCell T → StateT σ Jl R) (fBranch : Addr → SCell T → StateT σ Jl B)
    (op : B → List R → StateT σ Jl R) (fos : R → Bool → R) (fuel : Nat) (root : Addr) :
    StateT σ Jl R := do
  let (r, _) ← tmrH g D (isGraph && !bs) fLeaf fBranch op fos fuel root []
  pure r

/-- `count_nodes(tree; break_sharing)` (`src/base.jl:271-280`). -/
def countNodesH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (fuel : Nat) (root : Addr) : Jl Nat :=
  (treeMapreduceH (σ := Unit) g D isGraph bs (fun _ _ => pure 1) (fun _ _ => pure 1)
    (fun b rs => pure (b + rs.sum)) (fun c s => if s then 0 else c) fuel root).run' ()

/-- `count(f, tree; init, break_sharing)` (`src/base.jl:389-400`). -/
def countH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (f : Addr → SCell T → Bool)
    (init fuel : Nat) (root : Addr) : Jl Nat := do
  let n ← (treeMapreduceH (σ := Unit) g D isGraph bs (fun a c => pure (if f a c then 1 else 0))
    (fun a c => pure (if f a c then 1 else 0)) (fun b rs => pure (b + rs.sum))
    (fun c s => if s then 0 else c) fuel root).run' ()
  pure (n + init)

/-- `foreach(f, tree; break_sharing)` (`src/base.jl:287-298`). -/
def foreachH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (f : Addr → SCell T → StateT σ Jl Unit)
    (fuel : Nat) (root : Addr) : StateT σ Jl Unit :=
  treeMapreduceH g D isGraph bs f f (fun (_ : Unit) (_ : List Unit) => pure ()) (fun r _ => r) fuel root

/-- The `filter_map!` callback (`src/base.jl:333-338`) on heap nodes. -/
def fmStepH (ff : Addr → SCell T → Bool) (mf : Addr → SCell T → G) (a : Addr) (c : SCell T) :
    StateT (Nat × List G) Jl Unit :=
  if ff a c then do
    let s ← get
    let p := s.1 + 1
    if p ≤ s.2.length then set (p, s.2.set (p - 1) (mf a c))
    else throw (.undefinedBehavior "@inbounds destination[pointer] out of range")
  else pure ()

/-- `filter_map(filter_fnc, map_fnc, tree, GT; break_sharing)`
(`src/base.jl:308-340`); `none` is an unset `undef` slot. -/
def filterMapH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (ff : Addr → SCell T → Bool)
    (mf : Addr → SCell T → G) (fuel : Nat) (root : Addr) : Jl (List (Option G)) := do
  let n ← countH g D isGraph bs ff 0 fuel root
  let (_, (_, dest)) ← (foreachH g D isGraph bs (fmStepH ff (fun a c => some (mf a c))) fuel root).run
    (0, List.replicate n none)
  pure dest

/-- `collect(tree; break_sharing)` (`src/base.jl:347-360`): the nodes. -/
def collectH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (fuel : Nat) (root : Addr) :
    Jl (List (Option Addr)) :=
  filterMapH g D isGraph bs (fun _ _ => true) (fun a _ => a) fuel root

/-- `length(tree)` (`src/base.jl:457-459`): `count_nodes` with the default
`break_sharing = Val(false)`. -/
def lengthH (g : SGraph T) (D : Nat) (isGraph : Bool) (fuel : Nat) (root : Addr) : Jl Nat :=
  countNodesH g D isGraph false fuel root

/-- The elements produced by iterating over a tree (`src/base.jl:451-455`):
the root, then `collect(root)[2:end]` with the default `break_sharing`. -/
def iterElemsH (g : SGraph T) (D : Nat) (isGraph : Bool) (fuel : Nat) (root : Addr) :
    Jl (List (Option Addr)) := do
  let l ← collectH g D isGraph false fuel root
  pure (some root :: l.drop 1)

/-- `leaf_equal` (`src/base.jl:250-260`) on heap cells; reading an unset
`val` is modelled as `UndefRefError`. -/
def leafEqH (veq : T → T → Bool) (ca cb : SCell T) : Jl Bool :=
  if ca.constant != cb.constant then pure false
  else if ca.constant then
    match ca.val, cb.val with
    | some x, some y => pure (veq x y)
    | _, _ => throw .undefRefError
  else pure (ca.feature == cb.feature)

/-- `inner_is_equal(a, b, id_maps)` with identity maps (`src/base.jl:203-245`),
the path of `==` on `GraphNode`. The maps are `Dict{UInt,UInt}`s from each
visited object to the object it was compared with (most recent insertion
first). A pair is equal when both objects were visited and matched each
other, unequal when exactly one was visited or they matched other objects,
and is otherwise compared field by field, children with a short-circuiting
`@nall`. Both objects are recorded after the comparison. -/
def innerEqH (g : SGraph T) (D : Nat) (veq : T → T → Bool) :
    Nat → Addr → Addr → Cache Addr × Cache Addr → Jl (Bool × (Cache Addr × Cache Addr))
  | 0, _, _, _ => throw (.errorException "StackOverflowError")
  | fuel + 1, a, b, maps =>
    match findCache maps.1 a, findCache maps.2 b with
    | some b', some a' => pure (b' == b && a' == a, maps)
    | some _, none | none, some _ => pure (false, maps)
    | none, none => do
      let ca ← g.read a
      let cb ← g.read b
      let (result, maps') ← (if ca.degree ≠ cb.degree then pure (false, maps)
        else if ca.degree = 0 then do
          let r ← leafEqH veq ca cb
          pure (r, maps)
        else if ca.op ≠ cb.op then pure (false, maps)
        else do
          let k := nifDeg D ca.degree
          let csa ← getChildren g D a k
          let csb ← getChildren g D b k
          (csa.zip csb).foldlM (fun (acc : Bool × (Cache Addr × Cache Addr)) xy =>
            if acc.1 then innerEqH g D veq fuel xy.1 xy.2 acc.2 else pure acc) (true, maps))
      pure (result, ((a, b) :: maps'.1, (b, a) :: maps'.2))

/-- `a == b` on two `GraphNode`s of the same type (`src/base.jl:196-202`). -/
def graphEqH (g : SGraph T) (D : Nat) (veq : T → T → Bool) (fuel : Nat) (a b : Addr) : Jl Bool :=
  (innerEqH g D veq fuel a b ([], [])).map (·.1)

/-- Allocate a node object in the state heap. -/
def allocS (c : SCell T) : StateT (SGraph T) Jl Addr := fun h => .ok (h.alloc c)

/-- `leaf_copy` (`src/base.jl:501-507`) for element types whose `copy_value`
is the identity (`isbits` values, `src/ValueInterface.jl:82`): values are
carried by value. -/
def leafCopyH (_ : Addr) (c : SCell T) : StateT (SGraph T) Jl Addr :=
  if c.constant then
    match c.val with
    | some v => allocS { (blankCell : SCell T) with constant := true, val := some v }
    | none => throw .undefRefError
  else allocS { (blankCell : SCell T) with feature := c.feature }

/-- `leaf_copy` (`src/base.jl:501-507`) with an explicit `copy_value`
(`src/ValueInterface.jl:82`) acting on the heap. -/
def leafCopyVH (cv : T → StateT (SGraph T) Jl T) (_ : Addr) (c : SCell T) :
    StateT (SGraph T) Jl Addr :=
  if c.constant then
    match c.val with
    | some v => do
      let v' ← cv v
      allocS { (blankCell : SCell T) with constant := true, val := some v' }
    | none => throw .undefRefError
  else allocS { (blankCell : SCell T) with feature := c.feature }

/-- `branch_copy` (`src/base.jl:508-510`): the branch constructor with the
source's `op` and the copied children. -/
def branchCopyH (D : Nat) (src : Addr) (rs : List Addr) : StateT (SGraph T) Jl Addr := fun h => do
  let c ← h.read src
  ctor h D true { op := some c.op, children := some rs }

/-- `copy_node(tree; break_sharing)` (`src/base.jl:496-500`) for element types
whose `copy_value` is the identity (`isbits` values): the source is read from
`g`, copies are allocated in the evolving heap that starts as `g`. -/
def copyNodeH (g : SGraph T) (D : Nat) (isGraph bs : Bool) (fuel : Nat) (root : Addr) :
    Jl (Addr × SGraph T) :=
  (treeMapreduceH g D isGraph bs leafCopyH (fun a _ => pure a) (branchCopyH D)
    (fun r _ => r) fuel root).run g

/-- `copy_node(tree; break_sharing)` (`src/base.jl:496-500`) with an explicit
`copy_value`. -/
def copyNodeVH (cv : T → StateT (SGraph T) Jl T) (g : SGraph T) (D : Nat) (isGraph bs : Bool)
    (fuel : Nat) (root : Addr) : Jl (Addr × SGraph T) :=
  (treeMapreduceH g D isGraph bs (leafCopyVH cv) (fun a _ => pure a) (branchCopyH D)
    (fun r _ => r) fuel root).run g

/-- `copy_value` on a mutable value object (`deepcopy`,
`src/ValueInterface.jl:82`), with element values modelled as object
identities (`Addr`): it allocates a new object, whose contents are not
modelled, and returns its identity. -/
def deepcopyH (_ : Addr) : StateT (SGraph Addr) Jl Addr := allocS blankCell

/-- Build a heap by allocating the given cells at addresses `0, 1, ...`. -/
def mkGraph (cs : List (SCell T)) : SGraph T :=
  cs.foldl (fun h c => (h.alloc c).2) Heap.empty

/-- A feature leaf object. -/
def featC (i : Nat) : SCell T := { (blankCell : SCell T) with feature := i }

/-- A branch object with `D = 2` slots. -/
def br2 (o : Nat) (cs : List Addr) : SCell T :=
  { (blankCell : SCell T) with degree := cs.length, op := o, slots := some (slotsOf 2 (cs.map some)) }

/-! ## Properties -/

/-- `GraphNode x1 + x1` with one shared leaf: `x1` at 0, the sum at 1. -/
def sharedSum : SGraph Nat := mkGraph [featC 1, br2 1 [0, 0]]

/-- Iterating over a tree yields exactly `length(tree)` elements (the
`Base.HasLength` contract declared at `src/base.jl:361`): on every finite
well-formed tree both calls succeed and agree. -/
def iterate_length : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (isGraph : Bool) (t : Tree T),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    ∃ l, iterElemsH g D isGraph fuel root = .ok l ∧ lengthH g D isGraph fuel root = .ok l.length

/-- `==` on `GraphNode`s is sound: on finite well-formed trees it returns a
`Bool`, and `true` only when the two trees unfold to the same expression (with
an element `==` that is equality). -/
def graph_eq_sound : Prop :=
  ∀ (T : Type) (veq : T → T → Bool), (∀ x y, veq x y = true ↔ x = y) →
    ∀ (g : SGraph T) (D fuel a b : Nat) (ta tb : Tree T),
      Graph.unfold g.view fuel a = some ta → Graph.unfold g.view fuel b = some tb →
      ta.WF D (fun _ => 255) 65535 → tb.WF D (fun _ => 255) 65535 →
      ∃ r, graphEqH g D veq fuel a b = .ok r ∧ (r = true → ta = tb)

example : Graph.unfold sharedSum.view 3 1 = some (.branch 1 [.feature 1, .feature 1]) ∧
    (Tree.branch 1 [.feature 1, .feature 1] : Tree Nat).WF 2 (fun _ => 255) 65535 :=
  ⟨rfl, by simp [Tree.WF]⟩

/-! ## Object and value aliasing -/

/-- `convert(N1, tree::N2)` on the heap (`src/base.jl:535-553`): the same
object when `N1 === N2`, otherwise a `tree_mapreduce` copy through
`leaf_convert`/`branch_convert` (`src/base.jl:568-581`) with
`break_sharing = Val(!preserve_sharing(N1))`, so the identity map is used
only when both the source and the target type preserve sharing.
`leaf_convert` stores `convert(T1, t.val)`, which is the value itself for
equal element types, so values are carried as by `copyNodeH`. Element types
and the degree check are modelled in `NodeBase.Types`. The constructor form
`N(tree)` is this function (`src/base.jl:565-567`). -/
def convertH (g : SGraph T) (D : Nat) (sameType srcIsGraph dstIsGraph : Bool) (fuel : Nat)
    (root : Addr) : Jl (Addr × SGraph T) :=
  if sameType then .ok (root, g)
  else copyNodeH g D srcIsGraph (!dstIsGraph) fuel root

/-- Converting a finite well-formed `GraphNode` tree to a plain `Node` type
succeeds and yields an alias-free tree (plain `Node` trees must never contain
aliased nodes). -/
def convert_to_node_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    ∃ r h, convertH g D false true false fuel root = .ok (r, h) ∧ Graph.NoAlias h.view r

/-- Exposure property: `convert(N, tree)` and the constructor form `N(tree)`
return the argument object itself when `tree` already has type `N`, and leave
the heap unchanged (Julia `convert` convention). -/
def convert_same_type_identity : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (srcIsGraph dstIsGraph : Bool),
    convertH g D true srcIsGraph dstIsGraph fuel root = .ok (root, g)

theorem convert_same_type_identity_holds : convert_same_type_identity := by
  intro T g D fuel root srcIsGraph dstIsGraph
  rfl

/-- `copy_node` shares no mutable object with its source: on every finite
well-formed tree it succeeds, every node reachable from the copy is newly
allocated, and no constant value object of the copy is a value object of the
source. Element values are modelled as object identities (`Addr`) of live
objects (allocated before the call), as for mutable values such as
`Vector{Float64}` constants under `GenericOperatorEnum`, whose `copy_value`
is `deepcopy`. -/
def copy_value_fresh : Prop :=
  ∀ (g : SGraph Addr) (D fuel root : Nat) (t : Tree Addr) (isGraph bs : Bool),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    (∀ v ∈ constVals t, v < g.next) →
    ∃ r h tc, copyNodeVH deepcopyH g D isGraph bs fuel root = .ok (r, h) ∧
      (∀ b, Graph.Reachable h.view r b → g.next ≤ b) ∧
      Graph.unfold h.view fuel r = some tc ∧ ∀ v ∈ constVals tc, v ∉ constVals t

end DynExpr.NodeBase
