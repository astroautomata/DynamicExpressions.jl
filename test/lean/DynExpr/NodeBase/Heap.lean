import DynExpr.Model.NodeHeap
import DynExpr.NodeBase.Types

/-!
Heap model of node objects with their full children tuples, and the
constructors, accessors and mutators of `src/Node.jl`.

The shared `Cell` stores only active children, but `set_child!` and
`set_children!` write the whole `NTuple{D}` regardless of `degree`, so this
slice keeps every slot (`SCell`) and projects to `Cell` (`SGraph.view`) to
reuse `Graph.unfold`.
-/

namespace DynExpr.NodeBase
open DynExpr

variable {T : Type}

/-- Fields of a mutable `Node{T,D}`/`GraphNode{T,D}` (`src/Node.jl:75-91`).
`slots = none` when the `children` field is undefined (fresh `N{T,D}()`,
`src/Node.jl:87`); otherwise one entry per tuple slot, where `none` is the
poison placeholder `Nullable(true, n)` whose access throws `UndefRefError`
(`src/Node.jl:176-178`, `src/Utils.jl:90-93`). Uninitialised bit fields of a
fresh object are modelled as zero/`false`. -/
structure SCell (T : Type) where
  degree : Nat
  constant : Bool
  val : Option T
  feature : Nat
  op : Nat
  slots : Option (List (Option Addr))

/-- Heap of node objects. -/
abbrev SGraph (T : Type) := Heap (SCell T)

/-- Active children: the first `degree` slots (`src/Node.jl:20-21`). A
poisoned active slot drops out, so `Graph.unfold` rejects the node. -/
def SCell.active (c : SCell T) : List Addr := ((c.slots.getD []).take c.degree).filterMap id

/-- Projection to the shared node cell. -/
def SCell.toCell (c : SCell T) : Cell T :=
  ⟨c.degree, c.constant, c.val, c.feature, c.op, c.active⟩

/-- Projection to the shared node graph, for `Graph.unfold`. -/
def SGraph.view (g : SGraph T) : Graph T where
  cells a := (g.cells a).map SCell.toCell
  next := g.next
  fresh a h := by simp [g.fresh a h]

/-- A freshly allocated `N{T,D}()` (`src/Node.jl:87`). -/
def blankCell : SCell T := ⟨0, false, none, 0, 0, none⟩

/-- `get_child(n, i)` (`src/Node.jl:214-216`): tuple indexing then
`Nullable` dereference. -/
def getChild (g : SGraph T) (D : Nat) (n : Addr) (i : Nat) : Jl Addr := do
  let c ← g.read n
  let some s := c.slots | throw .undefRefError
  if 1 ≤ i ∧ i ≤ D then
    match s[i - 1]? with
    | some (some a) => pure a
    | _ => throw .undefRefError
  else throw .boundsError

/-- `get_children(n, Val(k))` (`src/Node.jl:201-207`). -/
def getChildren (g : SGraph T) (D : Nat) (n : Addr) (k : Nat) : Jl (List Addr) :=
  (List.range k).mapM (fun i => getChild g D n (i + 1))

/-- The tuple built by `set_children!` (`src/Node.jl:238-253`): the first `D`
given entries, padded with poison when fewer are given. -/
def slotsOf (D : Nat) (cs : List (Option Addr)) : List (Option Addr) :=
  (List.range D).map (fun i => (cs[i]?).getD none)

/-- `set_children!` with raw `Nullable` entries (`src/Node.jl:235-256`):
more than `D` entries throw an `ArgumentError` (`src/Node.jl:239-240`). -/
def setChildrenRaw (g : SGraph T) (D : Nat) (n : Addr) (cs : List (Option Addr)) :
    Jl (SGraph T) :=
  if cs.length > D then
    throw (.argumentError "Cannot store more children than the maximum degree.")
  else do
    let c ← g.read n
    g.write n { c with slots := some (slotsOf D cs) }

/-- `set_children!(n, children)` with node children (`src/Node.jl:235-256`). -/
def setChildren (g : SGraph T) (D : Nat) (n : Addr) (cs : List Addr) : Jl (SGraph T) :=
  setChildrenRaw g D n (cs.map some)

/-- `set_child!(n, child, i)` (`src/Node.jl:224-227`): `Base.setindex` on the
current tuple, then `set_children!`; returns the child. -/
def setChild (g : SGraph T) (D : Nat) (n child : Addr) (i : Nat) : Jl (Addr × SGraph T) := do
  let c ← g.read n
  let some s := c.slots | throw .undefRefError
  if ¬ (1 ≤ i ∧ i ≤ D) then throw .boundsError
  let g' ← setChildrenRaw g D n (s.set (i - 1) (some child))
  pure (child, g')

/-- `set_node!(tree, new_tree)` (`src/Node.jl:490-512`): copies `degree`, then
`constant` and `val`/`feature` for a leaf, or `op` and the raw children tuple
for a branch. Reading an unset `val` is modelled as `UndefRefError`. -/
def setNode (g : SGraph T) (D : Nat) (t s : Addr) : Jl (SGraph T) := do
  let sc ← g.read s
  let tc ← g.read t
  let tc1 := { tc with degree := sc.degree }
  if sc.degree = 0 then
    let tc2 := { tc1 with constant := sc.constant }
    if sc.constant then
      match sc.val with
      | none => throw .undefRefError
      | some v => g.write t { tc2 with val := some v }
    else g.write t { tc2 with feature := sc.feature }
  else
    let some ss := sc.slots | throw .undefRefError
    let g1 ← g.write t { tc1 with op := sc.op }
    setChildrenRaw g1 D t ss

/-- Keyword arguments of the generic constructor (`src/Node.jl:350-352`). -/
structure Kw (T : Type) where
  val : Option T := none
  feature : Option Nat := none
  op : Option Nat := none
  l : Option Addr := none
  r : Option Addr := none
  children : Option (List Addr) := none

/-- The generic constructor `N(; val, feature, op, l, r, children)`
(`src/Node.jl:350-430`) building a node of maximum degree `D` (the degree
that `NodeBase.Types.ctorDegree` computes, `src/Node.jl:419-423`). `hasD`
records whether the called type fixes `D` (`has_max_degree`), which makes
the all-defaults call an error instead of a blank node
(`src/Node.jl:368-380`). `r` without `l` throws (`src/Node.jl:353`). Value
conversion and element types are modelled in `NodeBase.Types`. -/
def ctor (g : SGraph T) (D : Nat) (hasD : Bool) (kw : Kw T) : Jl (Addr × SGraph T) := do
  let children ← match kw.l, kw.r with
    | none, some _ => throw (.argumentError "The r child requires an l child.")
    | some l, none =>
      if kw.children.isSome then throw (.assertionError "isnothing(children)") else pure (some [l])
    | some l, some r =>
      if kw.children.isSome then throw (.assertionError "isnothing(children)") else pure (some [l, r])
    | none, none => pure kw.children
  match kw.val, kw.feature, kw.op, children with
  | none, none, none, none =>
    if hasD then throw (.errorException "Encountered the call for N() inside the generic constructor.")
    else pure (g.alloc blankCell)
  | some v, none, none, none => pure (g.alloc { (blankCell : SCell T) with constant := true, val := some v })
  | none, some i, none, none =>
    if i ≤ 65535 then pure (g.alloc { (blankCell : SCell T) with feature := i })
    else throw (.errorException "InexactError: trunc(UInt16, feature)")
  | none, none, some o, some cs =>
    if cs.length > D then throw (.assertionError "D2 <= max_degree(N)")
    else if o > 255 then throw (.errorException "InexactError: trunc(UInt8, op)")
    else
      let (n, g1) := g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }
      let g2 ← setChildren g1 D n cs
      pure (n, g2)
  | _, _, _, _ => throw (.methodError "no method matching node_factory")

/-! ## Basic lemmas -/

private theorem read_eq {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    g.read a = .ok c := by simp [Heap.read, h]

private theorem write_ok {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c)
    (v : SCell T) : ∃ g', g.write a v = .ok g' ∧ g'.cells a = some v ∧
      (∀ b, b ≠ a → g'.cells b = g.cells b) ∧ g'.next = g.next := by
  unfold Heap.write
  rw [dite_eq_right (by simp [h])]
  exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩

private theorem slotsOf_self (D : Nat) (s : List (Option Addr)) (hs : s.length = D) :
    slotsOf D s = s := by
  apply List.ext_getElem
  · simp [slotsOf, hs]
  · intro i h1 h2
    simp [slotsOf, List.getElem?_eq_getElem h2]

private theorem slotsOf_get (D : Nat) (cs : List (Option Addr)) (i : Nat) (hi : i < D) :
    (slotsOf D cs)[i]? = some ((cs[i]?).getD none) := by
  simp [slotsOf, hi]

private theorem mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

/-! ## Properties -/

/-- `set_child!(n, child, i)` for `1 ≤ i ≤ D` returns `child`, makes
`get_child(n, i)` return it, leaves every other slot, every other field of
`n` and every other object unchanged. -/
def set_child : Prop :=
  ∀ (T : Type) (g : SGraph T) (D n child i : Nat) (c : SCell T) (s : List (Option Addr)),
    g.cells n = some c → c.slots = some s → s.length = D → 1 ≤ i → i ≤ D →
    ∃ g', setChild g D n child i = .ok (child, g') ∧
      getChild g' D n i = .ok child ∧
      (∀ j, j ≠ i → getChild g' D n j = getChild g D n j) ∧
      (∀ a, a ≠ n → g'.cells a = g.cells a) ∧
      g'.cells n = some { c with slots := some (s.set (i - 1) (some child)) }

theorem set_child_holds : set_child := by
  intro T g D n child i c s hc hs hlen hi1 hiD
  obtain ⟨g', hw, hn, hother, _⟩ := write_ok hc { c with slots := some (slotsOf D (s.set (i - 1) (some child))) }
  have hslots : slotsOf D (s.set (i - 1) (some child)) = s.set (i - 1) (some child) :=
    slotsOf_self D _ (by simp [hlen])
  rw [hslots] at hw hn
  have hlt : i - 1 < s.length := by omega
  refine ⟨g', ?_, ?_, ?_, hother, hn⟩
  · have hng : ¬ D < s.length := by omega
    simp [setChild, setChildrenRaw, read_eq hc, hs, hi1, hiD, hslots, hw, hng, bind, Except.bind,
      pure, Except.pure]
  · simp [getChild, read_eq hn, hi1, hiD, bind, Except.bind, pure, Except.pure,
      hlt]
  · intro j hj
    simp only [getChild, read_eq hn, read_eq hc, hs, bind, Except.bind]
    by_cases hjr : 1 ≤ j ∧ j ≤ D
    · have hne : i - 1 ≠ j - 1 := by omega
      simp [hjr, hne]
    · simp [hjr]

example : ∃ (g : SGraph Nat) (c : SCell Nat), g.cells 0 = some c ∧ c.slots = some [none, none] :=
  ⟨(Heap.empty.alloc { (blankCell : SCell Nat) with slots := some [none, none] }).2, _, rfl, rfl⟩

/-- `set_children!(n, cs)` with at most `D` children makes
`get_children(n, length(cs))` return `cs`, poisons the remaining slots, and
changes nothing else. -/
def set_children : Prop :=
  ∀ (T : Type) (g : SGraph T) (D n : Nat) (cs : List Addr) (c : SCell T),
    g.cells n = some c → cs.length ≤ D →
    ∃ g', setChildren g D n cs = .ok g' ∧
      getChildren g' D n cs.length = .ok cs ∧
      (∀ j, cs.length < j → j ≤ D → getChild g' D n j = .error .undefRefError) ∧
      (∀ a, a ≠ n → g'.cells a = g.cells a) ∧
      (∃ c', g'.cells n = some c' ∧ c'.degree = c.degree ∧ c'.constant = c.constant ∧
        c'.val = c.val ∧ c'.feature = c.feature ∧ c'.op = c.op)

theorem set_children_holds : set_children := by
  intro T g D n cs c hc hlen
  obtain ⟨g', hw, hn, hother, _⟩ :=
    write_ok hc { c with slots := some (slotsOf D (cs.map some)) }
  refine ⟨g', ?_, ?_, ?_, hother, ⟨_, hn, rfl, rfl, rfl, rfl, rfl⟩⟩
  · have hng : ¬ D < cs.length := by omega
    simp [setChildren, setChildrenRaw, read_eq hc, hw, hng, bind, Except.bind]
  · have hget : ∀ i, i < cs.length → getChild g' D n (i + 1) = .ok ((cs[i]?).getD 0) := by
      intro i hi
      have h1 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, read_eq hn, h1, bind, Except.bind, slotsOf_get D _ i (by omega),
        List.getElem?_eq_getElem hi, pure, Except.pure]
    unfold getChildren
    rw [mapM_range_ok _ _ cs.length hget]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]
  · intro j hj1 hj2
    have h1 : 1 ≤ j ∧ j ≤ D := by omega
    have h2 : cs.length ≤ j - 1 := by omega
    simp [getChild, read_eq hn, h1, bind, Except.bind, slotsOf_get D _ (j - 1) (by omega), h2]
    rfl

/-- `set_children!(n, cs)` either throws or stores `cs`: whenever it returns
normally, `get_children(n, length(cs))` returns `cs` (no child is silently
dropped). -/
def set_children_total : Prop :=
  ∀ (T : Type) (g : SGraph T) (D n : Nat) (cs : List Addr) (c : SCell T), g.cells n = some c →
    (∃ e, setChildren g D n cs = .error e) ∨
    ∃ g', setChildren g D n cs = .ok g' ∧ getChildren g' D n cs.length = .ok cs

/-- The successful result of a call, or a default. -/
def okOr {α : Type} (r : Jl α) (d : α) : α :=
  match r with
  | .ok a => a
  | .error _ => d

/-- Example heap: one feature leaf `x1` at address 0. -/
def oneLeaf : SGraph Nat := (Heap.empty.alloc { (blankCell : SCell Nat) with feature := 1 }).2

theorem set_children_total_holds : set_children_total := by
  intro T g D n cs c hc
  by_cases hlen : cs.length ≤ D
  · obtain ⟨g', hw, hget, _⟩ := set_children_holds T g D n cs c hc hlen
    exact Or.inr ⟨g', hw, hget⟩
  · have hg : D < cs.length := by omega
    exact Or.inl ⟨_, by unfold setChildren setChildrenRaw; rw [if_pos (by simpa using hg)]; rfl⟩

example : (oneLeaf : SGraph Nat).cells 0 = some { (blankCell : SCell Nat) with feature := 1 } := rfl

/-- Companion of `set_children_total` (implied by it since PR #236): with at
most `D` children, `set_children!` succeeds and stores every child. -/
def set_children_total_le : Prop :=
  ∀ (T : Type) (g : SGraph T) (D n : Nat) (cs : List Addr) (c : SCell T), g.cells n = some c →
    cs.length ≤ D →
    (∃ e, setChildren g D n cs = .error e) ∨
    ∃ g', setChildren g D n cs = .ok g' ∧ getChildren g' D n cs.length = .ok cs

theorem set_children_total_le_holds : set_children_total_le :=
  fun T g D n cs c hc _ => set_children_total_holds T g D n cs c hc

/-! ### `set_node!` -/

private theorem mapM_congr' {α β : Type} (f h : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = h x) → l.mapM f = l.mapM h := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    simp [List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]

/-- Unfolding from an address is unaffected by writes to objects that are
not reachable from it. -/
theorem unfold_frame (g g' : SGraph T) (t : Addr) (hfr : ∀ b, b ≠ t → g'.cells b = g.cells b) :
    ∀ fuel a, (∀ b, Graph.Reachable g.view a b → b ≠ t) →
      Graph.unfold g'.view fuel a = Graph.unfold g.view fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a _; rfl
  | succ fuel ih =>
    intro a hr
    have ha : a ≠ t := hr a ⟨[], .nil a⟩
    have hview : g'.view.cells a = g.view.cells a := by simp [SGraph.view, hfr a ha]
    simp only [Graph.unfold, hview]
    cases hc : g.view.cells a with
    | none => rfl
    | some c =>
      have hch : ∀ b ∈ c.children, Graph.unfold g'.view fuel b = Graph.unfold g.view fuel b := by
        intro b hb
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
        apply ih b
        intro b' ⟨p, hp⟩
        exact hr b' ⟨i :: p, .cons hc hi hp⟩
      simp only [bind, Option.bind]
      rw [mapM_congr' _ _ c.children hch]

/-- `set_node!(t, s)` for well-formed `s` not reaching `t` makes `t` unfold to
the same expression as `s`, gives `t` exactly the same active child objects as
`s` (a shallow copy: the children become shared), and leaves every other
object unchanged. The `constant` flag of `t` becomes that of `s` when `s` is
a leaf and is otherwise left as it was. -/
def set_node : Prop :=
  ∀ (T : Type) (g : SGraph T) (D t s : Nat) (tc sc : SCell T) (ss : List (Option Addr)),
    g.cells t = some tc → g.cells s = some sc → ss.length = D →
    (sc.degree = 0 → sc.constant = true → sc.val.isSome) →
    (sc.degree ≠ 0 → sc.slots = some ss) →
    (∀ b, Graph.Reachable g.view s b → b ≠ t) →
    ∃ g', setNode g D t s = .ok g' ∧ (∀ a, a ≠ t → g'.cells a = g.cells a) ∧
      (g'.cells t).map SCell.active = some sc.active ∧
      (g'.cells t).map SCell.constant = some (if sc.degree = 0 then sc.constant else tc.constant) ∧
      ∀ fuel, Graph.unfold g'.view fuel t = Graph.unfold g.view fuel s

theorem set_node_holds : set_node := by
  intro T g D t s tc sc ss ht hs hlen hval hslots hr
  have hst : s ≠ t := hr s ⟨[], .nil s⟩
  -- The new cell of `t` and its relation to `sc`.
  have main : ∀ (tc' : SCell T) (g' : SGraph T), g'.cells t = some tc' →
      (∀ a, a ≠ t → g'.cells a = g.cells a) →
      tc'.degree = sc.degree → tc'.active = sc.active →
      (sc.degree = 0 → tc'.constant = sc.constant ∧
        (sc.constant = true → tc'.val = sc.val) ∧ (sc.constant = false → tc'.feature = sc.feature)) →
      (sc.degree ≠ 0 → tc'.op = sc.op) →
      ∀ fuel, Graph.unfold g'.view fuel t = Graph.unfold g.view fuel s := by
    intro tc' g' ht' hfr hdeg hact hleaf hop fuel
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have hv' : g'.view.cells t = some tc'.toCell := by simp [SGraph.view, ht']
      have hv : g.view.cells s = some sc.toCell := by simp [SGraph.view, hs]
      simp only [Graph.unfold, hv', hv, bind, Option.bind, SCell.toCell, hdeg, hact]
      have hch : ∀ b ∈ sc.active, Graph.unfold g'.view fuel b = Graph.unfold g.view fuel b := by
        intro b hb
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
        apply unfold_frame g g' t hfr fuel b
        intro b' ⟨p, hp⟩
        exact hr b' ⟨i :: p, .cons hv hi hp⟩
      by_cases hd : sc.degree = 0
      · obtain ⟨hc, hvv, hff⟩ := hleaf hd
        simp only [hd, hc]
        cases hcs : sc.constant
        · simp [hff hcs]
        · simp [hvv hcs]
      · simp only [hd, ite_false, hop hd]
        rw [mapM_congr' _ _ sc.active hch]
  by_cases hd : sc.degree = 0
  · by_cases hc : sc.constant = true
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval hd hc)
      obtain ⟨g', hw, hn, hfr, _⟩ :=
        write_ok ht { tc with degree := sc.degree, constant := sc.constant, val := some v }
      have hact : SCell.active { tc with degree := sc.degree, constant := sc.constant, val := some v } =
          sc.active := by simp [SCell.active, hd]
      refine ⟨g', ?_, hfr, by simp [hn, hact], by simp [hn, hd], main _ g' hn hfr rfl hact ?_ ?_⟩
      · simp only [hd, hc] at hw
        simp [setNode, read_eq hs, read_eq ht, hd, hc, hv, bind, Except.bind, hw]
      · intro _; exact ⟨rfl, fun _ => hv.symm, fun h => by simp_all⟩
      · intro h; exact absurd hd h
    · obtain ⟨g', hw, hn, hfr, _⟩ :=
        write_ok ht { tc with degree := sc.degree, constant := sc.constant, feature := sc.feature }
      have hact : SCell.active { tc with degree := sc.degree, constant := sc.constant, feature := sc.feature } = sc.active := by
        simp [SCell.active, hd]
      refine ⟨g', ?_, hfr, by simp [hn, hact], by simp [hn, hd], main _ g' hn hfr rfl hact ?_ ?_⟩
      · have hc' : sc.constant = false := by simpa using hc
        simp only [hd, hc'] at hw
        simp [setNode, read_eq hs, read_eq ht, hd, hc', bind, Except.bind, hw]
      · intro _; exact ⟨rfl, fun h => absurd h hc, fun _ => rfl⟩
      · intro h; exact absurd hd h
  · have hss := hslots hd
    obtain ⟨g1, hw1, hn1, hfr1, _⟩ := write_ok ht { tc with degree := sc.degree, op := sc.op }
    obtain ⟨g', hw, hn, hfr', _⟩ :=
      write_ok hn1 { tc with degree := sc.degree, op := sc.op, slots := some (slotsOf D ss) }
    have hfr : ∀ a, a ≠ t → g'.cells a = g.cells a := fun a ha => by rw [hfr' a ha, hfr1 a ha]
    have hact : SCell.active { tc with degree := sc.degree, op := sc.op, slots := some (slotsOf D ss) } = sc.active := by
      simp [SCell.active, slotsOf_self D ss hlen, hss]
    refine ⟨g', ?_, hfr, by simp [hn, hact], by simp [hn, hd], main _ g' hn hfr rfl hact ?_ ?_⟩
    · have hng : ¬ D < ss.length := by omega
      simp [setNode, read_eq hs, read_eq ht, hd, hss, bind, Except.bind, hw1, setChildrenRaw,
        read_eq hn1, hw, hng]
    · intro h; exact absurd h hd
    · intro _; rfl

example : ∃ (g : SGraph Nat) (tc sc : SCell Nat),
    g.cells 0 = some tc ∧ g.cells 1 = some sc ∧ sc.degree = 0 ∧ sc.constant = true ∧
    sc.val.isSome ∧ (∀ b, Graph.Reachable g.view 1 b → b ≠ 0) := by
  let g : SGraph Nat := ((Heap.empty.alloc { (blankCell : SCell Nat) with feature := 1 }).2.alloc
    { (blankCell : SCell Nat) with constant := true, val := some 3 }).2
  refine ⟨g, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro b ⟨p, hp⟩
  cases hp with
  | nil => decide
  | cons hc hi _ =>
    have h1 : g.view.cells 1 =
        some (SCell.toCell { (blankCell : SCell Nat) with constant := true, val := some 3 }) := rfl
    rw [h1] at hc
    cases hc
    simp [SCell.toCell, SCell.active, blankCell] at hi

/-! ### Constructors -/

/-- The constructors build a constant leaf from `val`, a feature leaf from
`feature`, and a branch from `op` with `children` (or `l`/`r`) whose
`get_children` are exactly the given children; existing objects are
unchanged. -/
def ctor_nodes : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (hasD : Bool),
    (∀ v : T, ∃ g', ctor g D hasD { val := some v } = .ok (g.next, g') ∧
      (∀ a, a < g.next → g'.cells a = g.cells a) ∧
      Graph.unfold g'.view 1 g.next = some (.const v)) ∧
    (∀ i, i ≤ 65535 → ∃ g', ctor g D hasD { feature := some i } = .ok (g.next, g') ∧
      (∀ a, a < g.next → g'.cells a = g.cells a) ∧
      Graph.unfold g'.view 1 g.next = some (.feature i)) ∧
    (∀ (o : Nat) (cs : List Addr), o ≤ 255 → cs.length ≤ D →
      ∃ g', ctor g D hasD { op := some o, children := some cs } = .ok (g.next, g') ∧
        (∀ a, a < g.next → g'.cells a = g.cells a) ∧
        getChildren g' D g.next cs.length = .ok cs ∧
        ∃ c, g'.cells g.next = some c ∧ c.degree = cs.length ∧ c.op = o) ∧
    (∀ (o a b : Nat),
      ctor g D hasD { op := some o, l := some a } = ctor g D hasD { op := some o, children := some [a] } ∧
      ctor g D hasD { op := some o, l := some a, r := some b } =
        ctor g D hasD { op := some o, children := some [a, b] })

theorem ctor_nodes_holds : ctor_nodes := by
  intro T g D hasD
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    refine ⟨_, rfl, ?_, ?_⟩
    · intro a ha; simp [show a ≠ g.next by omega]
    · simp [Graph.unfold, SGraph.view, SCell.toCell, SCell.active, blankCell]
  · intro i hi
    refine ⟨_, by simp [ctor, hi]; rfl, ?_, ?_⟩
    · intro a ha; simp [show a ≠ g.next by omega]
    · simp [Graph.unfold, SGraph.view, SCell.toCell, SCell.active, blankCell]
  · intro o cs ho hlen
    let g1 := (g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }).2
    have h1 : g1.cells g.next = some { (blankCell : SCell T) with degree := cs.length, op := o } := by
      simp [g1, Heap.alloc]
    obtain ⟨g', hsc, hgc, _, hother, c', hc', hdeg, _, _, _, hop⟩ :=
      set_children_holds T g1 D g.next cs _ h1 hlen
    refine ⟨g', ?_, ?_, hgc, c', hc', hdeg, hop⟩
    · have hn1 : ¬ cs.length > D := by omega
      have hn2 : ¬ o > 255 := by omega
      have hfst : (g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }).1 = g.next :=
        rfl
      simp only [g1] at hsc
      simp [ctor, hn1, hn2, bind, Except.bind, pure, Except.pure, hfst, hsc]
    · intro a ha
      rw [hother a (by omega)]
      simp [g1, Heap.alloc, show a ≠ g.next by omega]
  · intro o a b
    exact ⟨rfl, rfl⟩

/-- Child arguments given through `l`, `r` and `children`, in that order. -/
def Kw.childArgs (kw : Kw T) : List Addr := kw.l.toList ++ kw.r.toList ++ kw.children.getD []

/-- Every child passed to the constructor through `l`, `r` or `children` is
stored, in order, as the children of the result, or the call throws. -/
def ctor_child_arg : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (hasD : Bool) (kw : Kw T),
    (∃ e, ctor g D hasD kw = .error e) ∨
    ∃ n g', ctor g D hasD kw = .ok (n, g') ∧ getChildren g' D n kw.childArgs.length = .ok kw.childArgs

/-- The branch constructor either throws or stores exactly its children. -/
private theorem ctor_branch_or (g : SGraph T) (D : Nat) (hasD : Bool) (o : Nat) (cs : List Addr) :
    (∃ e, ctor g D hasD { op := some o, children := some cs } = .error e) ∨
    ∃ n g', ctor g D hasD { op := some o, children := some cs } = .ok (n, g') ∧
      getChildren g' D n cs.length = .ok cs := by
  by_cases h : cs.length ≤ D ∧ o ≤ 255
  · obtain ⟨g', hc, _, hget, _⟩ := (ctor_nodes_holds T g D hasD).2.2.1 o cs h.2 h.1
    exact Or.inr ⟨_, g', hc, hget⟩
  · left
    by_cases h1 : cs.length ≤ D
    · have h2 : ¬ o ≤ 255 := fun h2 => h ⟨h1, h2⟩
      exact ⟨_, by simp [ctor, show ¬ cs.length > D by omega, show o > 255 by omega]; rfl⟩
    · exact ⟨_, by simp [ctor, show cs.length > D by omega]; rfl⟩

theorem ctor_child_arg_holds : ctor_child_arg := by
  intro T g D hasD kw
  obtain ⟨val, feature, op, l, r, children⟩ := kw
  cases l <;> cases r <;> cases children <;> cases val <;> cases feature <;> cases op <;>
    first
    | (left; exact ⟨_, rfl⟩)
    | (right; exact ⟨_, _, rfl, rfl⟩)
    | skip
  all_goals first
    | (cases hasD <;> first | (left; exact ⟨_, rfl⟩) | (right; exact ⟨_, _, rfl, rfl⟩))
    | exact ctor_branch_or g D hasD _ _
    | (rename_i i
       by_cases hi : i ≤ 65535
       · right; exact ⟨_, _, by simp [ctor, hi]; rfl, rfl⟩
       · left; exact ⟨_, by simp [ctor, hi]; rfl⟩)

/-- Companion of `ctor_child_arg` (implied by it since PR #235): when `r` is
only given together with `l`, every child argument is stored. -/
def ctor_child_arg_with_l : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (hasD : Bool) (kw : Kw T),
    (kw.r.isSome → kw.l.isSome) →
    (∃ e, ctor g D hasD kw = .error e) ∨
    ∃ n g', ctor g D hasD kw = .ok (n, g') ∧ getChildren g' D n kw.childArgs.length = .ok kw.childArgs

theorem ctor_child_arg_with_l_holds : ctor_child_arg_with_l :=
  fun T g D hasD kw _ => ctor_child_arg_holds T g D hasD kw

end DynExpr.NodeBase
