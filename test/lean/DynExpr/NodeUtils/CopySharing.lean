import DynExpr.NodeUtils.Preallocation

/-!
End-to-end correctness of `copy_into!` on `GraphNode` sources
(src/NodePreallocation.jl:35-65 with the identity cache of src/base.jl:123-158).
For every well-formed finite acyclic source graph, adequate traversal fuel and a
duplicate-free initialized destination large enough for the distinct reachable
source objects, the copy succeeds, the destination unfolds to the source tree,
sharing is preserved exactly, the cursor counts the distinct reachable source
objects, and only consumed destination slots change.
-/

namespace DynExpr.NodeUtils
open Graph

/-- Every object reachable from `root` exists and its active child count agrees
with its degree (src/Node.jl:75-91). Reusable input condition for recursive
traversals such as `tree_mapreduce` (src/base.jl:77-158). -/
def GraphWF (g : Graph T) (root : Addr) : Prop :=
  ∀ x, Reachable g root x → ∃ c, g.cells x = some c ∧ c.children.length = c.degree

/-- Traversal fuel exceeds the length of every child path from `root`; fuel counts
node levels, so leaves need one unit (src/base.jl:123-158). -/
def PathFuel (g : Graph T) (root : Addr) (fuel : Nat) : Prop :=
  ∀ p x, Path g root p x → p.length < fuel

/-- A duplicate-free list of exactly the objects reachable from `root`. It is
defined from the source graph alone, independently of any copy result. -/
def ReachInventory (g : Graph T) (root : Addr) (L : List Addr) : Prop :=
  L.Nodup ∧ ∀ x, x ∈ L ↔ Reachable g root x

/-- The destination has a slot for every distinct reachable source object
(src/NodePreallocation.jl:22-26,45,48). -/
def CopyCapacity (g : Graph T) (root : Addr) (dest : List Addr) : Prop :=
  ∀ L : List Addr, L.Nodup → (∀ x ∈ L, Reachable g root x) → L.length ≤ dest.length

/-! ## Reachability -/

theorem reach_refl' (g : Graph T) (a : Addr) : Reachable g a a := ⟨[], .nil a⟩

theorem reach_trans' {g : Graph T} {a b c : Addr} (h1 : Reachable g a b)
    (h2 : Reachable g b c) : Reachable g a c := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  exact ⟨p ++ q, hp.append hq⟩

theorem reach_mem' {g : Graph T} {a b : Addr} {c : Cell T}
    (hc : g.cells a = some c) (hb : b ∈ c.children) : Reachable g a b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  exact ⟨[i], .cons hc hi (.nil b)⟩

/-- Well-formedness is inherited by every reachable child. -/
theorem GraphWF.child {g : Graph T} {root a b : Addr} {c : Cell T}
    (h : GraphWF g root) (ha : Reachable g root a) (hc : g.cells a = some c)
    (hb : b ∈ c.children) : GraphWF g b :=
  fun x hx => h x (reach_trans' (reach_trans' ha (reach_mem' hc hb)) hx)

/-- A child of a node traversed with `fuel + 1` is covered by `fuel`. -/
theorem PathFuel.child {g : Graph T} {a b : Addr} {c : Cell T} {fuel : Nat}
    (h : PathFuel g a (fuel + 1)) (hc : g.cells a = some c) (hb : b ∈ c.children) :
    PathFuel g b fuel := by
  intro p z hp
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hb
  have := h (n :: p) z (.cons hc hn hp)
  simp only [List.length_cons] at this
  omega

/-- Covered traversals have positive fuel. -/
theorem PathFuel.pos {g : Graph T} {a : Addr} {fuel : Nat} (h : PathFuel g a fuel) :
    0 < fuel := h [] a (.nil a)

/-- Adequate fuel excludes child cycles below the root: a reachable cycle would
give arbitrarily long paths. -/
theorem PathFuel.acyclic {g : Graph T} {root : Addr} {fuel : Nat}
    (h : PathFuel g root fuel) : Acyclic g root := by
  intro a ⟨p, hp⟩ q hq
  cases q with
  | nil => rfl
  | cons i q =>
    exfalso
    have pump : ∀ n, ∃ r : List Nat, n ≤ r.length ∧ Path g root r a := by
      intro n
      induction n with
      | zero => exact ⟨p, Nat.zero_le _, hp⟩
      | succ n ih =>
        obtain ⟨r, hr, hpr⟩ := ih
        refine ⟨r ++ i :: q, ?_, hpr.append hq⟩
        simp only [List.length_append, List.length_cons]
        omega
    obtain ⟨r, hr, hpr⟩ := pump fuel
    have := h r a hpr
    omega

/-! ## Cache lookups -/

abbrev CopyCache := List (Addr × Addr)

private theorem lookup_cons (x k v : Addr) (m : CopyCache) :
    ((k, v) :: m).lookup x = if x = k then some v else m.lookup x := by
  by_cases h : x = k
  · subst h; simp [List.lookup]
  · simp [List.lookup, beq_false_of_ne h, h]

private theorem lookup_mem {m : CopyCache} {x y : Addr} (h : m.lookup x = some y) :
    (x, y) ∈ m := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons e m ih =>
    obtain ⟨k, v⟩ := e
    rw [lookup_cons] at h
    by_cases hx : x = k
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · simp only [hx, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem key_of_lookup {m : CopyCache} {x y : Addr} (h : m.lookup x = some y) :
    x ∈ m.map Prod.fst :=
  List.mem_map.mpr ⟨(x, y), lookup_mem h, rfl⟩

private theorem val_of_lookup {m : CopyCache} {x y : Addr} (h : m.lookup x = some y) :
    y ∈ m.map Prod.snd :=
  List.mem_map.mpr ⟨(x, y), lookup_mem h, rfl⟩

private theorem lookup_of_key {m : CopyCache} {x : Addr} (h : x ∈ m.map Prod.fst) :
    ∃ y, m.lookup x = some y := by
  induction m with
  | nil => simp at h
  | cons e m ih =>
    obtain ⟨k, v⟩ := e
    rw [lookup_cons]
    by_cases hx : x = k
    · exact ⟨v, by simp [hx]⟩
    · simp only [hx, ↓reduceIte]
      apply ih
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h hx
      · exact h

private theorem lookup_inj {m : CopyCache} (hn : (m.map Prod.snd).Nodup) {x x' y : Addr}
    (h : m.lookup x = some y) (h' : m.lookup x' = some y) : x = x' := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons e m ih =>
    obtain ⟨k, v⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [lookup_cons] at h h'
    by_cases hx : x = k <;> by_cases hx' : x' = k
    · rw [hx, hx']
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h
      simp only [hx', ↓reduceIte] at h'
      subst h
      exact absurd (val_of_lookup h') hn.1
    · simp only [hx, ↓reduceIte] at h
      simp only [hx', ↓reduceIte, Option.some.injEq] at h'
      subst h'
      exact absurd (val_of_lookup h) hn.1
    · simp only [hx, ↓reduceIte] at h
      simp only [hx', ↓reduceIte] at h'
      exact ih hn.2 h h'

/-- The second cache extends every mapping of the first. -/
private def Grows (m m' : CopyCache) : Prop :=
  ∀ x y, m.lookup x = some y → m'.lookup x = some y

private theorem grows_push {m : CopyCache} {x a : Addr} (hx : x ∉ m.map Prod.fst) :
    Grows m ((x, a) :: m) := by
  intro z y h
  have hz : z ≠ x := fun e => hx (e ▸ key_of_lookup h)
  rw [lookup_cons, ite_eq_right hz]
  exact h

/-! ## Destination slots -/

private theorem slot_inj {dest : List Addr} (hn : dest.Nodup)
    {i j x : Nat} (hi : dest[i]? = some x) (hj : dest[j]? = some x) : i = j := by
  have bi := List.getElem?_eq_some_iff.mp hi
  have bj := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj hn).mp (bi.2.trans bj.2.symm)

private theorem mem_take_index {dest : List Addr} {j a : Nat} (h : a ∈ dest.take j) :
    ∃ i, i < j ∧ dest[i]? = some a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_take] at hi
  split at hi
  · exact ⟨i, by assumption, hi⟩
  · simp at hi

private theorem take_mono {dest : List Addr} {j k a : Nat} (h : a ∈ dest.take j) (hjk : j ≤ k) :
    a ∈ dest.take k := by
  obtain ⟨i, hi, ha⟩ := mem_take_index h
  apply List.mem_of_getElem? (i := i)
  rw [List.getElem?_take, ite_eq_left (by omega)]
  exact ha

private theorem take_ne {dest : List Addr} (hn : dest.Nodup) {j k a b : Nat}
    (ha : a ∈ dest.take j) (hb : dest[k]? = some b) (hk : j ≤ k) : a ≠ b := by
  intro hab
  subst hab
  obtain ⟨i, hi, hia⟩ := mem_take_index ha
  have := slot_inj hn hia hb
  omega

private theorem take_succ_of {dest : List Addr} {j a : Nat} (h : dest[j]? = some a) :
    dest.take (j + 1) = dest.take j ++ [a] := by
  rw [List.take_add_one, h]
  rfl

/-! ## Copy invariant -/

/-- A destination cell copies its source cell, with children mapped through the
identity cache (src/NodePreallocation.jl:53-64). -/
private structure CellCorr (m : CopyCache) (c c' : Cell T) : Prop where
  leaf : c.degree = 0 → c' = c
  branch : c.degree ≠ 0 → c'.degree = c'.children.length ∧ c'.op = c.op
  len : c'.children.length = c.children.length
  kids : ∀ (i : Nat) (b : Addr), c.children[i]? = some b →
    ∃ b', c'.children[i]? = some b' ∧ m.lookup b = some b'

private theorem CellCorr.grows {m m' : CopyCache} {c c' : Cell T} (hg : Grows m m')
    (h : CellCorr m c c') : CellCorr m' c c' := by
  refine ⟨h.leaf, h.branch, h.len, fun i b hb => ?_⟩
  obtain ⟨b', hb', hl⟩ := h.kids i b hb
  exact ⟨b', hb', hg _ _ hl⟩

/-- State invariant of the cached postorder walk: the cache maps distinct
reachable source objects to the consumed slots, newest first, and each consumed
slot holds a copy of its source cell. -/
private structure CopyInv (source out0 : Graph T) (dest : List Addr) (R : Addr)
    (out : Graph T) (j : Nat) (m : CopyCache) : Prop where
  len : j ≤ dest.length
  vals : m.map Prod.snd = (dest.take j).reverse
  keys : (m.map Prod.fst).Nodup
  reach : ∀ x ∈ m.map Prod.fst, Reachable source R x
  corr : ∀ x y, m.lookup x = some y →
    ∃ c c', source.cells x = some c ∧ out.cells y = some c' ∧ CellCorr m c c'
  frame : ∀ a, a ∉ dest.take j → out.cells a = out0.cells a

private theorem CopyInv.length {source out0 out : Graph T} {dest R j m}
    (h : CopyInv source out0 dest R out j m) : m.length = j := by
  have := congrArg List.length h.vals
  simp only [List.length_map, List.length_reverse, List.length_take] at this
  have := h.len
  omega

private theorem CopyInv.slot {source out0 out : Graph T} {dest R j m x y}
    (h : CopyInv source out0 dest R out j m) (hl : m.lookup x = some y) : y ∈ dest.take j := by
  have := val_of_lookup hl
  rw [h.vals] at this
  exact List.mem_reverse.mp this

private theorem CopyInv.valsNodup {source out0 out : Graph T} {dest R j m}
    (hn : dest.Nodup) (h : CopyInv source out0 dest R out j m) : (m.map Prod.snd).Nodup := by
  rw [h.vals]
  exact List.pairwise_reverse.mpr (((List.take_sublist _ _).nodup hn).imp fun h e => h e.symm)

private theorem CopyInv.init (source out0 : Graph T) (dest : List Addr) (R : Addr) :
    CopyInv source out0 dest R out0 0 [] := by
  refine ⟨Nat.zero_le _, by simp, List.nodup_nil, by simp, ?_, fun _ _ => rfl⟩
  intro x y h
  simp [List.lookup] at h

private theorem CopyInv.push {source out0 out out' : Graph T} {dest R j m}
    (hn : dest.Nodup) (h : CopyInv source out0 dest R out j m)
    {x a : Addr} {c c'' : Cell T}
    (hx : x ∉ m.map Prod.fst) (hxr : Reachable source R x) (ha : dest[j]? = some a)
    (hc : source.cells x = some c) (ha' : out'.cells a = some c'')
    (hoff : ∀ z, z ≠ a → out'.cells z = out.cells z)
    (hcc : CellCorr ((x, a) :: m) c c'') :
    CopyInv source out0 dest R out' (j + 1) ((x, a) :: m) := by
  refine ⟨?_, ?_, List.nodup_cons.mpr ⟨hx, h.keys⟩, ?_, ?_, ?_⟩
  · have := (List.getElem?_eq_some_iff.mp ha).1
    omega
  · simp [h.vals, take_succ_of ha]
  · intro z hz
    simp only [List.map_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hxr
    · exact h.reach z hz
  · intro z y hl
    rw [lookup_cons] at hl
    by_cases hzx : z = x
    · subst hzx
      simp only [↓reduceIte, Option.some.injEq] at hl
      subst hl
      exact ⟨c, c'', hc, ha', hcc⟩
    · simp only [hzx, ↓reduceIte] at hl
      obtain ⟨c0, c', h0, h1, h2⟩ := h.corr z y hl
      refine ⟨c0, c', h0, ?_, h2.grows (grows_push hx)⟩
      rw [hoff y (take_ne hn (h.slot hl) ha (Nat.le_refl _))]
      exact h1
  · intro z hz
    rw [take_succ_of ha] at hz
    simp only [List.mem_append, List.mem_singleton, not_or] at hz
    rw [hoff z hz.2]
    exact h.frame z hz.1

/-! ## One walk step -/

/-- Cache actually passed by `copyWalk`: GraphNode keeps the identity cache, plain
`Node` never consults or extends it (src/base.jl:96-108,127-155). -/
def cacheOf (sharing : Bool) (m : CopyCache) : CopyCache := if sharing then m else []

/-- The child-folding step of `copyWalk` (src/base.jl:137-147). -/
def copyStep (source : Graph T) (sharing : Bool) (dest : List Addr) (fuel : Nat) :
    List Addr × Graph T × Nat × CopyCache → Addr → Jl (List Addr × Graph T × Nat × CopyCache) :=
  fun (as, g, i, m) a => do
    let (b, h, j, m') ← copyWalk source sharing dest fuel a g i m
    return (as ++ [b], h, j, m')

private theorem copyWalk_miss (source : Graph T) (sharing : Bool) (dest : List Addr)
    (fuel root : Nat) (out : Graph T) (cursor : Nat) (cache : CopyCache)
    (hmiss : (if sharing then cache.lookup root else none) = none) :
    copyWalk source sharing dest (fuel + 1) root out cursor cache = (do
      let c ← source.read root
      let (children, h, j, cache') ←
        if c.degree = 0 then pure ([], out, cursor, cache)
        else c.children.foldlM (copyStep source sharing dest fuel) ([], out, cursor, cache)
      let a ← destinationSlot dest j
      let h' ← writeCopiedCell h a c children
      return (a, h', j + 1, if sharing then (root, a) :: cache' else cache')) := by
  simp only [copyWalk, hmiss]
  rfl

/-- Plain `Node` precondition: no repeated identity below `x`, and none of them
copied yet. GraphNode needs nothing. -/
private def PlainFresh (source : Graph T) (sharing : Bool) (x : Addr) (m : CopyCache) : Prop :=
  sharing = false → NoAlias source x ∧ ∀ z, Reachable source x z → z ∉ m.map Prod.fst

private theorem noAlias_child {g : Graph T} {x b : Addr} {c : Cell T} {i : Nat}
    (h : NoAlias g x) (hc : g.cells x = some c) (hi : c.children[i]? = some b) :
    NoAlias g b := by
  intro p q z hp hq
  have := h (i :: p) (i :: q) z (.cons hc hi hp) (.cons hc hi hq)
  exact (List.cons.inj this).2

private theorem write_spec (g : Graph T) (a : Addr) (c old : Cell T) (cs : List Addr)
    (hold : g.cells a = some old) :
    ∃ g', writeCopiedCell g a c cs = .ok g' ∧
      g'.cells a = some (if c.degree = 0 then c else
        { old with degree := cs.length, op := c.op, children := cs }) ∧
      ∀ z, z ≠ a → g'.cells z = g.cells z := by
  simp only [writeCopiedCell, Heap.read, hold, bindOk, Heap.write]
  exact ⟨_, rfl, by simp, fun z hz => by simp [hz]⟩

private theorem walk_spec {T : Type} (source out0 : Graph T) (sharing : Bool)
    (dest : List Addr) (R : Addr)
    (hwf : GraphWF source R) (hac : Acyclic source R) (hn : dest.Nodup)
    (hinit : ∀ a ∈ dest, (out0.cells a).isSome) (hcap : CopyCapacity source R dest) :
    ∀ fuel x out j m, Reachable source R x → PathFuel source x fuel →
      CopyInv source out0 dest R out j m → PlainFresh source sharing x m →
      ∃ y out' j' m', copyWalk source sharing dest fuel x out j (cacheOf sharing m) =
          .ok (y, out', j', cacheOf sharing m') ∧
        CopyInv source out0 dest R out' j' m' ∧ m'.lookup x = some y ∧ Grows m m' ∧ j ≤ j' ∧
        (∀ a ∈ dest.take j, out'.cells a = out.cells a) ∧
        (∀ z ∈ m'.map Prod.fst, z ∈ m.map Prod.fst ∨ Reachable source x z) := by
  intro fuel
  induction fuel with
  | zero =>
    intro x out j m _ hf _ _
    exact absurd hf.pos (Nat.lt_irrefl 0)
  | succ fuel ih =>
    intro x out j m hx hf hinv hfr
    have hcase : (sharing = true ∧ ∃ y, m.lookup x = some y) ∨
        ((if sharing then (cacheOf sharing m).lookup x else none) = none ∧
          x ∉ m.map Prod.fst) := by
      cases sharing with
      | true =>
        cases hlook : m.lookup x with
        | some y => exact Or.inl ⟨rfl, y, rfl⟩
        | none =>
          refine Or.inr ⟨by simpa [cacheOf] using hlook, fun hk => ?_⟩
          obtain ⟨y, hy⟩ := lookup_of_key hk
          rw [hlook] at hy
          cases hy
      | false => exact Or.inr ⟨rfl, (hfr rfl).2 x (reach_refl' _ _)⟩
    rcases hcase with ⟨rfl, y, hlook⟩ | ⟨hmiss, hxk⟩
    · exact ⟨y, out, j, m, copyWalk_cacheHit source out dest fuel x j m y hlook, hinv, hlook,
        fun _ _ h => h, Nat.le_refl _, fun _ _ => rfl, fun z hz => Or.inl hz⟩
    · obtain ⟨c, hc, hlen⟩ := hwf x hx
      have hphase : ∃ cs h j' m',
          (if c.degree = 0 then
            (pure ([], out, j, cacheOf sharing m) : Jl (List Addr × Graph T × Nat × CopyCache))
          else c.children.foldlM (copyStep source sharing dest fuel)
            ([], out, j, cacheOf sharing m)) = .ok (cs, h, j', cacheOf sharing m') ∧
          CopyInv source out0 dest R h j' m' ∧ Grows m m' ∧ j ≤ j' ∧
          (∀ a ∈ dest.take j, h.cells a = out.cells a) ∧
          (∀ z ∈ m'.map Prod.fst, z ∈ m.map Prod.fst ∨ ∃ b ∈ c.children, Reachable source b z) ∧
          cs.length = c.children.length ∧
          ∀ (i : Nat) (b : Addr), c.children[i]? = some b →
            ∃ b', cs[i]? = some b' ∧ m'.lookup b = some b' := by
        by_cases hz : c.degree = 0
        · have hnil : c.children = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
          refine ⟨[], out, j, m, by rw [ite_eq_left hz]; rfl, hinv, fun _ _ h => h, Nat.le_refl _,
            fun _ _ => rfl, fun z hz => Or.inl hz, by simp [hnil], by simp [hnil]⟩
        · rw [ite_eq_right hz]
          have fold : ∀ (ys : List Addr) (off : Nat),
              (∀ (n : Nat) (b : Addr), ys[n]? = some b → c.children[off + n]? = some b) →
              ∀ as g i k, CopyInv source out0 dest R g i k →
              (sharing = false → ∀ z ∈ k.map Prod.fst, z ∈ m.map Prod.fst ∨
                ∃ (n : Nat) (b : Addr), n < off ∧ c.children[n]? = some b ∧
                  Reachable source b z) →
              ∃ bs g' i' k',
                ys.foldlM (copyStep source sharing dest fuel) (as, g, i, cacheOf sharing k) =
                  .ok (as ++ bs, g', i', cacheOf sharing k') ∧
                CopyInv source out0 dest R g' i' k' ∧ Grows k k' ∧ i ≤ i' ∧
                (∀ a ∈ dest.take i, g'.cells a = g.cells a) ∧
                (∀ z ∈ k'.map Prod.fst, z ∈ k.map Prod.fst ∨
                  ∃ (n : Nat) (b : Addr), off ≤ n ∧ c.children[n]? = some b ∧
                    Reachable source b z) ∧
                bs.length = ys.length ∧
                ∀ (n : Nat) (b : Addr), ys[n]? = some b →
                  ∃ b', bs[n]? = some b' ∧ k'.lookup b = some b' := by
            intro ys
            induction ys with
            | nil =>
              intro _ _ as g i k hk _
              refine ⟨[], g, i, k, ?_, hk, fun _ _ h => h, Nat.le_refl _, fun _ _ => rfl,
                fun z hz => Or.inl hz, rfl, by simp⟩
              simp only [List.foldlM_nil, List.append_nil]
              rfl
            | cons b ys iht =>
              intro off hys as g i k hk hkf
              have hb0 : c.children[off]? = some b := by simpa using hys 0 b rfl
              have hb : b ∈ c.children := List.mem_of_getElem? hb0
              have hbr : Reachable source R b := reach_trans' hx (reach_mem' hc hb)
              have hbf : PlainFresh source sharing b k := by
                intro hs
                obtain ⟨hna, hxf⟩ := hfr hs
                refine ⟨noAlias_child hna hc hb0, fun z hz hzk => ?_⟩
                rcases hkf hs z hzk with hzm | ⟨n, e, hlt, he, hez⟩
                · exact hxf z (reach_trans' (reach_mem' hc hb) hz) hzm
                · obtain ⟨p, hp⟩ := hz
                  obtain ⟨q, hq⟩ := hez
                  have := (List.cons.inj (hna (off :: p) (n :: q) z
                    (.cons hc hb0 hp) (.cons hc he hq))).1
                  omega
              obtain ⟨b', g1, i1, k1, hw, hk1, hl1, hg1, hi1, hp1, hn1⟩ :=
                ih b g i k hbr (hf.child hc hb) hk hbf
              have hys' : ∀ (n : Nat) (e : Addr), ys[n]? = some e →
                  c.children[off + 1 + n]? = some e := by
                intro n e he
                have := hys (n + 1) e (by simpa using he)
                rwa [show off + (n + 1) = off + 1 + n by omega] at this
              have hkf' : sharing = false → ∀ z ∈ k1.map Prod.fst, z ∈ m.map Prod.fst ∨
                  ∃ (n : Nat) (e : Addr), n < off + 1 ∧ c.children[n]? = some e ∧
                    Reachable source e z := by
                intro hs z hz
                rcases hn1 z hz with hz | hz
                · rcases hkf hs z hz with hz | ⟨n, e, hlt, he, hez⟩
                  · exact Or.inl hz
                  · exact Or.inr ⟨n, e, by omega, he, hez⟩
                · exact Or.inr ⟨off, b, by omega, hb0, hz⟩
              obtain ⟨bs, g2, i2, k2, hw2, hk2, hg2, hi2, hp2, hn2, hlen2, hrel2⟩ :=
                iht (off + 1) hys' (as ++ [b']) g1 i1 k1 hk1 hkf'
              refine ⟨b' :: bs, g2, i2, k2, ?_, hk2, fun u v h => hg2 _ _ (hg1 _ _ h),
                by omega, ?_, ?_, by simp [hlen2], ?_⟩
              · rw [List.foldlM_cons]
                simp only [copyStep, hw, bindOk, pure, Except.pure]
                rw [hw2]
                simp
              · intro a ha
                rw [hp2 a (take_mono ha hi1), hp1 a ha]
              · intro z hz
                rcases hn2 z hz with hz | ⟨n, e, hle, he, hez⟩
                · rcases hn1 z hz with hz | hz
                  · exact Or.inl hz
                  · exact Or.inr ⟨off, b, Nat.le_refl _, hb0, hz⟩
                · exact Or.inr ⟨n, e, by omega, he, hez⟩
              · intro n e he
                cases n with
                | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at he
                  subst he
                  exact ⟨b', rfl, hg2 _ _ hl1⟩
                | succ n =>
                  simp only [List.getElem?_cons_succ] at he
                  obtain ⟨e', he', hle⟩ := hrel2 n e he
                  exact ⟨e', by simpa using he', hle⟩
          obtain ⟨bs, g', i', k', hw, hk', hg', hi', hp', hn', hlen', hrel'⟩ :=
            fold c.children 0 (fun n b h => by simpa using h) [] out j m hinv
              (fun _ z hz => Or.inl hz)
          rw [List.nil_append] at hw
          refine ⟨bs, g', i', k', hw, hk', hg', hi', hp', ?_, hlen', hrel'⟩
          intro z hz
          rcases hn' z hz with hz | ⟨n, e, _, he, hez⟩
          · exact Or.inl hz
          · exact Or.inr ⟨e, List.mem_of_getElem? he, hez⟩
      obtain ⟨cs, h, j', m', hph, hinv', hg', hj', hp', hnew', hcsl, hrel⟩ := hphase
      have hxk' : x ∉ m'.map Prod.fst := by
        intro hk
        rcases hnew' x hk with hk | ⟨b, hb, hbx⟩
        · exact hxk hk
        · obtain ⟨n, hn'⟩ := List.mem_iff_getElem?.mp hb
          obtain ⟨p, hp⟩ := hbx
          have := hac x hx (n :: p) (.cons hc hn' hp)
          cases this
      have hlt : j' < dest.length := by
        have := hcap (x :: m'.map Prod.fst) (List.nodup_cons.mpr ⟨hxk', hinv'.keys⟩) (by
          intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hx
          · exact hinv'.reach z hz)
        simp only [List.length_cons, List.length_map, hinv'.length] at this
        omega
      obtain ⟨a, ha⟩ : ∃ a, dest[j']? = some a := ⟨dest[j'], List.getElem?_eq_getElem hlt⟩
      have hfr : h.cells a = out0.cells a :=
        hinv'.frame a (fun hm => take_ne hn hm ha (Nat.le_refl _) rfl)
      obtain ⟨old, hold⟩ : ∃ old, h.cells a = some old := by
        rw [hfr]
        exact Option.isSome_iff_exists.mp (hinit a (List.mem_of_getElem? ha))
      obtain ⟨h', hw, hwa, hwo⟩ := write_spec h a c old cs hold
      have hgrow : Grows m' ((x, a) :: m') := grows_push hxk'
      have hcc : CellCorr ((x, a) :: m') c (if c.degree = 0 then c else
          { old with degree := cs.length, op := c.op, children := cs }) := by
        by_cases hz : c.degree = 0
        · have hnil : c.children = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
          refine ⟨fun _ => ite_eq_left hz, fun h => absurd hz h, by rw [ite_eq_left hz], ?_⟩
          intro i b hb
          simp [hnil] at hb
        · rw [ite_eq_right hz]
          refine ⟨fun h => absurd h hz, fun _ => ⟨rfl, rfl⟩, hcsl, fun i b hb => ?_⟩
          obtain ⟨b', h1, h2⟩ := hrel i b hb
          exact ⟨b', h1, hgrow _ _ h2⟩
      refine ⟨a, h', j' + 1, (x, a) :: m', ?_, hinv'.push hn hxk' hx ha hc hwa hwo hcc,
        ?_, fun z y hzy => hgrow _ _ (hg' _ _ hzy), by omega, ?_, ?_⟩
      · rw [copyWalk_miss source sharing dest fuel x out j _ hmiss,
          show source.read x = .ok c by simp [Heap.read, hc]]
        simp only [bindOk]
        have hslot : destinationSlot dest j' = .ok a := by simp [destinationSlot, ha]
        by_cases hz : c.degree = 0
        · rw [ite_eq_left hz] at hph
          rw [ite_eq_left hz, hph]
          simp only [bindOk, hslot, hw]
          cases sharing <;> rfl
        · rw [ite_eq_right hz] at hph
          rw [ite_eq_right hz, hph]
          simp only [bindOk, hslot, hw]
          cases sharing <;> rfl
      · simp
      · intro z hz
        rw [hwo z (take_ne hn hz ha hj'), hp' z hz]
      · intro z hz
        simp only [List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inr (reach_refl' _ _)
        · rcases hnew' z hz with h1 | ⟨b, hb, hbz⟩
          · exact Or.inl h1
          · exact Or.inr (reach_trans' (reach_mem' hc hb) hbz)

/-! ## Reading the final copy -/

private theorem unfold_succ {g : Graph T} {f : Nat} {a : Addr} {c : Cell T}
    (hc : g.cells a = some c) :
    g.unfold (f + 1) a = (do
      if c.children.length ≠ c.degree then none
      else if c.degree = 0 then
        if c.constant then return .const (← c.val)
        else return .feature c.feature
      else return .branch c.op (← c.children.mapM (g.unfold f)) : Option (Tree T)) := by
  simp only [Graph.unfold, hc]
  rfl

private theorem mapM_corr {F G : Addr → Option (Tree T)} :
    ∀ (l l' : List Addr), l'.length = l.length →
      (∀ (i : Nat) (b : Addr), l[i]? = some b → ∃ b', l'[i]? = some b' ∧ F b' = G b) →
      l'.mapM F = l.mapM G
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: l, b' :: l', h, hr => by
    obtain ⟨e, he, hfe⟩ := hr 0 b rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    rw [List.mapM_cons, List.mapM_cons, hfe, mapM_corr l l' (by simpa using h)
      (fun i x hx => by
        obtain ⟨e, he, hfe⟩ := hr (i + 1) x (by simpa using hx)
        exact ⟨e, by simpa using he, hfe⟩)]

private theorem unfold_copy {source out0 out : Graph T} {dest R j m}
    (hwf : GraphWF source R) (hinv : CopyInv source out0 dest R out j m) :
    ∀ f x y, m.lookup x = some y → out.unfold f y = source.unfold f x := by
  intro f
  induction f with
  | zero => intro x y _; rfl
  | succ f ih =>
    intro x y hl
    obtain ⟨c, c', hc, hc', hcc⟩ := hinv.corr x y hl
    obtain ⟨c0, hc0, hlen⟩ := hwf x (hinv.reach x (key_of_lookup hl))
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    rw [unfold_succ hc', unfold_succ hc]
    have h1 : ¬ (c.children.length ≠ c.degree) := fun h => h hlen
    by_cases hz : c.degree = 0
    · rw [hcc.leaf hz, ite_eq_right h1, ite_eq_right h1, ite_eq_left hz, ite_eq_left hz]
    · obtain ⟨hd', hop⟩ := hcc.branch hz
      have hlen' := hcc.len
      have h2 : ¬ (c'.children.length ≠ c'.degree) := fun h => h hd'.symm
      have h3 : ¬ c'.degree = 0 := by omega
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hz, ite_eq_right h3, hop,
        mapM_corr c.children c'.children hlen' (fun i b hb => by
          obtain ⟨b', hb', hlb⟩ := hcc.kids i b hb
          exact ⟨b', hb', ih b b' hlb⟩)]

private theorem path_det {g : Graph T} {a : Addr} {p : List Nat} {z z' : Addr}
    (h : Path g a p z) (h' : Path g a p z') : z = z' := by
  induction h generalizing z' with
  | nil => cases h'; rfl
  | cons hc hi _ ih =>
    cases h' with
    | cons hc' hi' hp' =>
      rw [hc] at hc'
      obtain rfl := Option.some.inj hc'
      rw [hi] at hi'
      obtain rfl := Option.some.inj hi'
      exact ih hp'

private theorem path_fwd {source out0 out : Graph T} {dest R j m}
    (hinv : CopyInv source out0 dest R out j m) {x : Addr} {p : List Nat} {z : Addr}
    (hp : Path source x p z) :
    ∀ y, m.lookup x = some y → ∃ z', Path out y p z' ∧ m.lookup z = some z' := by
  induction hp with
  | nil a => intro y hy; exact ⟨y, .nil y, hy⟩
  | cons hc hi _ ih =>
    intro y hy
    obtain ⟨c0, c', hc0, hc', hcc⟩ := hinv.corr _ y hy
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    obtain ⟨b', hb', hl⟩ := hcc.kids _ _ hi
    obtain ⟨z', hz', hlz⟩ := ih b' hl
    exact ⟨z', .cons hc' hb' hz', hlz⟩

private theorem path_bwd {source out0 out : Graph T} {dest R j m}
    (hinv : CopyInv source out0 dest R out j m) {y : Addr} {p : List Nat} {z' : Addr}
    (hp : Path out y p z') :
    ∀ x, m.lookup x = some y → ∃ z, Path source x p z ∧ m.lookup z = some z' := by
  induction hp with
  | nil a => intro x hx; exact ⟨x, .nil x, hx⟩
  | @cons a b z i p c' hc' hi _ ih =>
    intro x hx
    obtain ⟨c, c'', hc, hc'', hcc⟩ := hinv.corr x a hx
    rw [hc'] at hc''
    obtain rfl := Option.some.inj hc''
    have hlt : i < c.children.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      rw [hcc.len] at this
      exact this
    obtain ⟨b0, hb0⟩ : ∃ b0, c.children[i]? = some b0 :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨b', hb', hl⟩ := hcc.kids i b0 hb0
    rw [hi] at hb'
    obtain rfl := Option.some.inj hb'
    obtain ⟨z, hz, hlz⟩ := ih b0 hl
    exact ⟨z, .cons hc hb0 hz, hlz⟩

private theorem nodup_length_le : ∀ (l l' : List Addr), l.Nodup → (∀ x ∈ l, x ∈ l') →
    l.length ≤ l'.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l', hn, hs => by
    have ha : a ∈ l' := hs a (by simp)
    obtain ⟨hna, hnl⟩ := List.nodup_cons.mp hn
    have := nodup_length_le l (l'.erase a) hnl (fun x hx =>
      (List.mem_erase_of_ne (fun h : x = a => hna (h ▸ hx))).mpr
        (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ha] at this
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Duplicate-free inventories of one reachable set have one length. -/
theorem ReachInventory.length_eq {g : Graph T} {root : Addr} {L L' : List Addr}
    (h : ReachInventory g root L) (h' : ReachInventory g root L') : L.length = L'.length := by
  have h1 := nodup_length_le L L' h.1 (fun x hx => (h'.2 x).mpr ((h.2 x).mp hx))
  have h2 := nodup_length_le L' L h'.1 (fun x hx => (h.2 x).mpr ((h'.2 x).mp hx))
  omega

/-! ## Registered property -/

/-- src/NodePreallocation.jl:35-65 with src/base.jl:96-158, for both `GraphNode`
(`sharing = true`, identity cache) and plain `Node` (`sharing = false`, which
requires unique child paths, `NoAlias`). For every source type, well-formed source
graph with adequate traversal fuel (which makes the reachable graph finite and
acyclic, see `PathFuel.acyclic`) whose constant leaves hold values (the source
unfolds to a tree), and duplicate-free initialized destination with a
slot for each distinct reachable source object, `copy_into!` succeeds; the copy
unfolds to the source tree at every fuel; source paths and destination paths
correspond and reach the same object together; each copied leaf is the source leaf
cell and each copied branch keeps the source degree and operator; the cursor equals
the number of distinct reachable source objects; every copied object lies in the
consumed slots; and every other destination cell is unchanged. The source graph is
a separate input heap and is never written. -/
def CopySharing : Prop :=
  ∀ (T : Type) (sharing : Bool) (source out : Graph T) (dest : List Addr) (fuel root : Nat),
    GraphWF source root → PathFuel source root fuel → (∃ t, source.unfold fuel root = some t) →
    (sharing = false → NoAlias source root) →
    dest.Nodup → (∀ a ∈ dest, (out.cells a).isSome) → CopyCapacity source root dest →
    ∃ r out' cursor cache,
      copyInto source sharing dest out fuel root = .ok (r, out', cursor, cache) ∧
      (∀ f, out'.unfold f r = source.unfold f root) ∧
      (∀ p x, Path source root p x → ∃ x', Path out' r p x') ∧
      (∀ p x', Path out' r p x' → ∃ x, Path source root p x) ∧
      (∀ p q x y x' y', Path source root p x → Path source root q y →
        Path out' r p x' → Path out' r q y' → (x = y ↔ x' = y')) ∧
      (∀ p x y c, Path source root p x → Path out' r p y → source.cells x = some c →
        (c.degree = 0 → out'.cells y = some c) ∧
        (c.degree ≠ 0 → ∃ c', out'.cells y = some c' ∧ c'.degree = c.degree ∧ c'.op = c.op)) ∧
      (∃ L, ReachInventory source root L) ∧
      (∀ L, ReachInventory source root L → cursor = L.length) ∧
      (∀ x, Reachable out' r x → x ∈ dest.take cursor) ∧
      (∀ x, x ∉ dest.take cursor → out'.cells x = out.cells x)

theorem copySharing_proven : CopySharing := by
  intro T sharing source out dest fuel root hwf hfuel _ hplain hn hinit hcap
  obtain ⟨r, out', j', m', hrun, hinv, hroot, -, -, -, -⟩ :=
    walk_spec source out sharing dest root hwf hfuel.acyclic hn hinit hcap fuel root out 0 []
      (reach_refl' _ _) hfuel (CopyInv.init source out dest root)
      (fun hs => ⟨hplain hs, fun _ _ h => by simp at h⟩)
  have hempty : cacheOf sharing ([] : CopyCache) = [] := by cases sharing <;> rfl
  rw [hempty] at hrun
  have hiff : ∀ z, z ∈ m'.map Prod.fst ↔ Reachable source root z := fun z =>
    ⟨hinv.reach z, fun ⟨_, hp⟩ => by
      obtain ⟨_, _, hz⟩ := path_fwd hinv hp r hroot
      exact key_of_lookup hz⟩
  have hinvK : ReachInventory source root (m'.map Prod.fst) := ⟨hinv.keys, hiff⟩
  refine ⟨r, out', j', cacheOf sharing m', hrun, fun f => unfold_copy hwf hinv f root r hroot,
    ?_, ?_, ?_, ?_,
    ⟨_, hinvK⟩, ?_, ?_, hinv.frame⟩
  · intro p x hp
    obtain ⟨x', hx', _⟩ := path_fwd hinv hp r hroot
    exact ⟨x', hx'⟩
  · intro p x' hp
    obtain ⟨x, hx, _⟩ := path_bwd hinv hp root hroot
    exact ⟨x, hx⟩
  · intro p q x y x' y' hpx hqy hpx' hqy'
    obtain ⟨x'', hx'', hlx⟩ := path_fwd hinv hpx r hroot
    obtain ⟨y'', hy'', hly⟩ := path_fwd hinv hqy r hroot
    rw [path_det hpx' hx'', path_det hqy' hy'']
    constructor
    · rintro rfl
      exact Option.some.inj (hlx.symm.trans hly)
    · intro he
      subst he
      exact lookup_inj (hinv.valsNodup hn) hlx hly
  · intro p x y c hpx hpy hc
    obtain ⟨y'', hy'', hl⟩ := path_fwd hinv hpx r hroot
    rw [path_det hpy hy'']
    obtain ⟨c0, c', hc0, hc', hcc⟩ := hinv.corr x y'' hl
    rw [hc] at hc0
    obtain rfl := Option.some.inj hc0
    obtain ⟨c1, hc1, hlen⟩ := hwf x ⟨p, hpx⟩
    rw [hc] at hc1
    obtain rfl := Option.some.inj hc1
    refine ⟨fun hz => by rw [hc', hcc.leaf hz], fun hz => ⟨c', hc', ?_, (hcc.branch hz).2⟩⟩
    have := (hcc.branch hz).1
    have := hcc.len
    omega
  · intro L hL
    rw [← hinvK.length_eq hL, List.length_map, hinv.length]
  · intro x ⟨p, hp⟩
    obtain ⟨_, _, hw⟩ := path_bwd hinv hp root hroot
    exact hinv.slot hw

/-! ## Satisfiable preconditions on a shared source -/

private theorem aliasPaths {p : List Nat} {z : Addr} (h : Path aliasGraph 1 p z) :
    (p = [] ∧ z = 1) ∨ (∃ i, p = [i] ∧ z = 0) := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons _ b _ i q c hc hi hp =>
    have hc1 : aliasGraph.cells 1 = some (operatorCell 1 [0, 0]) := rfl
    rw [hc1] at hc
    obtain rfl := Option.some.inj hc
    have hb : b = 0 := by
      have := List.mem_of_getElem? hi
      simpa [operatorCell] using this
    subst hb
    cases hp with
    | nil => exact Or.inr ⟨i, rfl, rfl⟩
    | cons hc' hi' _ =>
      have hc0 : aliasGraph.cells 0 = some (constantCell 1) := rfl
      rw [hc0] at hc'
      obtain rfl := Option.some.inj hc'
      simp [constantCell] at hi'

example : GraphWF aliasGraph 1 ∧ PathFuel aliasGraph 1 2 ∧ (∃ t, aliasGraph.unfold 2 1 = some t) ∧
    (emptySlots 2).1.Nodup ∧ (∀ a ∈ (emptySlots 2).1, ((emptySlots 2).2.cells a).isSome) ∧
    CopyCapacity aliasGraph 1 (emptySlots 2).1 := by
  have hreach : ∀ x, Reachable aliasGraph 1 x → x = 0 ∨ x = 1 := by
    intro x ⟨p, hp⟩
    rcases aliasPaths hp with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  refine ⟨?_, ?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases hreach x hx with rfl | rfl
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩
  · intro p z hp
    rcases aliasPaths hp with ⟨rfl, _⟩ | ⟨i, rfl, _⟩ <;> simp
  · show ([0, 1] : List Nat).Nodup
    decide
  · intro a ha
    change a ∈ [0, 1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  · intro L hL hr
    have := nodup_length_le L [0, 1] hL (fun x hx => by
      rcases hreach x (hr x hx) with rfl | rfl <;> simp)
    exact this

end DynExpr.NodeUtils
