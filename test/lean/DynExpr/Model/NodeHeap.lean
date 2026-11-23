import DynExpr.Runtime.Heap
import DynExpr.Model.Tree

namespace DynExpr

/-- Active fields of the mutable `Node{T,D}` and `GraphNode{T,D}` objects in
`src/Node.jl:74-90`. `none` records an unset value field. Only active children
are stored; the capacity and integer-width constraints belong to `Tree.WF`. -/
structure Cell (T : Type) where
  degree : Nat
  constant : Bool
  val : Option T
  feature : Nat
  op : Nat
  children : List Addr

/-- Object identities and mutable node contents (`src/Node.jl:74-90`). -/
abbrev Graph (T : Type) := Heap (Cell T)

namespace Graph

private def constCell (v : T) : Cell T := ⟨0, true, some v, 0, 0, []⟩
private def featureCell (i : Nat) : Cell T := ⟨0, false, none, i, 0, []⟩
private def branchCell (op : Nat) (cs : List Addr) : Cell T :=
  ⟨cs.length, false, none, 0, op, cs⟩

/-- Unfold mutable child references (`src/Node.jl:95-98`). Fuel counts node
levels, with leaves requiring one unit. Missing references, inconsistent active
child counts, and unset constant values fail rather than inventing a tree. -/
def unfold (g : Graph T) : Nat → Addr → Option (Tree T)
  | 0, _ => none
  | fuel + 1, a => do
    let c ← g.cells a
    if c.children.length ≠ c.degree then none
    else if c.degree = 0 then
      if c.constant then return .const (← c.val)
      else return .feature c.feature
    else return .branch c.op (← c.children.mapM (unfold g fuel))

/-- An indexed child path through active references (`src/Node.jl:81,95-98`).
The empty path visits the root itself, even if its address is missing. -/
inductive Path (g : Graph T) : Addr → List Nat → Addr → Prop where
  | nil (a) : Path g a [] a
  | cons {a b z i p c} : g.cells a = some c → c.children[i]? = some b →
      Path g b p z → Path g a (i :: p) z

/-- An address reachable along active child references (`src/Node.jl:95-98`). -/
def Reachable (g : Graph T) (root a : Addr) : Prop := ∃ p, Path g root p a

/-- No reachable object lies on a nonempty child cycle. This is the finite
acyclic input condition for recursive node traversal (`src/base.jl:77-158`). -/
def Acyclic (g : Graph T) (root : Addr) : Prop :=
  ∀ a, Reachable g root a → ∀ p, Path g a p a → p = []

/-- Every reachable address has a unique indexed child path from the root.
This excludes both repeated references and shared descendants, distinguishing
unshared trees from legal `GraphNode` sharing (`src/Node.jl:74-90`). -/
def NoAlias (g : Graph T) (root : Addr) : Prop :=
  ∀ p q a, Path g root p a → Path g root q a → p = q

mutual
  /-- Allocate a fresh unshared copy of a pure tree, as node constructors in
  `src/Node.jl:86,392-414` do. Children are allocated from left to right before
  their parent, so the root is the last allocated object. Existing cells remain
  unchanged. Empty branches are allocated too, but only `Tree.Representable`
  trees can be recovered by `unfold`. -/
  def ofTree (g : Graph T) : Tree T → Addr × Graph T
    | .const v => g.alloc (constCell v)
    | .feature i => g.alloc (featureCell i)
    | .branch op cs =>
      let (as, h) := ofForest g cs
      h.alloc (branchCell op as)
  /-- Left-to-right child allocation for `ofTree` (`src/Node.jl:81,392-414`). -/
  def ofForest (g : Graph T) : List (Tree T) → List Addr × Graph T
    | [] => ([], g)
    | c :: cs =>
      let (a, h) := ofTree g c
      let (as, k) := ofForest h cs
      (a :: as, k)
end

private def Preserves (g h : Graph T) (n : Nat) : Prop :=
  ∀ a, a < n → h.cells a = g.cells a

private theorem preserves_refl (g : Graph T) (n) : Preserves g g n := by
  intro a ha; rfl

private theorem preserves_trans {g h k : Graph T} {n m}
    (gh : Preserves g h n) (hk : Preserves h k m) (hnm : n ≤ m) :
    Preserves g k n := by
  intro a ha
  rw [hk a (by omega), gh a ha]

private theorem alloc_preserves (g : Graph T) (c : Cell T) :
    Preserves g (g.alloc c).2 g.next := by
  intro a ha
  simp [Heap.alloc, show a ≠ g.next by omega]

mutual
  private def Layout (g : Graph T) (lo hi a : Nat) : Tree T → Prop
    | .const v => a = lo ∧ hi = lo + 1 ∧ g.cells a = some (constCell v)
    | .feature i => a = lo ∧ hi = lo + 1 ∧ g.cells a = some (featureCell i)
    | .branch op cs => ∃ mid as, a = mid ∧ hi = mid + 1 ∧
        ForestLayout g lo mid as cs ∧ g.cells a = some (branchCell op as)
  private def ForestLayout (g : Graph T) (lo hi : Nat) : List Addr → List (Tree T) → Prop
    | [], [] => hi = lo
    | a :: as, t :: ts => ∃ mid, Layout g lo mid a t ∧ ForestLayout g mid hi as ts
    | _, _ => False
end

private theorem layout_bounds (t : Tree T) :
    ∀ {g lo hi a}, Layout g lo hi a t → lo ≤ a ∧ a < hi := by
  induction t using Tree.induction with
  | hc v => intro g lo hi a h; obtain ⟨rfl, rfl, _⟩ := h; omega
  | hf i => intro g lo hi a h; obtain ⟨rfl, rfl, _⟩ := h; omega
  | hb op cs ih =>
    intro g lo hi a h
    obtain ⟨mid, as, rfl, rfl, hf, _⟩ := h
    suffices lo ≤ a by omega
    have bound : ∀ ts, (∀ t ∈ ts, ∀ {lo hi a}, Layout g lo hi a t → lo ≤ a ∧ a < hi) →
        ∀ {lo hi as}, ForestLayout g lo hi as ts → lo ≤ hi := by
      intro ts ht
      induction ts with
      | nil => intro lo hi as hf; cases as <;> simp_all [ForestLayout]
      | cons t ts iht =>
        intro lo hi as hf
        cases as with
        | nil => exact False.elim hf
        | cons a as =>
          obtain ⟨m, hl, hf⟩ := hf
          have := ht t (by simp) hl
          have := iht (fun c hc => ht c (by simp [hc])) hf
          omega
    exact bound cs (fun t ht => ih t ht) hf

private theorem forest_bounds {g : Graph T} {lo hi as ts}
    (hf : ForestLayout g lo hi as ts) : lo ≤ hi := by
  induction ts generalizing lo as with
  | nil => cases as <;> simp_all [ForestLayout]
  | cons t ts ih =>
    cases as with
    | nil => exact False.elim hf
    | cons a as =>
      obtain ⟨m, hl, hf⟩ := hf
      have := layout_bounds t hl
      have := ih hf
      omega

private theorem layout_preserves (t : Tree T) :
    ∀ {g h lo hi a}, Layout g lo hi a t → Preserves g h hi → Layout h lo hi a t := by
  induction t using Tree.induction with
  | hc v =>
    intro g h lo hi a hl hp
    obtain ⟨rfl, rfl, hc⟩ := hl
    exact ⟨rfl, rfl, by rw [hp a (by omega), hc]⟩
  | hf i =>
    intro g h lo hi a hl hp
    obtain ⟨rfl, rfl, hc⟩ := hl
    exact ⟨rfl, rfl, by rw [hp a (by omega), hc]⟩
  | hb op cs ih =>
    intro g h lo hi a hl hp
    obtain ⟨mid, as, rfl, rfl, hf, hc⟩ := hl
    refine ⟨a, as, rfl, rfl, ?_, by rw [hp a (by omega), hc]⟩
    have transfer : ∀ ts, (∀ t ∈ ts, ∀ {lo hi a}, Layout g lo hi a t →
        Preserves g h hi → Layout h lo hi a t) →
        ∀ {lo hi as}, ForestLayout g lo hi as ts →
        Preserves g h hi → ForestLayout h lo hi as ts := by
      intro ts ht
      induction ts with
      | nil => intro lo hi as hf _; cases as <;> simp_all [ForestLayout]
      | cons t ts iht =>
        intro lo hi as hf hp
        cases as with
        | nil => exact False.elim hf
        | cons a as =>
          obtain ⟨m, hl, hf⟩ := hf
          have hm := forest_bounds hf
          refine ⟨m, ht t (by simp) hl ?_, iht (fun c hc => ht c (by simp [hc])) hf hp⟩
          intro b hb
          exact hp b (by omega)
    exact transfer cs (fun t ht => ih t ht) hf (fun b hb => hp b (by omega))

private theorem forest_preserves {g h : Graph T} {lo hi as ts}
    (hf : ForestLayout g lo hi as ts) (hp : Preserves g h hi) :
    ForestLayout h lo hi as ts := by
  induction ts generalizing lo as with
  | nil => cases as <;> simp_all [ForestLayout]
  | cons t ts ih =>
    cases as with
    | nil => exact False.elim hf
    | cons a as =>
      obtain ⟨m, hl, hf⟩ := hf
      have hm := forest_bounds hf
      exact ⟨m, layout_preserves t hl (fun b hb => hp b (by omega)), ih hf⟩

private theorem ofTree_layout (t : Tree T) : ∀ g : Graph T,
    Layout (ofTree g t).2 g.next (ofTree g t).2.next (ofTree g t).1 t ∧
    Preserves g (ofTree g t).2 g.next ∧ g.next ≤ (ofTree g t).2.next := by
  induction t using Tree.induction with
  | hc v =>
    intro g
    refine ⟨?_, alloc_preserves g _, ?_⟩
    · simp [ofTree, Layout, Heap.alloc]
    · simp [ofTree, Heap.alloc]
  | hf i =>
    intro g
    refine ⟨?_, alloc_preserves g _, ?_⟩
    · simp [ofTree, Layout, Heap.alloc]
    · simp [ofTree, Heap.alloc]
  | hb op cs ih =>
    intro g
    have build : ∀ ts, (∀ t ∈ ts, ∀ g : Graph T,
        Layout (ofTree g t).2 g.next (ofTree g t).2.next (ofTree g t).1 t ∧
        Preserves g (ofTree g t).2 g.next ∧ g.next ≤ (ofTree g t).2.next) →
        ∀ g : Graph T,
        ForestLayout (ofForest g ts).2 g.next (ofForest g ts).2.next (ofForest g ts).1 ts ∧
        Preserves g (ofForest g ts).2 g.next ∧ g.next ≤ (ofForest g ts).2.next := by
      intro ts ht
      induction ts with
      | nil => intro g; exact ⟨rfl, preserves_refl _ _, Nat.le_refl _⟩
      | cons t ts iht =>
        intro g
        obtain ⟨hl, hp, hm⟩ := ht t (by simp) g
        obtain ⟨hf, hq, hn⟩ := iht (fun c hc => ht c (by simp [hc])) (ofTree g t).2
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨(ofTree g t).2.next, layout_preserves t hl hq, hf⟩
        · exact preserves_trans hp hq hm
        · exact Nat.le_trans hm hn
    obtain ⟨hf, hp, hm⟩ := build cs ih g
    let h := (ofForest g cs).2
    let as := (ofForest g cs).1
    change Layout (h.alloc (branchCell op as)).2 g.next
      (h.alloc (branchCell op as)).2.next (h.alloc (branchCell op as)).1 (.branch op cs) ∧ _
    refine ⟨⟨h.next, as, rfl, rfl, forest_preserves hf (alloc_preserves h _), ?_⟩,
      preserves_trans hp (alloc_preserves h _) hm, ?_⟩
    · simp [Heap.alloc]
    · change g.next ≤ h.next + 1
      exact Nat.le_trans hm (Nat.le_succ _)

/-- Fresh construction preserves all previous node contents (src/Node.jl:86). -/
theorem cells_ofTree (g : Graph T) (t : Tree T) (a : Addr) (ha : a < g.next) :
    (g.ofTree t).2.cells a = g.cells a :=
  (ofTree_layout t g).2.1 a ha

/-- Reads through previously allocated identities are unchanged by fresh
construction (src/Node.jl:86,214). -/
theorem read_ofTree (g : Graph T) (t : Tree T) (a : Addr) (ha : a < g.next) :
    Heap.read (g.ofTree t).2 a = Heap.read g a := by
  simp [Heap.read, cells_ofTree g t a ha]

private theorem forest_length {g : Graph T} {lo hi as ts}
    (hf : ForestLayout g lo hi as ts) : as.length = ts.length := by
  induction ts generalizing lo as with
  | nil => cases as <;> simp_all [ForestLayout]
  | cons t ts ih =>
    cases as with
    | nil => exact False.elim hf
    | cons a as =>
      obtain ⟨m, _, hf⟩ := hf
      simpa using ih hf

private theorem depth_le_max (ts : List (Tree T)) (t : Tree T) (ht : t ∈ ts) :
    t.depth ≤ (ts.map Tree.depth).foldr max 0 := by
  induction ts with
  | nil => simp at ht
  | cons c cs ih =>
    simp only [List.mem_cons] at ht
    simp only [List.map_cons, List.foldr_cons]
    rcases ht with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

private theorem layout_unfold (t : Tree T) : ∀ {g lo hi a fuel},
    Layout g lo hi a t → t.Representable → t.depth ≤ fuel → unfold g fuel a = some t := by
  induction t using Tree.induction with
  | hc v =>
    intro g lo hi a fuel hl _ hd
    obtain ⟨_, _, hc⟩ := hl
    cases fuel with
    | zero => simp [Tree.depth] at hd
    | succ f => simp [unfold, hc, constCell]
  | hf i =>
    intro g lo hi a fuel hl _ hd
    obtain ⟨_, _, hc⟩ := hl
    cases fuel with
    | zero => simp [Tree.depth] at hd
    | succ f => simp [unfold, hc, featureCell]
  | hb op cs ih =>
    intro g lo hi a fuel hl hr hd
    obtain ⟨mid, as, _, _, hf, hc⟩ := hl
    simp only [Tree.Representable] at hr
    obtain ⟨hpos, hr⟩ := hr
    cases fuel with
    | zero => have := Tree.depth_pos (Tree.branch op cs); omega
    | succ f =>
      have hn : as.length ≠ 0 := by have := forest_length hf; omega
      have decode : ∀ ts, (∀ t ∈ ts, ∀ {lo hi a}, Layout g lo hi a t →
          t.Representable → t.depth ≤ f → unfold g f a = some t) →
          ∀ {lo hi as}, ForestLayout g lo hi as ts →
          (∀ t ∈ ts, t.Representable) → (∀ t ∈ ts, t.depth ≤ f) →
          as.mapM (unfold g f) = some ts := by
        intro ts ht
        induction ts with
        | nil =>
          intro lo hi as hf _ _
          cases as <;> simp_all [ForestLayout]
        | cons t ts iht =>
          intro lo hi as hf hr hd
          cases as with
          | nil => exact False.elim hf
          | cons a as =>
            obtain ⟨m, hl, hf⟩ := hf
            have hhead := ht t (by simp) hl (hr t (by simp)) (hd t (by simp))
            have htail := iht (fun c hc => ht c (by simp [hc])) hf
              (fun c hc => hr c (by simp [hc])) (fun c hc => hd c (by simp [hc]))
            simp [List.mapM_cons, hhead, htail]
      have hmap := decode cs (fun t ht => ih t ht) hf hr (by
        intro t ht
        have hm := depth_le_max cs t ht
        simp only [Tree.depth] at hd
        omega)
      simp [unfold, hc, branchCell, hn, hmap]

/-- Fresh node construction unfolds to the original representable tree with
at least its depth in fuel (src/Node.jl:86,95-98,392-414). -/
theorem unfold_ofTree (g : Graph T) (t : Tree T) (hr : t.Representable)
    (fuel : Nat) (hf : t.depth ≤ fuel) :
    (g.ofTree t).2.unfold fuel (g.ofTree t).1 = some t :=
  layout_unfold t (ofTree_layout t g).1 hr hf

private theorem forest_path_bounds (g : Graph T) (ts : List (Tree T))
    (ht : ∀ t ∈ ts, ∀ {lo hi a p z}, Layout g lo hi a t → Path g a p z → lo ≤ z ∧ z < hi) :
    ∀ {lo hi as} {i : Nat} {b p z}, ForestLayout g lo hi as ts → as[i]? = some b →
    Path g b p z → lo ≤ z ∧ z < hi := by
  induction ts with
  | nil =>
    intro lo hi as i b p z hf hb _
    cases as <;> simp_all [ForestLayout]
  | cons t ts ih =>
    intro lo hi as i b p z hf hb hp
    cases as with
    | nil => exact False.elim hf
    | cons a as =>
      obtain ⟨m, hl, hf⟩ := hf
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst b
        have hz : lo ≤ z ∧ z < m := ht t (by simp) hl hp
        have hm := forest_bounds hf
        exact ⟨hz.1, Nat.lt_of_lt_of_le hz.2 hm⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hb
        have hz : m ≤ z ∧ z < hi := ih (fun c hc => ht c (by simp [hc])) hf hb hp
        have hm := layout_bounds t hl
        exact ⟨Nat.le_trans (Nat.le_trans hm.1 (Nat.le_of_lt hm.2)) hz.1, hz.2⟩

private theorem layout_path_bounds (t : Tree T) : ∀ {g lo hi a p z},
    Layout g lo hi a t → Path g a p z → lo ≤ z ∧ z < hi := by
  induction t using Tree.induction with
  | hc v =>
    intro g lo hi a p z hl hp
    have hbounds := layout_bounds _ hl
    obtain ⟨_, _, hc⟩ := hl
    cases hp with
    | nil => exact hbounds
    | cons hcell hget _ =>
      rw [hc] at hcell
      cases hcell
      simp [constCell] at hget
  | hf i =>
    intro g lo hi a p z hl hp
    have hbounds := layout_bounds _ hl
    obtain ⟨_, _, hc⟩ := hl
    cases hp with
    | nil => exact hbounds
    | cons hcell hget _ =>
      rw [hc] at hcell
      cases hcell
      simp [featureCell] at hget
  | hb op cs ih =>
    intro g lo hi a p z hl hp
    have hbounds := layout_bounds _ hl
    obtain ⟨mid, as, _, hhi, hf, hc⟩ := hl
    cases hp with
    | nil => exact hbounds
    | cons hcell hget hp =>
      rw [hc] at hcell
      cases hcell
      have hz : lo ≤ z ∧ z < mid := forest_path_bounds g cs (fun t ht => ih t ht) hf hget hp
      exact ⟨hz.1, Nat.lt_of_lt_of_le hz.2 (by omega)⟩

private theorem forest_unique (g : Graph T) (ts : List (Tree T))
    (ht : ∀ t ∈ ts, ∀ {lo hi a}, Layout g lo hi a t → NoAlias g a) :
    ∀ {lo hi as} {i j : Nat} {b c p q z}, ForestLayout g lo hi as ts →
    as[i]? = some b → as[j]? = some c → Path g b p z → Path g c q z →
    i = j ∧ p = q := by
  induction ts with
  | nil =>
    intro lo hi as i j b c p q z hf hb _ _ _
    cases as <;> simp_all [ForestLayout]
  | cons t ts ih =>
    intro lo hi as i j b c p q z hf hb hc hp hq
    cases as with
    | nil => exact False.elim hf
    | cons a as =>
      obtain ⟨m, hl, hf⟩ := hf
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst b
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst c
          exact ⟨rfl, ht t (by simp) hl p q z hp hq⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hc
          have hhead : lo ≤ z ∧ z < m := layout_path_bounds t hl hp
          have htail : m ≤ z ∧ z < hi :=
            forest_path_bounds g ts (fun c _ => layout_path_bounds c) hf hc hq
          exact False.elim (Nat.not_lt_of_ge htail.1 hhead.2)
      | succ i =>
        simp only [List.getElem?_cons_succ] at hb
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst c
          have hhead : lo ≤ z ∧ z < m := layout_path_bounds t hl hq
          have htail : m ≤ z ∧ z < hi :=
            forest_path_bounds g ts (fun c _ => layout_path_bounds c) hf hb hp
          exact False.elim (Nat.not_lt_of_ge htail.1 hhead.2)
        | succ j =>
          simp only [List.getElem?_cons_succ] at hc
          obtain ⟨hij, hpq⟩ := ih (fun c hc => ht c (by simp [hc])) hf hb hc hp hq
          exact ⟨congrArg Nat.succ hij, hpq⟩

private theorem leaf_path_nil {g : Graph T} {a c p z}
    (hc : g.cells a = some c) (hn : c.children = []) (hp : Path g a p z) : p = [] := by
  cases hp with
  | nil => rfl
  | cons hcell hget _ =>
    rw [hc] at hcell
    cases hcell
    rw [hn] at hget
    simp at hget

private theorem layout_noAlias (t : Tree T) :
    ∀ {g lo hi a}, Layout g lo hi a t → NoAlias g a := by
  induction t using Tree.induction with
  | hc v =>
    intro g lo hi a hl p q z hp hq
    obtain ⟨_, _, hc⟩ := hl
    exact (leaf_path_nil hc rfl hp).trans (leaf_path_nil hc rfl hq).symm
  | hf i =>
    intro g lo hi a hl p q z hp hq
    obtain ⟨_, _, hc⟩ := hl
    exact (leaf_path_nil hc rfl hp).trans (leaf_path_nil hc rfl hq).symm
  | hb op cs ih =>
    intro g lo hi a hl p q z hp hq
    obtain ⟨mid, as, hroot, _, hf, hc⟩ := hl
    cases hp with
    | nil =>
      cases hq with
      | nil => rfl
      | cons hcell hget hq =>
        rw [hc] at hcell
        cases hcell
        have hz : lo ≤ a ∧ a < mid :=
          forest_path_bounds g cs (fun c _ => layout_path_bounds c) hf hget hq
        omega
    | @cons a b z i p c hcell hget hp =>
      rw [hc] at hcell
      cases hcell
      cases hq with
      | nil =>
        have hz : lo ≤ a ∧ a < mid :=
          forest_path_bounds g cs (fun c _ => layout_path_bounds c) hf hget hp
        omega
      | @cons _ d _ j q _ hcell hget' hq =>
        rw [hc] at hcell
        cases hcell
        obtain ⟨hij, hpq⟩ := forest_unique g cs (fun c hc => ih c hc) hf hget hget' hp hq
        simp [hij, hpq]

/-- Concatenating active child paths models successive traversal of references
(src/Node.jl:95-98). -/
theorem Path.append {g : Graph T} {a b c p q}
    (hp : Path g a p b) (hq : Path g b q c) : Path g a (p ++ q) c := by
  induction hp with
  | nil => exact hq
  | cons hc hi _ ih => exact Path.cons hc hi (ih hq)

/-- A reachable cycle supplies a second path to the same identity, so unique
paths exclude cycles in Julia child references (src/Node.jl:95-98). -/
theorem NoAlias.acyclic {g : Graph T} {root} (h : NoAlias g root) : Acyclic g root := by
  intro a ⟨p, hp⟩ q hq
  have heq := h p (p ++ q) a hp (hp.append hq)
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  cases q with
  | nil => rfl
  | cons i q => simp only [List.length_cons] at hlen; omega

/-- Freshly constructed trees contain no shared identities, even when equal
pure subtrees occur repeatedly (src/Node.jl:74-90,392-414). -/
theorem noAlias_ofTree (g : Graph T) (t : Tree T) :
    NoAlias (g.ofTree t).2 (g.ofTree t).1 :=
  layout_noAlias t (ofTree_layout t g).1

/-- Fresh child-first construction cannot create a child cycle
(src/Node.jl:86,392-414). -/
theorem acyclic_ofTree (g : Graph T) (t : Tree T) :
    Acyclic (g.ofTree t).2 (g.ofTree t).1 :=
  (noAlias_ofTree g t).acyclic

/-- The copied root has a fresh object identity (src/Node.jl:86). -/
theorem root_ofTree_fresh (g : Graph T) (t : Tree T) :
    g.next ≤ (g.ofTree t).1 :=
  (layout_bounds t (ofTree_layout t g).1).1

/-- Every identity in a freshly copied tree is new, including its descendants
(src/Node.jl:86,392-414). -/
theorem reachable_ofTree_fresh (g : Graph T) (t : Tree T) (a : Addr)
    (ha : Reachable (g.ofTree t).2 (g.ofTree t).1 a) : g.next ≤ a := by
  obtain ⟨p, hp⟩ := ha
  exact (layout_path_bounds t (ofTree_layout t g).1 hp).1

example : (Tree.branch 1 [Tree.const (3 : Nat), Tree.feature 1]).Representable := by
  simp [Tree.Representable]

example (g : Graph Nat) :
    (g.ofTree (.branch 1 [.const 3, .feature 1])).2.unfold 2
      (g.ofTree (.branch 1 [.const 3, .feature 1])).1 =
      some (.branch 1 [.const 3, .feature 1]) := by
  apply unfold_ofTree
  · simp [Tree.Representable]
  · simp [Tree.depth]

example (g : Graph T) (a : Addr) : unfold g 0 a = none := rfl

example : unfold (Heap.empty : Graph Nat) 1 0 = none := rfl

example : unfold ((Heap.empty : Graph Nat).alloc ⟨0, true, none, 0, 0, []⟩).2 1 0 = none := rfl

example : unfold ((Heap.empty : Graph Nat).alloc ⟨1, false, none, 0, 1, []⟩).2 1 0 = none := rfl

example : ¬ NoAlias
    (((Heap.empty : Graph Nat).alloc (constCell 3)).2.alloc (branchCell 1 [0, 0])).2 1 := by
  let g := (((Heap.empty : Graph Nat).alloc (constCell 3)).2.alloc (branchCell 1 [0, 0])).2
  have hc : g.cells 1 = some (branchCell 1 [0, 0]) := rfl
  have hp : Path g 1 [0] 0 := Path.cons hc rfl (Path.nil 0)
  have hq : Path g 1 [1] 0 := Path.cons hc rfl (Path.nil 0)
  intro h
  have heq := h [0] [1] 0 hp hq
  simp at heq

example : ¬ Acyclic ((Heap.empty : Graph Nat).alloc (branchCell 1 [0])).2 0 := by
  let g := ((Heap.empty : Graph Nat).alloc (branchCell 1 [0])).2
  have hc : g.cells 0 = some (branchCell 1 [0]) := rfl
  have hp : Path g 0 [0] 0 := Path.cons hc rfl (Path.nil 0)
  intro h
  have heq := h 0 ⟨[], Path.nil 0⟩ [0] hp
  simp at heq

end Graph
end DynExpr
