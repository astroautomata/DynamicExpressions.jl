import DynExpr.Model.NodeHeap

/-!
Reusable facts about `Graph.NoAlias` (unique child paths, the Q6 invariant for
plain `Node` trees, `src/Node.jl:343`). Every package operation that builds or
mutates plain `Node` trees only allocates objects (`src/Node.jl:87`) and
rewrites child references or value fields (`src/Node.jl:224-256,490-512`).
The lemmas below therefore characterise alias-freedom locally: a node is
alias-free when its children are alias-free, pairwise disjoint and do not reach
it; unchanged child references transfer paths; replacing the subtree at one
address preserves alias-freedom of every enclosing tree whose remaining nodes
the new subtree does not touch.
-/

namespace DynExpr.NoAlias
open DynExpr Graph

variable {T : Type}

/-- Active child references of an object, if it exists (`src/Node.jl:82,96-99`). -/
def kids (g : Graph T) (a : Addr) : Option (List Addr) := (g.cells a).map Cell.children

/-- No object is reachable from both roots: two trees share no node. -/
def Disjoint (g : Graph T) (a b : Addr) : Prop :=
  ∀ z, Reachable g a z → Reachable g b z → False

/-- Every reachable reference names an existing object (Julia references are
never dangling; `src/Utils.jl:87-93`). -/
def Closed (g : Graph T) (a : Addr) : Prop :=
  ∀ z, Reachable g a z → (g.cells z).isSome

/-- Two heaps agree on the child references of every object reachable from `a`
in the first heap. -/
def SameKidsOn (g g' : Graph T) (a : Addr) : Prop :=
  ∀ x, Reachable g a x → kids g' x = kids g x

/-- Every child reference of the second heap already exists, at the same
position, in the first heap (only edge deletions, e.g. turning a branch into a
leaf, and value writes). -/
def Shrinks (g g' : Graph T) : Prop :=
  ∀ (x : Addr) (c' : Cell T), g'.cells x = some c' → ∀ (i : Nat) (b : Addr),
    c'.children[i]? = some b → ∃ c, g.cells x = some c ∧ c.children[i]? = some b

/-! ## Paths and reachability -/

theorem path_nil_inv {g : Graph T} {a z : Addr} (h : Path g a [] z) : a = z := by
  cases h; rfl

theorem path_cons_inv {g : Graph T} {a z : Addr} {i : Nat} {p : List Nat}
    (h : Path g a (i :: p) z) :
    ∃ c b, g.cells a = some c ∧ c.children[i]? = some b ∧ Path g b p z := by
  cases h with
  | cons hc hi hp => exact ⟨_, _, hc, hi, hp⟩

theorem reach_refl (g : Graph T) (a : Addr) : Reachable g a a := ⟨[], .nil a⟩

theorem reach_trans {g : Graph T} {a b c : Addr} (h1 : Reachable g a b)
    (h2 : Reachable g b c) : Reachable g a c := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  exact ⟨p ++ q, hp.append hq⟩

theorem reach_child {g : Graph T} {a b : Addr} {c : Cell T} {i : Nat}
    (hc : g.cells a = some c) (hi : c.children[i]? = some b) : Reachable g a b :=
  ⟨[i], .cons hc hi (.nil b)⟩

theorem reach_mem {g : Graph T} {a b : Addr} {c : Cell T}
    (hc : g.cells a = some c) (hb : b ∈ c.children) : Reachable g a b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  exact reach_child hc hi

/-- A reachable object other than the root is reachable from one of the
root's children. -/
theorem reach_inv {g : Graph T} {a z : Addr} (h : Reachable g a z) :
    z = a ∨ ∃ c b, g.cells a = some c ∧ b ∈ c.children ∧ Reachable g b z := by
  obtain ⟨p, hp⟩ := h
  cases hp with
  | nil => exact Or.inl rfl
  | cons hc hi hp => exact Or.inr ⟨_, _, hc, List.mem_of_getElem? hi, ⟨_, hp⟩⟩

theorem disjoint_symm {g : Graph T} {a b : Addr} (h : Disjoint g a b) : Disjoint g b a :=
  fun z hb ha => h z ha hb

theorem disjoint_ne {g : Graph T} {a b : Addr} (h : Disjoint g a b) : a ≠ b := by
  intro hab
  subst hab
  exact h a (reach_refl g a) (reach_refl g a)

/-- Disjointness passes to descendants. -/
theorem disjoint_mono {g : Graph T} {a b a' b' : Addr} (h : Disjoint g a b)
    (ha : Reachable g a a') (hb : Reachable g b b') : Disjoint g a' b' :=
  fun z h1 h2 => h z (reach_trans ha h1) (reach_trans hb h2)

/-! ## Transfer of paths along unchanged child references -/

theorem kids_some {g : Graph T} {a : Addr} {c : Cell T} (h : g.cells a = some c) :
    kids g a = some c.children := by simp [kids, h]

theorem cell_of_kids {g : Graph T} {a : Addr} {l : List Addr} (h : kids g a = some l) :
    ∃ c, g.cells a = some c ∧ c.children = l := by
  unfold kids at h
  cases hc : g.cells a with
  | none => simp [hc] at h
  | some c => simp [hc] at h; exact ⟨c, rfl, h⟩

theorem path_transfer {g g' : Graph T} :
    ∀ {a p z}, SameKidsOn g g' a → Path g a p z → Path g' a p z := by
  intro a p z hs hp
  induction hp with
  | nil => exact .nil _
  | @cons a b z i p c hc hi hp ih =>
    have hk : kids g' a = some c.children := by
      rw [hs a (reach_refl g a)]; exact kids_some hc
    obtain ⟨c', hc', hch⟩ := cell_of_kids hk
    refine .cons hc' (by rw [hch]; exact hi) (ih ?_)
    intro x hx
    exact hs x (reach_trans (reach_child hc hi) hx)

theorem path_transfer_back {g g' : Graph T} :
    ∀ {a p z}, SameKidsOn g g' a → Path g' a p z → Path g a p z := by
  intro a p z hs hp
  induction hp with
  | nil => exact .nil _
  | @cons a b z i p c' hc' hi hp ih =>
    have hk : kids g a = some c'.children := by
      rw [← hs a (reach_refl g a)]; exact kids_some hc'
    obtain ⟨c, hc, hch⟩ := cell_of_kids hk
    have hi' : c.children[i]? = some b := by rw [hch]; exact hi
    refine .cons hc hi' (ih ?_)
    intro x hx
    exact hs x (reach_trans (reach_child hc hi') hx)

theorem reach_transfer {g g' : Graph T} {a z : Addr} (hs : SameKidsOn g g' a) :
    Reachable g' a z ↔ Reachable g a z :=
  ⟨fun ⟨p, hp⟩ => ⟨p, path_transfer_back hs hp⟩, fun ⟨p, hp⟩ => ⟨p, path_transfer hs hp⟩⟩

theorem noAlias_transfer {g g' : Graph T} {a : Addr} (hs : SameKidsOn g g' a)
    (h : NoAlias g a) : NoAlias g' a :=
  fun p q z hp hq => h p q z (path_transfer_back hs hp) (path_transfer_back hs hq)

theorem closed_transfer {g g' : Graph T} {a : Addr} (hs : SameKidsOn g g' a)
    (h : Closed g a) : Closed g' a := by
  intro z hz
  have hz' := (reach_transfer hs).mp hz
  have hk := hs z hz'
  cases hc : g.cells z with
  | none => have := h z hz'; simp [hc] at this
  | some c =>
    rw [kids_some hc] at hk
    obtain ⟨c', hc', _⟩ := cell_of_kids hk
    simp [hc']

theorem disjoint_transfer {g g' : Graph T} {a b : Addr} (ha : SameKidsOn g g' a)
    (hb : SameKidsOn g g' b) (h : Disjoint g a b) : Disjoint g' a b :=
  fun z h1 h2 => h z ((reach_transfer ha).mp h1) ((reach_transfer hb).mp h2)

theorem sameKidsOn_mono {g g' : Graph T} {a b : Addr} (h : SameKidsOn g g' a)
    (hab : Reachable g a b) : SameKidsOn g g' b :=
  fun x hx => h x (reach_trans hab hx)

/-- Unchanged child references away from one written address `w` transfer
paths from every root that cannot reach `w`. -/
theorem sameKidsOn_of_frame {g g' : Graph T} {a w : Addr}
    (hoff : ∀ x, x ≠ w → kids g' x = kids g x) (hw : ¬ Reachable g a w) :
    SameKidsOn g g' a := by
  intro x hx
  apply hoff
  intro hxw
  subst hxw
  exact hw hx

/-! ## Local characterisation of alias-freedom -/

private theorem nodup_getElem?_inj {l : List Addr} (hl : l.Nodup) :
    ∀ {i j : Nat} {x : Addr}, l[i]? = some x → l[j]? = some x → i = j := by
  induction l with
  | nil => intro i j x hi; simp at hi
  | cons y ys ih =>
    intro i j x hi hj
    have hy : y ∉ ys := (List.nodup_cons.mp hl).1
    have hys := (List.nodup_cons.mp hl).2
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        simp only [List.getElem?_cons_succ] at hj
        subst hi
        exact absurd (List.mem_of_getElem? hj) hy
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        simp only [List.getElem?_cons_succ] at hi
        subst hj
        exact absurd (List.mem_of_getElem? hi) hy
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact congrArg Nat.succ (ih hys hi hj)

/-- A node is alias-free when its children are distinct, alias-free, pairwise
disjoint and do not reach it (`src/Node.jl:82,96-99`). -/
theorem noAlias_node {g : Graph T} {a : Addr} {c : Cell T} (hc : g.cells a = some c)
    (hnd : c.children.Nodup) (hk : ∀ b ∈ c.children, NoAlias g b)
    (hcyc : ∀ b ∈ c.children, ¬ Reachable g b a)
    (hdis : ∀ b ∈ c.children, ∀ b' ∈ c.children, b ≠ b' → Disjoint g b b') :
    NoAlias g a := by
  intro p q z hp hq
  cases hp with
  | nil =>
    cases hq with
    | nil => rfl
    | cons hc' hi hq =>
      rw [hc] at hc'; cases hc'
      exact absurd ⟨_, hq⟩ (hcyc _ (List.mem_of_getElem? hi))
  | @cons _ b _ i p c1 hc1 hi hp =>
    rw [hc] at hc1; cases hc1
    cases hq with
    | nil => exact absurd ⟨_, hp⟩ (hcyc _ (List.mem_of_getElem? hi))
    | @cons _ b' _ j q c2 hc2 hj hq =>
      rw [hc] at hc2; cases hc2
      by_cases hbb : b = b'
      · subst hbb
        have hij := nodup_getElem?_inj hnd hi hj
        subst hij
        rw [hk b (List.mem_of_getElem? hi) p q z hp hq]
      · exact absurd (hdis b (List.mem_of_getElem? hi) b' (List.mem_of_getElem? hj) hbb z
          ⟨_, hp⟩ ⟨_, hq⟩) id

/-- A node without children is alias-free. -/
theorem noAlias_leaf {g : Graph T} {a : Addr} (h : ∀ c, g.cells a = some c → c.children = []) :
    NoAlias g a := by
  intro p q z hp hq
  have hnil : ∀ {r}, Path g a r z → r = [] := by
    intro r hr
    cases hr with
    | nil => rfl
    | cons hc hi _ => rw [h _ hc] at hi; simp at hi
  rw [hnil hp, hnil hq]

/-- Descendants of an alias-free root are alias-free. -/
theorem noAlias_reach {g : Graph T} {a b : Addr} (h : NoAlias g a) (hab : Reachable g a b) :
    NoAlias g b := by
  obtain ⟨r, hr⟩ := hab
  intro p q z hp hq
  have := h (r ++ p) (r ++ q) z (hr.append hp) (hr.append hq)
  exact List.append_cancel_left this

theorem noAlias_child {g : Graph T} {a b : Addr} {c : Cell T} (h : NoAlias g a)
    (hc : g.cells a = some c) (hb : b ∈ c.children) : NoAlias g b :=
  noAlias_reach h (reach_mem hc hb)

/-- In an alias-free tree, a child does not reach its parent. -/
theorem noAlias_child_not_reach {g : Graph T} {a b : Addr} {c : Cell T} (h : NoAlias g a)
    (hc : g.cells a = some c) (hb : b ∈ c.children) : ¬ Reachable g b a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  intro ⟨p, hp⟩
  have := h [] (i :: p) a (.nil a) (.cons hc hi hp)
  simp at this

/-- In an alias-free tree, a proper descendant does not reach its ancestor. -/
theorem noAlias_not_reach_back {g : Graph T} {a b : Addr} (h : NoAlias g a)
    (hab : Reachable g a b) (hne : b ≠ a) : ¬ Reachable g b a := by
  obtain ⟨p, hp⟩ := hab
  intro ⟨q, hq⟩
  have heq := h [] (p ++ q) a (.nil a) (hp.append hq)
  cases p with
  | nil => exact hne (path_nil_inv hp).symm
  | cons i p => simp at heq

theorem noAlias_kids_disjoint {g : Graph T} {a b b' : Addr} {c : Cell T} {i j : Nat}
    (h : NoAlias g a) (hc : g.cells a = some c) (hi : c.children[i]? = some b)
    (hj : c.children[j]? = some b') (hij : i ≠ j) : Disjoint g b b' := by
  intro z ⟨p, hp⟩ ⟨q, hq⟩
  have := h (i :: p) (j :: q) z (.cons hc hi hp) (.cons hc hj hq)
  simp at this
  exact hij this.1

theorem noAlias_kids_nodup {g : Graph T} {a : Addr} {c : Cell T} (h : NoAlias g a)
    (hc : g.cells a = some c) : c.children.Nodup := by
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  have hi' : c.children[i]? = some c.children[j] := by
    rw [← heq]; simp [List.getElem?_eq_getElem hi]
  have hj' : c.children[j]? = some c.children[j] := by simp [List.getElem?_eq_getElem hj]
  have := h [i] [j] _ (.cons hc hi' (.nil _)) (.cons hc hj' (.nil _))
  simp at this
  omega

theorem noAlias_mem_disjoint {g : Graph T} {a b b' : Addr} {c : Cell T} (h : NoAlias g a)
    (hc : g.cells a = some c) (hb : b ∈ c.children) (hb' : b' ∈ c.children) (hne : b ≠ b') :
    Disjoint g b b' := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb'
  refine noAlias_kids_disjoint h hc hi hj ?_
  intro hij; subst hij; rw [hi] at hj; cases hj; exact hne rfl

/-! ## Grafting a subtree at one address -/

/-- A path in the new heap either avoids `t` (and is a path in the old heap
with no prefix reaching `t`), or first reaches `t` along an old path. -/
theorem path_split {g g' : Graph T} {t : Addr}
    (hoff : ∀ x, x ≠ t → kids g' x = kids g x) :
    ∀ {a p z}, Path g' a p z →
      (Path g a p z ∧ ∀ p1 p2, p = p1 ++ p2 → ¬ Path g a p1 t) ∨
      ∃ p1 p2, p = p1 ++ p2 ∧ Path g a p1 t ∧ Path g' t p2 z := by
  intro a p z hp
  induction hp with
  | nil a =>
    by_cases hat : a = t
    · subst hat; exact Or.inr ⟨[], [], rfl, .nil a, .nil a⟩
    · refine Or.inl ⟨.nil a, fun p1 p2 heq hp1 => ?_⟩
      have : p1 = [] := (List.append_eq_nil_iff.mp heq.symm).1
      subst this
      exact hat (path_nil_inv hp1)
  | @cons a b z i p c hc hi hp ih =>
    by_cases hat : a = t
    · subst hat; exact Or.inr ⟨[], i :: p, rfl, .nil a, .cons hc hi hp⟩
    · have hk : kids g a = some c.children := by rw [← hoff a hat]; exact kids_some hc
      obtain ⟨c0, hc0, hch⟩ := cell_of_kids hk
      have hi0 : c0.children[i]? = some b := by rw [hch]; exact hi
      rcases ih with ⟨hpg, hno⟩ | ⟨p1, p2, heq, hp1, hp2⟩
      · refine Or.inl ⟨.cons hc0 hi0 hpg, fun p1 p2 heq hp1 => ?_⟩
        cases p1 with
        | nil => exact hat (path_nil_inv hp1)
        | cons j p1 =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, heq⟩ := heq
          obtain ⟨c1, b1, hc1, hb1, hp1⟩ := path_cons_inv hp1
          rw [hc0] at hc1; cases hc1
          rw [hi0] at hb1; cases hb1
          exact hno p1 p2 heq hp1
      · exact Or.inr ⟨i :: p1, p2, by simp [heq], .cons hc0 hi0 hp1, hp2⟩

/-- Replacing the subtree at `t` (only `t`'s child references change) keeps an
enclosing tree `r` alias-free when the new subtree is alias-free and meets
the old tree `r` only inside the old subtree at `t`. -/
theorem noAlias_graft {g g' : Graph T} {r t : Addr}
    (hoff : ∀ x, x ≠ t → kids g' x = kids g x)
    (hr : NoAlias g r) (ht : NoAlias g' t)
    (hsub : ∀ x, Reachable g' t x → Reachable g r x → Reachable g t x) :
    NoAlias g' r := by
  intro p q z hp hq
  have cross : ∀ p q, (∃ p1 p2, p = p1 ++ p2 ∧ Path g r p1 t ∧ Path g' t p2 z) →
      (Path g r q z ∧ ∀ p1 p2, q = p1 ++ p2 → ¬ Path g r p1 t) → False := by
    intro p q ⟨p1, p2, _, hp1, hp2⟩ ⟨hqg, hno⟩
    obtain ⟨w, hw⟩ := hsub z ⟨p2, hp2⟩ ⟨q, hqg⟩
    have heq := hr q (p1 ++ w) z hqg (hp1.append hw)
    exact hno p1 w heq hp1
  rcases path_split hoff hp with hl | hR <;> rcases path_split hoff hq with hl' | hR'
  · exact hr p q z hl.1 hl'.1
  · exact (cross q p hR' hl).elim
  · exact (cross p q hR hl').elim
  · obtain ⟨p1, p2, rfl, hp1, hp2⟩ := hR
    obtain ⟨q1, q2, rfl, hq1, hq2⟩ := hR'
    rw [hr p1 q1 t hp1 hq1, ht p2 q2 z hp2 hq2]


/-! ## Edge deletion -/

theorem shrinks_refl (g : Graph T) : Shrinks g g := fun _ c' h _ _ hb => ⟨c', h, hb⟩

theorem shrinks_trans {g h k : Graph T} (h1 : Shrinks g h) (h2 : Shrinks h k) : Shrinks g k := by
  intro x c hc i b hb
  obtain ⟨c1, hc1, hb1⟩ := h2 x c hc i b hb
  exact h1 x c1 hc1 i b hb1

theorem path_shrinks {g g' : Graph T} (hs : Shrinks g g') :
    ∀ {a p z}, Path g' a p z → Path g a p z := by
  intro a p z hp
  induction hp with
  | nil => exact .nil _
  | cons hc hi _ ih =>
    obtain ⟨c0, hc0, hi0⟩ := hs _ _ hc _ _ hi
    exact .cons hc0 hi0 ih

theorem reach_shrinks {g g' : Graph T} (hs : Shrinks g g') {a z : Addr}
    (h : Reachable g' a z) : Reachable g a z :=
  let ⟨p, hp⟩ := h; ⟨p, path_shrinks hs hp⟩

theorem noAlias_shrinks {g g' : Graph T} (hs : Shrinks g g') {a : Addr}
    (h : NoAlias g a) : NoAlias g' a :=
  fun p q z hp hq => h p q z (path_shrinks hs hp) (path_shrinks hs hq)

/-- Writing a cell with the same child references, or with none, only deletes
edges. -/
theorem shrinks_write {g g' : Graph T} {w : Addr} {v : Cell T}
    (hw : g.write w v = .ok g') (hv : (∃ c, g.cells w = some c ∧ c.children = v.children) ∨
      v.children = []) : Shrinks g g' := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw
    intro x c' hc' i b hb
    by_cases hxw : x = w
    · subst hxw
      simp at hc'
      subst hc'
      rcases hv with ⟨c, hc, hch⟩ | hnil
      · exact ⟨c, hc, by rw [hch]; exact hb⟩
      · rw [hnil] at hb; simp at hb
    · simp [hxw] at hc'
      exact ⟨c', hc', hb⟩

/-! ## Heap writes and allocation -/

theorem write_cells {g g' : Graph T} {w : Addr} {v : Cell T} (hw : g.write w v = .ok g') :
    g'.cells w = some v ∧ (∀ x, x ≠ w → g'.cells x = g.cells x) ∧ g'.next = g.next ∧
      (g.cells w).isSome := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · rename_i hne
    cases hw
    refine ⟨by simp, fun x hx => by simp [hx], rfl, ?_⟩
    cases h : g.cells w <;> simp_all

theorem write_kids_off {g g' : Graph T} {w : Addr} {v : Cell T} (hw : g.write w v = .ok g') :
    ∀ x, x ≠ w → kids g' x = kids g x := by
  intro x hx; simp [kids, (write_cells hw).2.1 x hx]

theorem alloc_cells (g : Graph T) (v : Cell T) :
    (g.alloc v).1 = g.next ∧ (g.alloc v).2.cells g.next = some v ∧
      (∀ x, x ≠ g.next → (g.alloc v).2.cells x = g.cells x) ∧ (g.alloc v).2.next = g.next + 1 := by
  refine ⟨rfl, by simp [Heap.alloc], fun x hx => by simp [Heap.alloc, hx], rfl⟩

theorem lt_next_of_isSome {g : Graph T} {a : Addr} (h : (g.cells a).isSome) : a < g.next := by
  apply Nat.lt_of_not_le
  intro hle
  rw [g.fresh a hle] at h
  simp at h

/-- Allocation leaves every closed tree unchanged. -/
theorem sameKidsOn_alloc {g : Graph T} {a : Addr} (v : Cell T) (h : Closed g a) :
    SameKidsOn g (g.alloc v).2 a := by
  intro x hx
  have hne : x ≠ g.next := Nat.ne_of_lt (lt_next_of_isSome (h x hx))
  simp only [kids]
  rw [(alloc_cells g v).2.2.1 x hne]

/-- A closed tree contains only allocated objects. -/
theorem closed_lt {g : Graph T} {a x : Addr} (h : Closed g a) (hx : Reachable g a x) :
    x < g.next := lt_next_of_isSome (h x hx)

end DynExpr.NoAlias
