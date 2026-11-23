import DynExpr.NodeBase.Traverse

/-! Properties of `copy_node` on the heap (`src/base.jl:496-510`). -/

namespace DynExpr.NodeBase
open DynExpr

/-- `copy_node(tree; break_sharing)` on a well-formed tree: succeeds, leaves
every existing object unchanged, returns a tree that unfolds to the same
expression and consists only of freshly allocated objects (no node shared
with the source). Without the identity map (plain `Node`, or
`break_sharing = Val(true)`) the copy is alias-free; with it (`GraphNode`
default) the copy has exactly the source's sharing shape: a bijection `φ`
from objects reachable from the source root onto objects reachable from the
copy root maps the root to the root and children lists to children lists. -/
def copy_node_heap : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    ∃ r h, copyNodeH g D isGraph bs fuel root = .ok (r, h) ∧
      (∀ a, a < g.next → h.cells a = g.cells a) ∧
      Graph.unfold h.view fuel r = some t ∧
      (∀ b, Graph.Reachable h.view r b → g.next ≤ b) ∧
      ((isGraph && !bs) = false → Graph.NoAlias h.view r) ∧
      ((isGraph && !bs) = true → ∃ φ : Addr → Addr, φ root = r ∧
        (∀ a b, Graph.Reachable g.view root a → Graph.Reachable g.view root b →
          (φ a = φ b ↔ a = b)) ∧
        (∀ b', Graph.Reachable h.view r b' → ∃ a, Graph.Reachable g.view root a ∧ φ a = b') ∧
        (∀ a, Graph.Reachable g.view root a →
          (h.cells (φ a)).map SCell.active = (g.cells a).map (fun c => c.active.map φ)))

/-! ## Proof of `copy_node_heap` -/

variable {T : Type}

/-! ### Generic list and heap lemmas -/

private theorem cp_read_eq {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    g.read a = .ok c := by simp [Heap.read, h]

private theorem cp_lt_next {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    (a : Nat) < g.next :=
  Nat.lt_of_not_le (fun hle => by rw [g.fresh a hle] at h; cases h)

private theorem cp_write_ok {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c)
    (v : SCell T) : ∃ g', g.write a v = .ok g' ∧ g'.cells a = some v ∧
      (∀ b, b ≠ a → g'.cells b = g.cells b) ∧ g'.next = g.next := by
  unfold Heap.write
  rw [dite_eq_right (by simp [h])]
  exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩

private theorem cp_mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

private theorem cp_mapM_congr {α β : Type} (f h : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = h x) → l.mapM f = l.mapM h := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    simp [List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]

private theorem cp_mapM_map {α β γ : Type} (φ : α → β) (F : β → Option γ) :
    ∀ l : List α, (l.map φ).mapM F = l.mapM (fun x => F (φ x)) := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

private theorem cp_mapM_cons_inv {α β : Type} {F : α → Option β} {x : α} {xs : List α}
    {ts : List β} (h : (x :: xs).mapM F = some ts) :
    ∃ y ys, F x = some y ∧ xs.mapM F = some ys ∧ ts = y :: ys := by
  cases hx : F x with
  | none => simp [List.mapM_cons, hx] at h
  | some y =>
    cases hxs : xs.mapM F with
    | none => simp [List.mapM_cons, hx, hxs] at h
    | some ys =>
      simp [List.mapM_cons, hx, hxs] at h
      exact ⟨y, ys, rfl, rfl, h.symm⟩

private theorem cp_mapM_some {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (ts : List β), l.mapM F = some ts →
      ts.length = l.length ∧ ∀ x ∈ l, ∃ y, F x = some y := by
  intro l
  induction l with
  | nil => intro ts h; simp at h; subst h; simp
  | cons x xs ih =>
    intro ts h
    obtain ⟨y, ys, hy, hys, rfl⟩ := cp_mapM_cons_inv h
    obtain ⟨hl, hm⟩ := ih ys hys
    refine ⟨by simp [hl], ?_⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨y, hy⟩
    · exact hm z hz

private theorem cp_filterMap_full {α : Type} : ∀ (l : List (Option α)),
    (l.filterMap id).length = l.length →
      ∀ i : Nat, (l[i]? : Option (Option α)) = ((l.filterMap id)[i]?).map some := by
  intro l
  induction l with
  | nil => intro _ i; simp
  | cons o xs ih =>
    intro hl i
    cases o with
    | none =>
      have := List.length_filterMap_le id xs
      rw [show List.filterMap id (none :: xs) = List.filterMap id xs from rfl,
        List.length_cons] at hl
      omega
    | some x =>
      have hl' : (xs.filterMap id).length = xs.length := by
        rw [show List.filterMap id (some x :: xs) = x :: List.filterMap id xs from rfl,
          List.length_cons, List.length_cons] at hl
        omega
      cases i with
      | zero => simp
      | succ i => simp [ih hl' i]

/-! ### Unfolding -/

private theorem cp_unfold_succ {G : Graph T} {f a t} (hu : Graph.unfold G (f + 1) a = some t) :
    ∃ c, G.cells a = some c ∧ c.children.length = c.degree ∧
      ((c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
          (c.constant = false ∧ t = .feature c.feature))) ∨
        (c.degree ≠ 0 ∧ ∃ ts, c.children.mapM (Graph.unfold G f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : G.cells a with
  | none => simp [Graph.unfold, hc] at hu
  | some c =>
    refine ⟨c, rfl, ?_⟩
    by_cases hl : c.children.length = c.degree
    case neg => simp [Graph.unfold, hc, hl] at hu
    refine ⟨hl, ?_⟩
    by_cases hd : c.degree = 0
    · left
      refine ⟨hd, ?_⟩
      cases hcs : c.constant
      · right
        refine ⟨rfl, ?_⟩
        simp [Graph.unfold, hc, hl, hd, hcs] at hu
        cases hu; rfl
      · left
        refine ⟨rfl, ?_⟩
        cases hv : c.val with
        | none => simp [Graph.unfold, hc, hl, hd, hcs, hv] at hu
        | some v =>
          simp [Graph.unfold, hc, hl, hd, hcs, hv] at hu
          exact ⟨v, rfl, by cases hu; rfl⟩
    · right
      refine ⟨hd, ?_⟩
      cases hm : c.children.mapM (Graph.unfold G f) with
      | none => simp [Graph.unfold, hc, hl, hd, hm] at hu
      | some ts =>
        simp [Graph.unfold, hc, hl, hd, hm] at hu
        exact ⟨ts, rfl, by cases hu; rfl⟩

private theorem cp_unfold_succS {g : SGraph T} {f a t}
    (hu : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
          (c.constant = false ∧ t = .feature c.feature))) ∨
        (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  obtain ⟨c0, hc0, rest⟩ := cp_unfold_succ hu
  cases hc : g.cells a with
  | none => simp [SGraph.view, hc] at hc0
  | some c =>
    have : c0 = c.toCell := by simp [SGraph.view, hc] at hc0; exact hc0.symm
    subst this
    exact ⟨c, rfl, rest⟩

/-- Unfolding with finite fuel bounds every path length from the root. -/
private theorem cp_path_len {G : Graph T} : ∀ {a p b}, Graph.Path G a p b →
    ∀ fuel t, Graph.unfold G fuel a = some t →
      p.length < fuel ∧ ∃ t', Graph.unfold G (fuel - p.length) b = some t' := by
  intro a p b hp
  induction hp with
  | nil a =>
    intro fuel t hu
    cases fuel with
    | zero => simp [Graph.unfold] at hu
    | succ f => exact ⟨by simp, t, by simpa using hu⟩
  | @cons a b z i p c hc hi _ ih =>
    intro fuel t hu
    cases fuel with
    | zero => simp [Graph.unfold] at hu
    | succ f =>
      obtain ⟨c0, hc0, hl, hcase⟩ := cp_unfold_succ hu
      rw [hc] at hc0
      cases hc0
      rcases hcase with ⟨hd, _⟩ | ⟨_, ts, hts, _⟩
      · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hi
        simp at hi
      · obtain ⟨tb, htb⟩ := (cp_mapM_some _ _ _ hts).2 b (List.mem_iff_getElem?.mpr ⟨i, hi⟩)
        obtain ⟨h1, h2⟩ := ih f tb htb
        refine ⟨by simp; omega, ?_⟩
        have : f + 1 - (i :: p).length = f - p.length := by simp
        rw [this]
        exact h2

/-- A node that unfolds is not reachable from its own children. -/
private theorem cp_no_back {G : Graph T} {f a t} (hu : Graph.unfold G f a = some t)
    {c : Cell T} (hc : G.cells a = some c) {x : Addr} (hx : x ∈ c.children) :
    ¬ Graph.Reachable G x a := by
  rintro ⟨p, hp⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have cyc : Graph.Path G a (i :: p) a := .cons hc hi hp
  have big : ∀ n, ∃ q, Graph.Path G a q a ∧ n ≤ q.length := by
    intro n
    induction n with
    | zero => exact ⟨[], .nil a, by simp⟩
    | succ n ihn =>
      obtain ⟨q, hq, hl⟩ := ihn
      exact ⟨(i :: p) ++ q, cyc.append hq, by simp; omega⟩
  obtain ⟨q, hq, hl⟩ := big f
  have := (cp_path_len hq f t hu).1
  omega

/-! ### Frames: cells below a bound are unchanged -/

private theorem cp_path_back {h h' : SGraph T} {N : Nat}
    (hp : ∀ x, x < N → h'.cells x = h.cells x) :
    ∀ {r p z}, Graph.Path h'.view r p z → (∀ b : Nat, Graph.Reachable h.view r b → b < N) →
      Graph.Path h.view r p z := by
  intro r p z hpath
  induction hpath with
  | nil a => intro _; exact .nil a
  | @cons a b z i p c hc hi _ ih =>
    intro hb
    have ha : a < N := hb a ⟨[], .nil a⟩
    have hc2 : h.view.cells a = some c := by
      have : h'.view.cells a = h.view.cells a := by simp [SGraph.view, hp a ha]
      rw [← this]; exact hc
    exact .cons hc2 hi (ih (fun x ⟨q, hq⟩ => hb x ⟨i :: q, .cons hc2 hi hq⟩))

private theorem cp_reach_back {h h' : SGraph T} {N : Nat}
    (hp : ∀ x, x < N → h'.cells x = h.cells x) {r z : Addr}
    (hr : Graph.Reachable h'.view r z) (hb : ∀ b : Nat, Graph.Reachable h.view r b → b < N) :
    Graph.Reachable h.view r z :=
  let ⟨p, hpath⟩ := hr
  ⟨p, cp_path_back hp hpath hb⟩

private theorem cp_noAlias_frame {h h' : SGraph T} {N : Nat}
    (hp : ∀ x, x < N → h'.cells x = h.cells x) {r : Addr}
    (hna : Graph.NoAlias h.view r) (hb : ∀ b : Nat, Graph.Reachable h.view r b → b < N) :
    Graph.NoAlias h'.view r :=
  fun p q z hp1 hq1 => hna p q z (cp_path_back hp hp1 hb) (cp_path_back hp hq1 hb)

private theorem cp_unfold_frame {h h' : SGraph T} {N : Nat}
    (hp : ∀ x, x < N → h'.cells x = h.cells x) :
    ∀ f r, (∀ b : Nat, Graph.Reachable h.view r b → b < N) →
      Graph.unfold h'.view f r = Graph.unfold h.view f r := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ f ih =>
    intro r hr
    have ha : r < N := hr r ⟨[], .nil r⟩
    have hview : h'.view.cells r = h.view.cells r := by simp [SGraph.view, hp r ha]
    simp only [Graph.unfold, hview]
    cases hc : h.view.cells r with
    | none => rfl
    | some c =>
      have hch : ∀ b ∈ c.children, Graph.unfold h'.view f b = Graph.unfold h.view f b := by
        intro b hb
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
        exact ih b (fun b' ⟨p, hp'⟩ => hr b' ⟨i :: p, .cons hc hi hp'⟩)
      simp only [bind, Option.bind]
      rw [cp_mapM_congr _ _ c.children hch]

/-! ### Copy relation between a source cell and its copy -/

private def CopyRel (φ : Addr → Addr) (c c' : SCell T) : Prop :=
  c'.degree = c.degree ∧ c'.active = c.active.map φ ∧
  (c.degree = 0 → c'.constant = c.constant ∧ (c.constant = true → c'.val = c.val) ∧
    (c.constant = false → c'.feature = c.feature)) ∧
  (c.degree ≠ 0 → c'.op = c.op)

private theorem cp_copyRel_congr {φ ψ : Addr → Addr} {c c' : SCell T} (hr : CopyRel φ c c')
    (he : ∀ b ∈ c.active, φ b = ψ b) : CopyRel ψ c c' := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  exact ⟨h1, by rw [h2]; exact List.map_congr_left he, h3, h4⟩

private theorem cp_unfold_cell {g h : SGraph T} {a a' : Addr} {f : Nat} {c c' : SCell T}
    (φ : Addr → Addr) (hc : g.cells a = some c) (hc' : h.cells a' = some c')
    (hr : CopyRel φ c c')
    (hch : ∀ b ∈ c.active, Graph.unfold h.view f (φ b) = Graph.unfold g.view f b) :
    Graph.unfold h.view (f + 1) a' = Graph.unfold g.view (f + 1) a := by
  obtain ⟨hdeg, hact, hleaf, hop⟩ := hr
  have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
  have hv' : h.view.cells a' = some c'.toCell := by simp [SGraph.view, hc']
  simp only [Graph.unfold, hv, hv', bind, Option.bind, SCell.toCell, hdeg, hact, List.length_map]
  by_cases hd : c.degree = 0
  · obtain ⟨h1, h2, h3⟩ := hleaf hd
    simp only [hd, h1]
    cases hcs : c.constant
    · simp [h3 hcs]
    · simp [h2 hcs]
  · simp only [hd, ite_false, hop hd]
    rw [cp_mapM_map, cp_mapM_congr _ _ c.active hch]

private theorem cp_unfold_copy {g h : SGraph T} (φ : Addr → Addr) (K : Addr → Prop)
    (hK : ∀ a, K a → ∃ c c', g.cells a = some c ∧ h.cells (φ a) = some c' ∧
      CopyRel φ c c' ∧ ∀ b ∈ c.active, K b) :
    ∀ f a, K a → Graph.unfold h.view f (φ a) = Graph.unfold g.view f a := by
  intro f
  induction f with
  | zero => intro _ _; rfl
  | succ f ih =>
    intro a ha
    obtain ⟨c, c', hc, hc', hr, hcl⟩ := hK a ha
    exact cp_unfold_cell φ hc hc' hr (fun b hb => ih b (hcl b hb))

/-! ### Children, leaf copies and branch copies -/

private theorem cp_getChildren {g : SGraph T} {D : Nat} {a : Addr} {c : SCell T}
    (hc : g.cells a = some c) (hl : c.active.length = c.degree) (hD : c.degree ≤ D) :
    getChildren g D a c.degree = .ok c.active := by
  cases hs : c.slots with
  | none =>
    have h0 : c.active = [] := by simp [SCell.active, hs]
    have hd : c.degree = 0 := by rw [← hl, h0]; rfl
    rw [hd, h0]
    rfl
  | some s =>
    have hlt : (s.take c.degree).length = c.degree := by
      have h1 := List.length_filterMap_le id (s.take c.degree)
      have h2 : (s.take c.degree).length ≤ c.degree := by
        rw [List.length_take]; exact Nat.min_le_left _ _
      have h3 : ((s.take c.degree).filterMap id).length = c.degree := by
        simpa [SCell.active, hs] using hl
      omega
    have hfull := cp_filterMap_full (s.take c.degree) (by
      have : ((s.take c.degree).filterMap id).length = c.degree := by
        simpa [SCell.active, hs] using hl
      omega)
    have hact : c.active = (s.take c.degree).filterMap id := by simp [SCell.active, hs]
    have hget : ∀ i, i < c.degree → getChild g D a (i + 1) = .ok ((c.active[i]?).getD 0) := by
      intro i hi
      have hi' : i < c.active.length := by omega
      have hsi : s[i]? = some (some c.active[i]) := by
        have := hfull i
        rw [← hact, List.getElem?_eq_getElem hi'] at this
        have h2 : (List.take c.degree s)[i]? = s[i]? := by simp [hi]
        rw [← h2, this]
        rfl
      have h1 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, cp_read_eq hc, hs, h1, bind, Except.bind, hsi, pure, Except.pure,
        List.getElem?_eq_getElem hi']
    unfold getChildren
    rw [cp_mapM_range_ok _ _ c.degree hget]
    congr 1
    apply List.ext_getElem
    · simp [hl]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]

private theorem cp_leaf {c : SCell T} (h : SGraph T) (a : Addr)
    (hval : c.constant = true → c.val.isSome) :
    ∃ cl : SCell T, (leafCopyH a c).run h = .ok (h.next, (h.alloc cl).2) ∧
      cl.degree = 0 ∧ cl.slots = none ∧ cl.constant = c.constant ∧
      (c.constant = true → cl.val = c.val) ∧ (c.constant = false → cl.feature = c.feature) := by
  cases hcs : c.constant
  · refine ⟨{ (blankCell : SCell T) with feature := c.feature }, ?_, rfl, rfl, rfl,
      by simp, fun _ => rfl⟩
    show leafCopyH a c h = _
    simp [leafCopyH, hcs] <;> rfl
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval hcs)
    refine ⟨{ (blankCell : SCell T) with constant := true, val := some v }, ?_, rfl, rfl, rfl,
      fun _ => hv.symm, by simp⟩
    show leafCopyH a c h = _
    simp [leafCopyH, hcs, hv] <;> rfl

private theorem cp_active_new (D : Nat) (rs : List Addr) (o : Nat) (hl : rs.length ≤ D) :
    SCell.active (⟨rs.length, false, none, 0, o, some (slotsOf D (rs.map some))⟩ : SCell T) =
      rs := by
  have ht : (slotsOf D (rs.map some)).take rs.length = rs.map some := by
    apply List.ext_getElem
    · simp [slotsOf]; omega
    · intro i h1 h2
      have hi : i < rs.length := by simpa using h2
      simp [slotsOf, List.getElem?_eq_getElem hi]
  simp [SCell.active, ht]

private theorem cp_ctor_branch (h : SGraph T) (D o : Nat) (rs : List Addr) (ho : o ≤ 255)
    (hl : rs.length ≤ D) :
    ∃ h', ctor h D true { op := some o, children := some rs } = .ok (h.next, h') ∧
      h'.next = h.next + 1 ∧
      h'.cells h.next = some ⟨rs.length, false, none, 0, o, some (slotsOf D (rs.map some))⟩ ∧
      ∀ x, x ≠ h.next → h'.cells x = h.cells x := by
  let c0 : SCell T := { (blankCell : SCell T) with degree := rs.length, op := o }
  have h1 : (h.alloc c0).2.cells h.next = some c0 := by simp [Heap.alloc]
  obtain ⟨g', hw, hn, hfr, hnx⟩ := cp_write_ok h1 { c0 with slots := some (slotsOf D (rs.map some)) }
  refine ⟨g', ?_, ?_, hn, ?_⟩
  · have hn1 : ¬ rs.length > D := by omega
    have hn2 : ¬ o > 255 := by omega
    have hfst : ∀ c : SCell T, (h.alloc c).1 = h.next := fun _ => rfl
    simp only [c0] at h1 hw
    simp [ctor, hn1, hn2, bind, Except.bind, pure, Except.pure, hfst, setChildren,
      setChildrenRaw, cp_read_eq h1, hw]
  · rw [hnx]; rfl
  · intro x hx
    rw [hfr x hx]
    simp [Heap.alloc, hx]

private theorem cp_branch {h : SGraph T} {D : Nat} {a : Addr} {c : SCell T}
    (hc : h.cells a = some c) (rs : List Addr) (ho : c.op ≤ 255) (hl : rs.length ≤ D) :
    ∃ h2, (branchCopyH D a rs).run h = .ok (h.next, h2) ∧ h2.next = h.next + 1 ∧
      h2.cells h.next = some ⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩ ∧
      ∀ x, x ≠ h.next → h2.cells x = h.cells x := by
  obtain ⟨h2, hct, hnx, hcell, hfr⟩ := cp_ctor_branch h D c.op rs ho hl
  refine ⟨h2, ?_, hnx, hcell, hfr⟩
  show (do let c ← h.read a; ctor h D true { op := some c.op, children := some rs }) = _
  rw [cp_read_eq hc]
  exact hct

private theorem cp_path_leaf {h : SGraph T} {n : Addr} {cl : SCell T} (hc : h.cells n = some cl)
    (hn : cl.active = []) {p z} (hp : Graph.Path h.view n p z) : p = [] ∧ z = n := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hc' hi _ =>
    simp [SGraph.view, hc] at hc'
    subst hc'
    simp [SCell.toCell, hn] at hi

private theorem cp_run_bind {α β : Type} {m : StateT (SGraph T) Jl α}
    {k : α → StateT (SGraph T) Jl β} {h h1 : SGraph T} {x : α}
    (hm : m.run h = .ok (x, h1)) : (m >>= k).run h = (k x).run h1 := by
  rw [StateT.run_bind, hm]
  rfl

private theorem cp_run_lift {α : Type} {e : Jl α} {x : α} (h : SGraph T) (he : e = .ok x) :
    (StateT.lift e : StateT (SGraph T) Jl α).run h = .ok (x, h) := by
  rw [he]
  rfl

private theorem cp_tmr_hit (g : SGraph T) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h : SGraph T) (r : Addr)
    (hm : (if s then findCache C a else none) = some r) :
    (tmrH g D s leafCopyH (fun a _ => pure a) (branchCopyH D) (fun r _ => r) (f + 1) a C).run h =
      .ok ((r, C), h) := by
  simp only [tmrH, hm]
  rfl

private theorem cp_tmr_leaf (g : SGraph T) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h h1 : SGraph T) (c : SCell T) (n : Addr)
    (hc : g.cells a = some c) (hm : (if s then findCache C a else none) = none)
    (hd : c.degree = 0) (hrun : (leafCopyH a c).run h = .ok (n, h1)) :
    (tmrH g D s leafCopyH (fun a _ => pure a) (branchCopyH D) (fun r _ => r) (f + 1) a C).run h =
      .ok ((n, if s then (a, n) :: C else C), h1) := by
  have hread := cp_run_lift h (cp_read_eq hc)
  simp only [tmrH, hm, bind_assoc, pure_bind, cp_run_bind hread, ite_eq_left hd, cp_run_bind hrun]
  cases s <;> rfl

private theorem cp_tmr_branch (g : SGraph T) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h hF h2 : SGraph T) (c : SCell T) (rs : List Addr) (C' : Cache Addr)
    (n : Addr) (hc : g.cells a = some c) (hm : (if s then findCache C a else none) = none)
    (hd : c.degree ≠ 0) (hgc : getChildren g D a (nifDeg D c.degree) = .ok c.active)
    (hfold : (c.active.foldlM (fun (acc : List Addr × Cache Addr) x => do
        let (r, c2) ← tmrH g D s leafCopyH (fun a _ => pure a) (branchCopyH D)
          (fun r _ => r) f x acc.2
        pure (acc.1 ++ [r], c2)) ([], C)).run h = .ok ((rs, C'), hF))
    (hbr : (branchCopyH D a rs).run hF = .ok (n, h2)) :
    (tmrH g D s leafCopyH (fun a _ => pure a) (branchCopyH D) (fun r _ => r) (f + 1) a C).run h =
      .ok ((n, if s then (a, n) :: C' else C'), h2) := by
  have hread := cp_run_lift h (cp_read_eq hc)
  have hlift := cp_run_lift h hgc
  simp only [tmrH, hm, bind_assoc, pure_bind, cp_run_bind hread, ite_eq_right hd, cp_run_bind hlift,
    cp_run_bind hfold, cp_run_bind hbr]
  cases s <;> rfl

private theorem cp_leaf_facts {g h : SGraph T} {a : Addr} {c : SCell T} {f : Nat} {t : Tree T}
    (hc : g.cells a = some c) (hlen : c.active.length = c.degree) (hd : c.degree = 0)
    (hleaf : (c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
      (c.constant = false ∧ t = .feature c.feature))
    (hu : Graph.unfold g.view (f + 1) a = some t) :
    ∃ cl : SCell T, (leafCopyH a c).run h = .ok (h.next, (h.alloc cl).2) ∧
      (h.alloc cl).2.cells h.next = some cl ∧ cl.active = [] ∧
      (h.alloc cl).2.next = h.next + 1 ∧
      (∀ x, x < h.next → (h.alloc cl).2.cells x = h.cells x) ∧
      (∀ φ, CopyRel φ c cl) ∧
      Graph.unfold (SGraph.view (h.alloc cl).2) (f + 1) h.next = some t := by
  have hval : c.constant = true → c.val.isSome := by
    intro hcs
    rcases hleaf with ⟨_, v, hv, _⟩ | ⟨hcs', _⟩
    · simp [hv]
    · rw [hcs] at hcs'; cases hcs'
  obtain ⟨cl, hrun, hd0, hsl, hk, hv, hft⟩ := cp_leaf (c := c) h a hval
  have hcact : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hclact : cl.active = [] := by simp [SCell.active, hsl]
  have hcl : (h.alloc cl).2.cells h.next = some cl := by simp [Heap.alloc]
  have hrel : ∀ φ, CopyRel φ c cl := fun φ =>
    ⟨by rw [hd0, hd], by rw [hclact, hcact]; rfl, fun _ => ⟨hk, hv, hft⟩,
      fun h0 => absurd hd h0⟩
  refine ⟨cl, hrun, hcl, hclact, rfl,
    fun x hx => by simp [Heap.alloc, show x ≠ h.next by omega], hrel, ?_⟩
  rw [cp_unfold_cell id hc hcl (hrel id) (by intro b hb; rw [hcact] at hb; cases hb)]
  exact hu

/-! ### Without the identity map: fresh alias-free copies -/

private def NsSpec (g : SGraph T) (D f : Nat) : Prop :=
  ∀ (a : Addr) (t : Tree T) (cache : Cache Addr) (h : SGraph T),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next →
    Graph.unfold g.view f a = some t → t.WF D (fun _ => 255) 65535 →
    ∃ (r : Addr) (h' : SGraph T), (tmrH g D false leafCopyH (fun a _ => pure a) (branchCopyH D)
        (fun r _ => r)
        f a cache).run h = .ok ((r, cache), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧
      Graph.unfold h'.view f r = some t ∧
      (∀ b : Nat, Graph.Reachable h'.view r b → h.next ≤ b ∧ b < h'.next) ∧
      Graph.NoAlias h'.view r

private theorem cp_ns_fold {g : SGraph T} {D f : Nat} (ih : NsSpec g D f) (cache : Cache Addr) :
    ∀ (xs : List Addr) (ts : List (Tree T)) (acc : List Addr) (h : SGraph T),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next →
    xs.mapM (Graph.unfold g.view f) = some ts → (∀ t ∈ ts, t.WF D (fun _ => 255) 65535) →
    ∃ (rs : List Addr) (h' : SGraph T), (xs.foldlM (fun (acc : List Addr × Cache Addr) x => do
        let (r, c2) ← tmrH g D false leafCopyH (fun a _ => pure a) (branchCopyH D)
          (fun r _ => r) f x acc.2
        pure (acc.1 ++ [r], c2)) (acc, cache)).run h = .ok ((acc ++ rs, cache), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧
      rs.mapM (Graph.unfold h'.view f) = some ts ∧
      (∀ x ∈ rs, ∀ b : Nat, Graph.Reachable h'.view x b → h.next ≤ b ∧ b < h'.next) ∧
      (∀ (i j : Nat) x y b, rs[i]? = some x → rs[j]? = some y → Graph.Reachable h'.view x b →
        Graph.Reachable h'.view y b → i = j) ∧
      (∀ x ∈ rs, Graph.NoAlias h'.view x) := by
  intro xs
  induction xs with
  | nil =>
    intro ts acc h _ _ hts _
    simp at hts
    subst hts
    exact ⟨[], h, by simp only [List.foldlM_nil, List.append_nil]; rfl, Nat.le_refl _,
      fun _ _ => rfl, rfl, by simp, by simp, by simp⟩
  | cons x xs ihx =>
    intro ts acc h hg hgn hts hwf
    obtain ⟨t0, ts', ht0, hts', rfl⟩ := cp_mapM_cons_inv hts
    obtain ⟨r0, h1, hrun0, hn1, hp1, hu1, hb1, hna1⟩ :=
      ih x t0 cache h hg hgn ht0 (hwf t0 (by simp))
    have hg1 : ∀ y, y < g.next → h1.cells y = g.cells y := fun y hy => by
      rw [hp1 y (by omega), hg y hy]
    obtain ⟨rs', h', hrun', hn', hp', hm', hb', hdisj', hna'⟩ :=
      ihx ts' (acc ++ [r0]) h1 hg1 (by omega) hts' (fun t ht => hwf t (by simp [ht]))
    have hb0 : ∀ b : Nat, Graph.Reachable h1.view r0 b → b < h1.next :=
      fun b hb => (hb1 b hb).2
    have hreach0 : ∀ b : Nat, Graph.Reachable h'.view r0 b → h.next ≤ b ∧ b < h1.next :=
      fun b hb => hb1 b (cp_reach_back hp' hb hb0)
    refine ⟨r0 :: rs', h', ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldlM_cons, bind_assoc, pure_bind, cp_run_bind hrun0, hrun']
      simp
    · intro y hy; rw [hp' y (by omega), hp1 y hy]
    · simp [List.mapM_cons, cp_unfold_frame hp' f r0 hb0, hu1, hm']
    · intro y hy b hb
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · have := hreach0 b hb; omega
      · have := hb' y hy b hb; omega
    · intro i j u v b hu hv hbu hbv
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j =>
          simp at hu
          subst hu
          have h1' := hreach0 b hbu
          have h2' := hb' v (List.mem_iff_getElem?.mpr ⟨j, by simpa using hv⟩) b hbv
          omega
      | succ i =>
        cases j with
        | zero =>
          simp at hv
          subst hv
          have h1' := hreach0 b hbv
          have h2' := hb' u (List.mem_iff_getElem?.mpr ⟨i, by simpa using hu⟩) b hbu
          omega
        | succ j =>
          simp only [List.getElem?_cons_succ] at hu hv
          rw [hdisj' i j u v b hu hv hbu hbv]
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact cp_noAlias_frame hp' hna1 hb0
      · exact hna' y hy

private theorem cp_ns_step {g : SGraph T} {D f : Nat} (ih : NsSpec g D f) :
    NsSpec g D (f + 1) := by
  intro a t cache h hg hgn hu hwf
  obtain ⟨c, hc, hlen, hcase⟩ := cp_unfold_succS hu
  have hca : h.cells a = some c := by rw [hg a (cp_lt_next hc)]; exact hc
  rcases hcase with ⟨hd, hleaf⟩ | ⟨hd, ts, hts, rfl⟩
  · obtain ⟨cl, hrun, hcl, hclact, hnx, hpres, _, hunf⟩ :=
      cp_leaf_facts (h := h) hc hlen hd hleaf hu
    refine ⟨h.next, (h.alloc cl).2, ?_, by rw [hnx]; omega, hpres, hunf, ?_, ?_⟩
    · exact cp_tmr_leaf g D false f a cache h _ c h.next hc rfl hd hrun
    · intro b ⟨p, hp⟩
      obtain ⟨_, rfl⟩ := cp_path_leaf hcl hclact hp
      rw [hnx]; omega
    · intro p q z hp hq
      rw [(cp_path_leaf hcl hclact hp).1, (cp_path_leaf hcl hclact hq).1]
  · simp only [Tree.WF] at hwf
    obtain ⟨⟨hpos, hD, _⟩, ⟨_, _, h255⟩, hwfc⟩ := hwf
    obtain ⟨htl, _⟩ := cp_mapM_some _ _ _ hts
    have hdeg : c.degree ≤ D := by omega
    have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hdeg]
    have hgc := cp_getChildren hc hlen hdeg
    obtain ⟨rs, hF, hfold, hnF, hpF, hmapF, hbnd, hdisj, hna⟩ :=
      cp_ns_fold ih cache c.active ts [] h hg hgn hts hwfc
    obtain ⟨hrsl, _⟩ := cp_mapM_some _ _ _ hmapF
    have hcaF : hF.cells a = some c := by
      rw [hpF a (Nat.lt_of_lt_of_le (cp_lt_next hc) hgn)]; exact hca
    obtain ⟨h2, hbr, hn2, hcell, hfr2⟩ := cp_branch (D := D) hcaF rs h255 (by omega)
    have hact : SCell.active
        (⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩ : SCell T) = rs :=
      cp_active_new D rs c.op (by omega)
    have hpres2 : ∀ x, x < hF.next → h2.cells x = hF.cells x := fun x hx => hfr2 x (by omega)
    have hrsF : ∀ x ∈ rs, ∀ b : Nat, Graph.Reachable hF.view x b → b < hF.next :=
      fun x hx b hb => (hbnd x hx b hb).2
    have hv2 : h2.view.cells hF.next = some (SCell.toCell
        ⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩) := by
      simp [SGraph.view, hcell]
    have hpath : ∀ p z, Graph.Path h2.view hF.next p z → (p = [] ∧ z = hF.next) ∨
        ∃ i x q, p = i :: q ∧ rs[i]? = some x ∧ Graph.Path hF.view x q z := by
      intro p z hp
      cases hp with
      | nil => left; exact ⟨rfl, rfl⟩
      | @cons _ x _ i q c0 hc0 hi hq =>
        right
        rw [hv2] at hc0
        cases hc0
        have hi' : rs[i]? = some x := by simpa [SCell.toCell, hact] using hi
        exact ⟨i, x, q, rfl, hi',
          cp_path_back hpres2 hq (hrsF x (List.mem_iff_getElem?.mpr ⟨i, hi'⟩))⟩
    refine ⟨hF.next, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.nil_append] at hfold
      rw [← hnif] at hgc
      exact cp_tmr_branch g D false f a cache h hF h2 c rs cache hF.next hc rfl hd hgc hfold hbr
    · rw [hn2]; omega
    · intro x hx; rw [hfr2 x (by omega), hpF x hx]
    · have hmap2 : rs.mapM (Graph.unfold h2.view f) = some ts := by
        rw [cp_mapM_congr _ (Graph.unfold hF.view f) rs
          (fun x hx => cp_unfold_frame hpres2 f x (hrsF x hx))]
        exact hmapF
      have hne : rs.length ≠ 0 := by omega
      simp only [Graph.unfold, hv2]
      simp [SCell.toCell, hact, hne, hmap2]
    · intro b ⟨p, hp⟩
      rcases hpath p b hp with ⟨_, rfl⟩ | ⟨i, x, q, _, hx, hq⟩
      · rw [hn2]; omega
      · have := hbnd x (List.mem_iff_getElem?.mpr ⟨i, hx⟩) b ⟨q, hq⟩
        rw [hn2]; omega
    · intro p q z hp hq
      rcases hpath p z hp with ⟨rfl, hz⟩ | ⟨i, x, p', rfl, hx, hp'⟩ <;>
        rcases hpath q z hq with ⟨rfl, hz'⟩ | ⟨j, y, q', rfl, hy, hq'⟩
      · rfl
      · rw [hz] at hq'
        exact absurd (hrsF y (List.mem_iff_getElem?.mpr ⟨j, hy⟩) _ ⟨q', hq'⟩) (Nat.lt_irrefl _)
      · rw [hz'] at hp'
        exact absurd (hrsF x (List.mem_iff_getElem?.mpr ⟨i, hx⟩) _ ⟨p', hp'⟩) (Nat.lt_irrefl _)
      · have hij := hdisj i j x y z hx hy ⟨p', hp'⟩ ⟨q', hq'⟩
        subst hij
        rw [hx] at hy
        cases hy
        rw [hna x (List.mem_iff_getElem?.mpr ⟨i, hx⟩) p' q' z hp' hq']

private theorem cp_ns_all (g : SGraph T) (D : Nat) : ∀ f, NsSpec g D f := by
  intro f
  induction f with
  | zero => intro a t _ _ _ _ hu _; simp [Graph.unfold] at hu
  | succ f ih => exact cp_ns_step ih

/-! ### With the identity map: a copy with the same sharing -/

private def CInv (g h : SGraph T) (C : Cache Addr) : Prop :=
  (∀ a r, findCache C a = some r → ∃ c c', g.cells a = some c ∧ h.cells r = some c' ∧
      g.next ≤ r ∧ CopyRel (fun b => (findCache C b).getD 0) c c' ∧
      ∀ b ∈ c.active, (findCache C b).isSome) ∧
  (∀ a b r, findCache C a = some r → findCache C b = some r → a = b)

private theorem cp_find_cons_ne {C : Cache Addr} {a b n : Addr} (h : b ≠ a) :
    findCache ((a, n) :: C) b = findCache C b := by
  simp [findCache, Ne.symm h]

private theorem cp_find_cons_eq {C : Cache Addr} {a n : Addr} :
    findCache ((a, n) :: C) a = some n := by
  simp [findCache]

private theorem cp_cinv_insert {g h h' : SGraph T} {C : Cache Addr} {a n : Addr}
    {c c' : SCell T}
    (hinv : CInv g h C) (hpres : ∀ x, x < h.next → h'.cells x = h.cells x)
    (hnf : findCache C a = none) (hn : h.next ≤ n) (hgn : g.next ≤ n)
    (hc : g.cells a = some c) (hc' : h'.cells n = some c')
    (hrel : CopyRel (fun b => (findCache C b).getD 0) c c')
    (hcl : ∀ b ∈ c.active, (findCache C b).isSome) :
    CInv g h' ((a, n) :: C) := by
  obtain ⟨h1, h2⟩ := hinv
  have hne : ∀ b, (findCache C b).isSome → b ≠ a := by
    intro b hb hba
    rw [hba, hnf] at hb
    cases hb
  have hagree : ∀ b, (findCache C b).isSome →
      (findCache ((a, n) :: C) b).getD 0 = (findCache C b).getD 0 := by
    intro b hb
    rw [cp_find_cons_ne (hne b hb)]
  have hold : ∀ k (r : Nat), findCache C k = some r → r < h.next := by
    intro k r hk
    obtain ⟨_, _, _, hr, _⟩ := h1 k r hk
    exact cp_lt_next hr
  refine ⟨?_, ?_⟩
  · intro k r hk
    by_cases hka : k = a
    · rw [hka, cp_find_cons_eq] at hk
      cases hk
      rw [hka]
      refine ⟨c, c', hc, hc', hgn,
        cp_copyRel_congr hrel (fun b hb => (hagree b (hcl b hb)).symm), ?_⟩
      intro b hb
      rw [cp_find_cons_ne (hne b (hcl b hb))]
      exact hcl b hb
    · rw [cp_find_cons_ne hka] at hk
      obtain ⟨ck, ck', hck, hck', hgr, hrk, hclk⟩ := h1 k r hk
      refine ⟨ck, ck', hck, by rw [hpres r (cp_lt_next hck')]; exact hck', hgr,
        cp_copyRel_congr hrk (fun b hb => (hagree b (hclk b hb)).symm), ?_⟩
      intro b hb
      rw [cp_find_cons_ne (hne b (hclk b hb))]
      exact hclk b hb
  · intro k1 k2 r hk1 hk2
    by_cases h1a : k1 = a <;> by_cases h2a : k2 = a
    · rw [h1a, h2a]
    · rw [h1a, cp_find_cons_eq] at hk1
      have hnr : r = n := (Option.some.inj hk1).symm
      rw [cp_find_cons_ne h2a] at hk2
      have := hold k2 r hk2
      rw [hnr] at this
      exact absurd this (Nat.not_lt.mpr hn)
    · rw [h2a, cp_find_cons_eq] at hk2
      have hnr : r = n := (Option.some.inj hk2).symm
      rw [cp_find_cons_ne h1a] at hk1
      have := hold k1 r hk1
      rw [hnr] at this
      exact absurd this (Nat.not_lt.mpr hn)
    · rw [cp_find_cons_ne h1a] at hk1
      rw [cp_find_cons_ne h2a] at hk2
      exact h2 k1 k2 r hk1 hk2

private def ShSpec (g : SGraph T) (D f : Nat) : Prop :=
  ∀ (a : Addr) (t : Tree T) (C : Cache Addr) (h : SGraph T),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next → CInv g h C →
    Graph.unfold g.view f a = some t → t.WF D (fun _ => 255) 65535 →
    ∃ (r : Addr) (C' : Cache Addr) (h' : SGraph T), (tmrH g D true leafCopyH (fun a _ => pure a)
        (branchCopyH D)
        (fun r _ => r)
        f a C).run h = .ok ((r, C'), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧
      CInv g h' C' ∧ findCache C' a = some r ∧
      (∀ k v, findCache C k = some v → findCache C' k = some v) ∧
      (∀ k, (findCache C' k).isSome → (findCache C k).isSome ∨ Graph.Reachable g.view a k)

private theorem cp_sh_fold {g : SGraph T} {D f : Nat} (ih : ShSpec g D f) :
    ∀ (xs : List Addr) (ts : List (Tree T)) (acc : List Addr) (C : Cache Addr) (h : SGraph T),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next → CInv g h C →
    xs.mapM (Graph.unfold g.view f) = some ts → (∀ t ∈ ts, t.WF D (fun _ => 255) 65535) →
    ∃ (rs : List Addr) (C' : Cache Addr) (h' : SGraph T),
      (xs.foldlM (fun (acc : List Addr × Cache Addr) x => do
        let (r, c2) ← tmrH g D true leafCopyH (fun a _ => pure a) (branchCopyH D)
          (fun r _ => r) f x acc.2
        pure (acc.1 ++ [r], c2)) (acc, C)).run h = .ok ((acc ++ rs, C'), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧ CInv g h' C' ∧
      rs = xs.map (fun x => (findCache C' x).getD 0) ∧ (∀ x ∈ xs, (findCache C' x).isSome) ∧
      (∀ k v, findCache C k = some v → findCache C' k = some v) ∧
      (∀ k, (findCache C' k).isSome →
        (findCache C k).isSome ∨ ∃ x ∈ xs, Graph.Reachable g.view x k) := by
  intro xs
  induction xs with
  | nil =>
    intro ts acc C h _ _ hinv _ _
    exact ⟨[], C, h, by simp only [List.foldlM_nil, List.append_nil]; rfl, Nat.le_refl _,
      fun _ _ => rfl, hinv, rfl, by simp,
      fun _ _ hk => hk, fun k hk => Or.inl hk⟩
  | cons x xs ihx =>
    intro ts acc C h hg hgn hinv hts hwf
    obtain ⟨t0, ts', ht0, hts', rfl⟩ := cp_mapM_cons_inv hts
    obtain ⟨r0, C1, h1, hrun0, hn1, hp1, hinv1, hf1, hmono1, hnew1⟩ :=
      ih x t0 C h hg hgn hinv ht0 (hwf t0 (by simp))
    have hg1 : ∀ y, y < g.next → h1.cells y = g.cells y := fun y hy => by
      rw [hp1 y (by omega), hg y hy]
    obtain ⟨rs', C', h', hrun', hn', hp', hinv', hrs', hsome', hmono', hnew'⟩ :=
      ihx ts' (acc ++ [r0]) C1 h1 hg1 (by omega) hinv1 hts' (fun t ht => hwf t (by simp [ht]))
    have hx' : findCache C' x = some r0 := hmono' x r0 hf1
    refine ⟨r0 :: rs', C', h', ?_, by omega, ?_, hinv', ?_, ?_, ?_, ?_⟩
    · simp only [List.foldlM_cons, bind_assoc, pure_bind, cp_run_bind hrun0, hrun']
      simp
    · intro y hy; rw [hp' y (by omega), hp1 y hy]
    · simp [hx', hrs']
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp [hx']
      · exact hsome' y hy
    · intro k v hk; exact hmono' k v (hmono1 k v hk)
    · intro k hk
      rcases hnew' k hk with hk1 | ⟨y, hy, hr⟩
      · rcases hnew1 k hk1 with hk0 | hr
        · exact Or.inl hk0
        · exact Or.inr ⟨x, by simp, hr⟩
      · exact Or.inr ⟨y, by simp [hy], hr⟩

private theorem cp_sh_step {g : SGraph T} {D f : Nat} (ih : ShSpec g D f) :
    ShSpec g D (f + 1) := by
  intro a t C h hg hgn hinv hu hwf
  cases hfind : findCache C a with
  | some r =>
    refine ⟨r, C, h, ?_, Nat.le_refl _, fun _ _ => rfl, hinv, hfind, fun _ _ hk => hk,
      fun k hk => Or.inl hk⟩
    exact cp_tmr_hit g D true f a C h r (by simp [hfind])
  | none =>
    obtain ⟨c, hc, hlen, hcase⟩ := cp_unfold_succS hu
    have hca : h.cells a = some c := by rw [hg a (cp_lt_next hc)]; exact hc
    have hvc : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    rcases hcase with ⟨hd, hleaf⟩ | ⟨hd, ts, hts, rfl⟩
    · obtain ⟨cl, hrun, hcl, _, hnx, hpres, hrel, _⟩ :=
        cp_leaf_facts (h := h) hc hlen hd hleaf hu
      have hcact : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
      refine ⟨h.next, (a, h.next) :: C, (h.alloc cl).2, ?_, by rw [hnx]; omega, hpres, ?_,
        cp_find_cons_eq, ?_, ?_⟩
      · exact cp_tmr_leaf g D true f a C h _ c h.next hc (by simp [hfind]) hd hrun
      · exact cp_cinv_insert hinv hpres hfind (Nat.le_refl _) hgn hc hcl (hrel _)
          (by simp [hcact])
      · intro k v hk
        have hka : k ≠ a := by intro e; rw [e, hfind] at hk; cases hk
        rw [cp_find_cons_ne hka]; exact hk
      · intro k hk
        by_cases hka : k = a
        · rw [hka]; exact Or.inr ⟨[], .nil _⟩
        · rw [cp_find_cons_ne hka] at hk; exact Or.inl hk
    · simp only [Tree.WF] at hwf
      obtain ⟨⟨hpos, hD, _⟩, ⟨_, _, h255⟩, hwfc⟩ := hwf
      obtain ⟨htl, _⟩ := cp_mapM_some _ _ _ hts
      have hdeg : c.degree ≤ D := by omega
      have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hdeg]
      have hgc := cp_getChildren hc hlen hdeg
      obtain ⟨rs, C', hF, hfold, hnF, hpF, hinvF, hrs, hsome, hmono, hnew⟩ :=
        cp_sh_fold ih c.active ts [] C h hg hgn hinv hts hwfc
      have hnoback : ∀ x ∈ c.active, ¬ Graph.Reachable g.view x a :=
        fun x hx => cp_no_back hu hvc hx
      have hnotin : findCache C' a = none := by
        cases hk : findCache C' a with
        | none => rfl
        | some r =>
          exfalso
          rcases hnew a (by simp [hk]) with h0 | ⟨x, hx, hr⟩
          · rw [hfind] at h0; cases h0
          · exact hnoback x hx hr
      have hcaF : hF.cells a = some c := by
        rw [hpF a (Nat.lt_of_lt_of_le (cp_lt_next hc) hgn)]; exact hca
      have hrsl : rs.length = c.degree := by rw [hrs, List.length_map, hlen]
      obtain ⟨h2, hbr, hn2, hcell, hfr2⟩ := cp_branch (D := D) hcaF rs h255 (by omega)
      have hact : SCell.active
          (⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩ : SCell T) = rs :=
        cp_active_new D rs c.op (by omega)
      have hpres2 : ∀ x, x < hF.next → h2.cells x = hF.cells x :=
        fun x hx => hfr2 x (by omega)
      refine ⟨hF.next, (a, hF.next) :: C', h2, ?_, by rw [hn2]; omega, ?_, ?_,
        cp_find_cons_eq, ?_, ?_⟩
      · rw [List.nil_append] at hfold
        rw [← hnif] at hgc
        exact cp_tmr_branch g D true f a C h hF h2 c rs C' hF.next hc (by simp [hfind]) hd hgc
          hfold hbr
      · intro x hx; rw [hfr2 x (by omega), hpF x hx]
      · exact cp_cinv_insert hinvF hpres2 hnotin (Nat.le_refl _) (by omega) hc hcell
          ⟨hrsl, by rw [hact, hrs], fun h0 => absurd h0 hd, fun _ => rfl⟩ hsome
      · intro k v hk
        have hk' := hmono k v hk
        have hka : k ≠ a := by intro e; rw [e, hnotin] at hk'; cases hk'
        rw [cp_find_cons_ne hka]; exact hk'
      · intro k hk
        by_cases hka : k = a
        · rw [hka]; exact Or.inr ⟨[], .nil _⟩
        · rw [cp_find_cons_ne hka] at hk
          rcases hnew k hk with h0 | ⟨x, hx, ⟨p, hp⟩⟩
          · exact Or.inl h0
          · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
            exact Or.inr ⟨i :: p, .cons hvc hi hp⟩

private theorem cp_sh_all (g : SGraph T) (D : Nat) : ∀ f, ShSpec g D f := by
  intro f
  induction f with
  | zero => intro a t _ _ _ _ _ hu _; simp [Graph.unfold] at hu
  | succ f ih => exact cp_sh_step ih

/-! ### The property -/

theorem copy_node_heap_holds : copy_node_heap := by
  intro T g D fuel root t isGraph bs hu hwf
  have hg : ∀ x, x < g.next → g.cells x = g.cells x := fun _ _ => rfl
  simp only [copyNodeH, treeMapreduceH]
  cases hs : (isGraph && !bs)
  · obtain ⟨r, h', hrun, _, hpres, hunf, hreach, hna⟩ :=
      cp_ns_all g D fuel root t [] g hg (Nat.le_refl _) hu hwf
    refine ⟨r, h', ?_, hpres, hunf, fun b hb => (hreach b hb).1, fun _ => hna,
      fun h0 => by cases h0⟩
    rw [cp_run_bind hrun]
    rfl
  · have hinv0 : CInv g g ([] : Cache Addr) :=
      ⟨fun _ _ h0 => (by simp [findCache] at h0), fun _ _ _ h0 => (by simp [findCache] at h0)⟩
    obtain ⟨r, C', h', hrun, _, hpres, ⟨hI1, hI2⟩, hfind, _, _⟩ :=
      cp_sh_all g D fuel root t [] g hg (Nat.le_refl _) hinv0 hu hwf
    let φ : Addr → Addr := fun a => (findCache C' a).getD 0
    have hK : ∀ a, (findCache C' a).isSome → ∃ c c', g.cells a = some c ∧
        h'.cells (φ a) = some c' ∧ CopyRel φ c c' ∧ ∀ b ∈ c.active, (findCache C' b).isSome := by
      intro a ha
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.mp ha
      obtain ⟨c, c', hc, hc', _, hrel, hcl⟩ := hI1 a r1 hr1
      exact ⟨c, c', hc, by simp [φ, hr1, hc'], hrel, hcl⟩
    have hφr : φ root = r := by simp [φ, hfind]
    have hkey : ∀ a, Graph.Reachable g.view root a → (findCache C' a).isSome := by
      have key : ∀ {x p z}, Graph.Path g.view x p z → (findCache C' x).isSome →
          (findCache C' z).isSome := by
        intro x p z hp
        induction hp with
        | nil => exact id
        | @cons a b z i p c hc hi _ ih =>
          intro ha
          obtain ⟨c1, _, hc1, _, _, hcl⟩ := hK a ha
          have e : c = c1.toCell := by simp [SGraph.view, hc1] at hc; exact hc.symm
          subst e
          exact ih (hcl b (List.mem_iff_getElem?.mpr ⟨i, hi⟩))
      intro a ⟨p, hp⟩
      exact key hp (by simp [hfind])
    have hsurj : ∀ p a b', Graph.Reachable g.view root a → Graph.Path h'.view (φ a) p b' →
        ∃ a2, Graph.Reachable g.view root a2 ∧ φ a2 = b' := by
      intro p
      induction p with
      | nil => intro a b' ha hp; cases hp; exact ⟨a, ha, rfl⟩
      | cons i p ihp =>
        intro a b' ha hp
        cases hp with
        | @cons _ y _ _ _ c0 hc0 hi hq =>
          obtain ⟨c, c', hc, hc', ⟨_, hact, _, _⟩, _⟩ := hK a (hkey a ha)
          have e0 : c0 = c'.toCell := by simp [SGraph.view, hc'] at hc0; exact hc0.symm
          subst e0
          have hi' : (c.active[i]?).map φ = some y := by
            have h0 : (c.active.map φ)[i]? = some y := by rw [← hact]; exact hi
            rw [List.getElem?_map] at h0
            exact h0
          cases hx : c.active[i]? with
          | none => rw [hx] at hi'; cases hi'
          | some x =>
            rw [hx] at hi'
            simp at hi'
            subst hi'
            obtain ⟨q, hq0⟩ := ha
            have hvc : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
            exact ihp x _ ⟨q ++ [i], hq0.append (.cons hvc hx (.nil x))⟩ hq
    refine ⟨r, h', ?_, hpres, ?_, ?_, fun h0 => (by cases h0), fun _ => ⟨φ, hφr, ?_, ?_, ?_⟩⟩
    · rw [cp_run_bind hrun]
      rfl
    · rw [← hφr, cp_unfold_copy φ _ hK fuel root (by simp [hfind])]
      exact hu
    · intro b ⟨p, hp⟩
      rw [← hφr] at hp
      obtain ⟨a2, ha2, rfl⟩ := hsurj p root b ⟨[], .nil root⟩ hp
      obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.mp (hkey a2 ha2)
      obtain ⟨_, _, _, _, hgr, _⟩ := hI1 a2 r2 hr2
      simp only [φ, hr2, Option.getD_some]
      exact hgr
    · intro a b ha hb
      constructor
      · intro he
        obtain ⟨ra, hra⟩ := Option.isSome_iff_exists.mp (hkey a ha)
        obtain ⟨rb, hrb⟩ := Option.isSome_iff_exists.mp (hkey b hb)
        simp only [φ, hra, hrb, Option.getD_some] at he
        subst he
        exact hI2 a b ra hra hrb
      · intro he; rw [he]
    · intro b' ⟨p, hp⟩
      rw [← hφr] at hp
      exact hsurj p root b' ⟨[], .nil root⟩ hp
    · intro a ha
      obtain ⟨c, c', hc, hc', ⟨_, hact, _, _⟩, _⟩ := hK a (hkey a ha)
      simp [hc, hc', hact]

example : Graph.unfold oneLeaf.view 1 0 = some (Tree.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 :=
  ⟨rfl, by simp [Tree.WF]⟩

end DynExpr.NodeBase
