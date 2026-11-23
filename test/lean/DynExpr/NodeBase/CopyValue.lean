import DynExpr.NodeBase.TraverseCopy

/-! `copy_value_fresh` and its immutable-value companion (`src/base.jl:496-510`,
`src/ValueInterface.jl:82`). -/

namespace DynExpr.NodeBase
open DynExpr

variable {T : Type}

private theorem cv_mapM_congr {α β : Type} (f h : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = h x) → l.mapM f = l.mapM h := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    simp [List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]

/-- Unfolding only reads cells reachable from the start. -/
private theorem cv_unfold_agree (g g' : SGraph T) :
    ∀ fuel a, (∀ b, Graph.Reachable g.view a b → g'.view.cells b = g.view.cells b) →
      Graph.unfold g'.view fuel a = Graph.unfold g.view fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a _; rfl
  | succ fuel ih =>
    intro a hr
    have ha := hr a ⟨[], .nil a⟩
    simp only [Graph.unfold, ha]
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
      rw [cv_mapM_congr _ _ c.children hch]

private theorem cv_mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y := by
  intro l
  induction l with
  | nil => intro _ _ x hx; simp at hx
  | cons a as ih =>
    intro ys h x hx
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      rw [hfa] at h
      cases hm : as.mapM f with
      | none => simp [hm] at h
      | some bs =>
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨b, hfa⟩
        · exact ih bs hm x hx'

/-- Every object on a path from a successfully unfolded root exists. -/
private theorem cv_reach_exists (g : Graph T) :
    ∀ (fuel a b : Nat) (p : List Nat) (t : Tree T), Graph.unfold g fuel a = some t →
      Graph.Path g a p b → (g.cells b).isSome := by
  intro fuel
  induction fuel with
  | zero => intro a b p t h; simp [Graph.unfold] at h
  | succ fuel ih =>
    intro a b p t h hp
    cases hp with
    | nil =>
      simp only [Graph.unfold] at h
      cases hc : g.cells a with
      | none => simp [hc, bind, Option.bind] at h
      | some c => simp
    | cons hc hi hp' =>
      rename_i b' _ _ c
      simp only [Graph.unfold, hc, bind, Option.bind] at h
      split at h
      · simp at h
      · split at h
        · have := List.mem_of_getElem? hi
          have : c.children = [] := by
            apply List.eq_nil_of_length_eq_zero; omega
          simp_all
        · cases hm : c.children.mapM (Graph.unfold g fuel) with
          | none => simp [hm] at h
          | some ys =>
            obtain ⟨t', ht'⟩ := cv_mapM_mem _ c.children ys hm b' (List.mem_of_getElem? hi)
            exact ih b' b _ t' ht' hp'

/-- Companion of `copy_value_fresh`: when constant values are immutable
scalars (plain values of any type `T`, carried by value as for isbits
numbers), `copy_node` succeeds on every finite well-formed tree, every node of
the copy is newly allocated, the copy equals the source, and mutating any node
of the copy (including replacing its value) leaves the source unchanged. -/
def copy_value_fresh_immutable : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T) (isGraph bs : Bool),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    ∃ r h, copyNodeH g D isGraph bs fuel root = .ok (r, h) ∧
      (∀ b, Graph.Reachable h.view r b → g.next ≤ b) ∧
      Graph.unfold h.view fuel r = some t ∧
      ∀ (a : Addr) (c : SCell T) (h' : SGraph T), Graph.Reachable h.view r a →
        h.write a c = .ok h' → Graph.unfold h'.view fuel root = some t

theorem copy_value_fresh_immutable_holds : copy_value_fresh_immutable := by
  intro T g D fuel root t isGraph bs hu hwf
  obtain ⟨r, h, hc, hpres, hu', hfresh, _⟩ := copy_node_heap_holds T g D fuel root t isGraph bs hu hwf
  refine ⟨r, h, hc, hfresh, hu', ?_⟩
  intro a c h' ha hw
  have hag : a ≥ g.next := hfresh a ha
  have hsrc : ∀ b, Graph.Reachable g.view root b → b < g.next := by
    intro b ⟨p, hp⟩
    have hs := cv_reach_exists g.view fuel root b p t hu hp
    rcases Nat.lt_or_ge b g.next with hlt | hge
    · exact hlt
    · have := g.fresh b hge
      simp [SGraph.view, this] at hs
  have hw' : ∀ b, b ≠ a → h'.cells b = h.cells b := by
    intro b hb
    unfold Heap.write at hw
    split at hw
    · cases hw
    · cases hw
      simp [hb]
  rw [← hu]
  apply cv_unfold_agree g h' fuel root
  intro b hb
  have hlt : (b : Nat) < g.next := hsrc b hb
  have hag' : g.next ≤ (a : Nat) := hag
  have hne : b ≠ a := fun e => by subst e; exact absurd hlt (Nat.not_lt.mpr hag')
  show (h'.cells b).map SCell.toCell = (g.cells b).map SCell.toCell
  rw [hw' b hne, hpres b hlt]

example : Graph.unfold oneLeaf.view 1 0 = some (Tree.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 :=
  ⟨rfl, by simp [Tree.WF]⟩

/-! ## The `isbits` instance -/

/-- `leaf_copy` with `copy_value = identity` (`src/ValueInterface.jl:82`, the
`isbitstype` branch) is `leafCopyH`. -/
theorem leafCopyVH_pure : leafCopyVH (T := T) pure = leafCopyH := by
  funext a c
  cases hc : c.constant <;> cases hv : c.val <;> simp [leafCopyVH, leafCopyH, hc, hv]

/-- `copy_node` with `copy_value = identity` (`src/base.jl:496-510`) is
`copyNodeH`. -/
theorem copyNodeVH_pure : copyNodeVH (T := T) pure = copyNodeH := by
  funext g D isGraph bs fuel root
  simp only [copyNodeVH, copyNodeH, leafCopyVH_pure]

/-! ## Proof of `copy_value_fresh` -/

private theorem cv_read_eq {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    g.read a = .ok c := by simp [Heap.read, h]

private theorem cv_lt_next {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c) :
    (a : Nat) < g.next :=
  Nat.lt_of_not_le (fun hle => by rw [g.fresh a hle] at h; cases h)

private theorem cv_write_ok {g : SGraph T} {a : Addr} {c : SCell T} (h : g.cells a = some c)
    (v : SCell T) : ∃ g', g.write a v = .ok g' ∧ g'.cells a = some v ∧
      (∀ b, b ≠ a → g'.cells b = g.cells b) ∧ g'.next = g.next := by
  unfold Heap.write
  rw [dite_eq_right (by simp [h])]
  exact ⟨_, rfl, by simp, by intro b hb; simp [hb], rfl⟩

private theorem cv_mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

private theorem cv_mapM_cons_inv {α β : Type} {F : α → Option β} {x : α} {xs : List α}
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

private theorem cv_mapM_some {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (ts : List β), l.mapM F = some ts →
      ts.length = l.length ∧ ∀ x ∈ l, ∃ y, F x = some y := by
  intro l
  induction l with
  | nil => intro ts h; simp at h; subst h; simp
  | cons x xs ih =>
    intro ts h
    obtain ⟨y, ys, hy, hys, rfl⟩ := cv_mapM_cons_inv h
    obtain ⟨hl, hm⟩ := ih ys hys
    refine ⟨by simp [hl], ?_⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨y, hy⟩
    · exact hm z hz

private theorem cv_filterMap_full {α : Type} : ∀ (l : List (Option α)),
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

private theorem cv_unfold_succ {G : Graph T} {f a t} (hu : Graph.unfold G (f + 1) a = some t) :
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

private theorem cv_unfold_succS {g : SGraph T} {f a t}
    (hu : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ ((c.constant = true ∧ ∃ v, c.val = some v ∧ t = .const v) ∨
          (c.constant = false ∧ t = .feature c.feature))) ∨
        (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  obtain ⟨c0, hc0, rest⟩ := cv_unfold_succ hu
  cases hc : g.cells a with
  | none => simp [SGraph.view, hc] at hc0
  | some c =>
    have : c0 = c.toCell := by simp [SGraph.view, hc] at hc0; exact hc0.symm
    subst this
    exact ⟨c, rfl, rest⟩

private theorem cv_path_back {h h' : SGraph T} {N : Nat}
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

private theorem cv_reach_back {h h' : SGraph T} {N : Nat}
    (hp : ∀ x, x < N → h'.cells x = h.cells x) {r z : Addr}
    (hr : Graph.Reachable h'.view r z) (hb : ∀ b : Nat, Graph.Reachable h.view r b → b < N) :
    Graph.Reachable h.view r z :=
  let ⟨p, hpath⟩ := hr
  ⟨p, cv_path_back hp hpath hb⟩

private theorem cv_unfold_frame {h h' : SGraph T} {N : Nat}
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
      rw [cv_mapM_congr _ _ c.children hch]

private theorem cv_getChildren {g : SGraph T} {D : Nat} {a : Addr} {c : SCell T}
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
    have hfull := cv_filterMap_full (s.take c.degree) (by
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
      simp [getChild, cv_read_eq hc, hs, h1, bind, Except.bind, hsi, pure, Except.pure,
        List.getElem?_eq_getElem hi']
    unfold getChildren
    rw [cv_mapM_range_ok _ _ c.degree hget]
    congr 1
    apply List.ext_getElem
    · simp [hl]
    · intro i h1 h2
      simp [List.getElem?_eq_getElem h2]

private theorem cv_active_new (D : Nat) (rs : List Addr) (o : Nat) (hl : rs.length ≤ D) :
    SCell.active (⟨rs.length, false, none, 0, o, some (slotsOf D (rs.map some))⟩ : SCell T) =
      rs := by
  have ht : (slotsOf D (rs.map some)).take rs.length = rs.map some := by
    apply List.ext_getElem
    · simp [slotsOf]; omega
    · intro i h1 h2
      have hi : i < rs.length := by simpa using h2
      simp [slotsOf, List.getElem?_eq_getElem hi]
  simp [SCell.active, ht]

private theorem cv_ctor_branch (h : SGraph T) (D o : Nat) (rs : List Addr) (ho : o ≤ 255)
    (hl : rs.length ≤ D) :
    ∃ h', ctor h D true { op := some o, children := some rs } = .ok (h.next, h') ∧
      h'.next = h.next + 1 ∧
      h'.cells h.next = some ⟨rs.length, false, none, 0, o, some (slotsOf D (rs.map some))⟩ ∧
      ∀ x, x ≠ h.next → h'.cells x = h.cells x := by
  let c0 : SCell T := { (blankCell : SCell T) with degree := rs.length, op := o }
  have h1 : (h.alloc c0).2.cells h.next = some c0 := by simp [Heap.alloc]
  obtain ⟨g', hw, hn, hfr, hnx⟩ := cv_write_ok h1 { c0 with slots := some (slotsOf D (rs.map some)) }
  refine ⟨g', ?_, ?_, hn, ?_⟩
  · have hn1 : ¬ rs.length > D := by omega
    have hn2 : ¬ o > 255 := by omega
    have hfst : ∀ c : SCell T, (h.alloc c).1 = h.next := fun _ => rfl
    simp only [c0] at h1 hw
    simp [ctor, hn1, hn2, bind, Except.bind, pure, Except.pure, hfst, setChildren,
      setChildrenRaw, cv_read_eq h1, hw]
  · rw [hnx]; rfl
  · intro x hx
    rw [hfr x hx]
    simp [Heap.alloc, hx]

private theorem cv_branch {h : SGraph T} {D : Nat} {a : Addr} {c : SCell T}
    (hc : h.cells a = some c) (rs : List Addr) (ho : c.op ≤ 255) (hl : rs.length ≤ D) :
    ∃ h2, (branchCopyH D a rs).run h = .ok (h.next, h2) ∧ h2.next = h.next + 1 ∧
      h2.cells h.next = some ⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩ ∧
      ∀ x, x ≠ h.next → h2.cells x = h.cells x := by
  obtain ⟨h2, hct, hnx, hcell, hfr⟩ := cv_ctor_branch h D c.op rs ho hl
  refine ⟨h2, ?_, hnx, hcell, hfr⟩
  show (do let c ← h.read a; ctor h D true { op := some c.op, children := some rs }) = _
  rw [cv_read_eq hc]
  exact hct

private theorem cv_path_leaf {h : SGraph T} {n : Addr} {cl : SCell T} (hc : h.cells n = some cl)
    (hn : cl.active = []) {p z} (hp : Graph.Path h.view n p z) : p = [] ∧ z = n := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hc' hi _ =>
    simp [SGraph.view, hc] at hc'
    subst hc'
    simp [SCell.toCell, hn] at hi

private theorem cv_run_bind {α β : Type} {m : StateT (SGraph T) Jl α}
    {k : α → StateT (SGraph T) Jl β} {h h1 : SGraph T} {x : α}
    (hm : m.run h = .ok (x, h1)) : (m >>= k).run h = (k x).run h1 := by
  rw [StateT.run_bind, hm]
  rfl

private theorem cv_run_lift {α : Type} {e : Jl α} {x : α} (h : SGraph T) (he : e = .ok x) :
    (StateT.lift e : StateT (SGraph T) Jl α).run h = .ok (x, h) := by
  rw [he]
  rfl

private theorem cv_tmr_hit (g : SGraph Addr) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h : SGraph Addr) (r : Addr)
    (hm : (if s then findCache C a else none) = some r) :
    (tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D) (fun r _ => r)
      (f + 1) a C).run h = .ok ((r, C), h) := by
  simp only [tmrH, hm]
  rfl

private theorem cv_tmr_leaf (g : SGraph Addr) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h h1 : SGraph Addr) (c : SCell Addr) (n : Addr)
    (hc : g.cells a = some c) (hm : (if s then findCache C a else none) = none)
    (hd : c.degree = 0) (hrun : (leafCopyVH deepcopyH a c).run h = .ok (n, h1)) :
    (tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D) (fun r _ => r)
      (f + 1) a C).run h = .ok ((n, if s then (a, n) :: C else C), h1) := by
  have hread := cv_run_lift h (cv_read_eq hc)
  simp only [tmrH, hm, bind_assoc, pure_bind, cv_run_bind hread, ite_eq_left hd, cv_run_bind hrun]
  cases s <;> rfl

private theorem cv_tmr_branch (g : SGraph Addr) (D : Nat) (s : Bool) (f : Nat) (a : Addr)
    (C : Cache Addr) (h hF h2 : SGraph Addr) (c : SCell Addr) (rs : List Addr) (C' : Cache Addr)
    (n : Addr) (hc : g.cells a = some c) (hm : (if s then findCache C a else none) = none)
    (hd : c.degree ≠ 0) (hgc : getChildren g D a (nifDeg D c.degree) = .ok c.active)
    (hfold : (c.active.foldlM (fun (acc : List Addr × Cache Addr) x => do
        let (r, c2) ← tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D)
          (fun r _ => r) f x acc.2
        pure (acc.1 ++ [r], c2)) ([], C)).run h = .ok ((rs, C'), hF))
    (hbr : (branchCopyH D a rs).run hF = .ok (n, h2)) :
    (tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D) (fun r _ => r)
      (f + 1) a C).run h = .ok ((n, if s then (a, n) :: C' else C'), h2) := by
  have hread := cv_run_lift h (cv_read_eq hc)
  have hlift := cv_run_lift h hgc
  simp only [tmrH, hm, bind_assoc, pure_bind, cv_run_bind hread, ite_eq_right hd, cv_run_bind hlift,
    cv_run_bind hfold, cv_run_bind hbr]
  cases s <;> rfl

private theorem cv_constVals_go {α : Type} (v : α) :
    ∀ ts : List (Tree α), v ∈ constVals.go ts → ∃ t ∈ ts, v ∈ constVals t := by
  intro ts
  induction ts with
  | nil => intro h; simp [constVals.go] at h
  | cons t ts ih =>
    intro h
    simp only [constVals.go, List.mem_append] at h
    rcases h with h | h
    · exact ⟨t, by simp, h⟩
    · obtain ⟨t', ht', hv⟩ := ih h
      exact ⟨t', by simp [ht'], hv⟩

/-- The copy `r` (made in heap `h`) of the source object `a` is good: every
object reachable from it was allocated by the copy, and whenever the source
unfolds, so does the copy, with every constant value allocated by the copy. -/
private def Good (g h : SGraph Addr) (a r : Addr) : Prop :=
  (∀ b : Nat, Graph.Reachable h.view r b → g.next ≤ b ∧ b < h.next) ∧
  ∀ f t, Graph.unfold g.view f a = some t →
    ∃ tc, Graph.unfold h.view f r = some tc ∧ ∀ v ∈ constVals tc, g.next ≤ v

private theorem cv_good_mono {g h h' : SGraph Addr} {a r : Addr} (hn : h.next ≤ h'.next)
    (hp : ∀ x, x < h.next → h'.cells x = h.cells x) (hg : Good g h a r) : Good g h' a r := by
  obtain ⟨hb, hu⟩ := hg
  have hb' : ∀ b : Nat, Graph.Reachable h.view r b → b < h.next := fun b hr => (hb b hr).2
  refine ⟨fun b hr => ?_, fun f t ht => ?_⟩
  · have := hb b (cv_reach_back hp hr hb')
    omega
  · rw [cv_unfold_frame hp f r hb']
    exact hu f t ht

private theorem cv_good_leaf {g h1 : SGraph Addr} {a n : Addr} {cl : SCell Addr}
    (hcl : h1.cells n = some cl) (hsl : cl.slots = none) (hd : cl.degree = 0)
    (hv : cl.constant = true → ∃ v, cl.val = some v ∧ g.next ≤ v)
    (hn : g.next ≤ n) (hn1 : n < h1.next) : Good g h1 a n := by
  have hact : cl.active = [] := by simp [SCell.active, hsl]
  refine ⟨fun b ⟨p, hp⟩ => ?_, fun f t ht => ?_⟩
  · obtain ⟨_, rfl⟩ := cv_path_leaf hcl hact hp
    exact ⟨hn, hn1⟩
  · cases f with
    | zero => simp [Graph.unfold] at ht
    | succ f =>
      have hv' : h1.view.cells n = some cl.toCell := by simp [SGraph.view, hcl]
      cases hcs : cl.constant
      · refine ⟨.feature cl.feature, ?_, by simp [constVals]⟩
        simp [Graph.unfold, hv', SCell.toCell, hact, hd, hcs]
      · obtain ⟨v, hvv, hle⟩ := hv hcs
        refine ⟨.const v, ?_, by simp [constVals, hle]⟩
        simp [Graph.unfold, hv', SCell.toCell, hact, hd, hcs, hvv]

/-- `leaf_copy` with `copy_value = deepcopy` (`src/base.jl:501-507`) allocates
a fresh leaf (and, for a constant, a fresh value object first). -/
private theorem cv_leaf (g h : SGraph Addr) (hgn : g.next ≤ h.next) (a : Addr) (c : SCell Addr)
    (hval : c.constant = true → c.val.isSome) :
    ∃ n h1, (leafCopyVH deepcopyH a c).run h = .ok (n, h1) ∧ h.next ≤ h1.next ∧
      (∀ x, x < h.next → h1.cells x = h.cells x) ∧ Good g h1 a n := by
  cases hcs : c.constant
  · have hrun : (leafCopyVH deepcopyH a c).run h =
        .ok (h.next, (h.alloc { (blankCell : SCell Addr) with feature := c.feature }).2) := by
      show leafCopyVH deepcopyH a c h = _
      simp [leafCopyVH, hcs] <;> rfl
    refine ⟨h.next, _, hrun, by simp [Heap.alloc],
      fun x hx => by simp [Heap.alloc, show x ≠ h.next by omega], ?_⟩
    exact cv_good_leaf (cl := { (blankCell : SCell Addr) with feature := c.feature })
      (by simp [Heap.alloc]) rfl rfl (by simp [blankCell]) hgn (Nat.lt_succ_self h.next)
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hval hcs)
    have hrun : (leafCopyVH deepcopyH a c).run h =
        .ok (h.next + 1, ((h.alloc (blankCell : SCell Addr)).2.alloc
          { (blankCell : SCell Addr) with constant := true, val := some h.next }).2) := by
      show leafCopyVH deepcopyH a c h = _
      simp only [leafCopyVH, hcs, hv, ↓reduceIte] <;> rfl
    refine ⟨h.next + 1, _, hrun, by simp only [Heap.alloc]; omega,
      fun x hx => by simp [Heap.alloc, show x ≠ h.next + 1 by omega, show x ≠ h.next by omega],
      ?_⟩
    exact cv_good_leaf
      (cl := { (blankCell : SCell Addr) with constant := true, val := some h.next })
      (by simp [Heap.alloc]) rfl rfl (fun _ => ⟨h.next, rfl, hgn⟩) (by omega)
      (Nat.lt_succ_self (h.next + 1))

/-- Pointwise relation between two lists of the same length. -/
private def Pw (P : Addr → Addr → Prop) : List Addr → List Addr → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | x :: xs, r :: rs => P x r ∧ Pw P xs rs

private theorem cv_pw_mono {P Q : Addr → Addr → Prop} (hpq : ∀ x r, P x r → Q x r) :
    ∀ (xs rs : List Addr), Pw P xs rs → Pw Q xs rs := by
  intro xs
  induction xs with
  | nil => intro rs h; cases rs <;> simp_all [Pw]
  | cons x xs ih =>
    intro rs h
    cases rs with
    | nil => simp [Pw] at h
    | cons r rs =>
      simp only [Pw] at h ⊢
      exact ⟨hpq x r h.1, ih rs h.2⟩

private theorem cv_pw_length {P : Addr → Addr → Prop} :
    ∀ (xs rs : List Addr), Pw P xs rs → xs.length = rs.length := by
  intro xs
  induction xs with
  | nil => intro rs h; cases rs <;> simp_all [Pw]
  | cons x xs ih =>
    intro rs h
    cases rs with
    | nil => simp [Pw] at h
    | cons r rs =>
      simp only [Pw] at h
      simp [ih rs h.2]

private theorem cv_pw_right {P : Addr → Addr → Prop} :
    ∀ (xs rs : List Addr), Pw P xs rs → ∀ r ∈ rs, ∃ x, P x r := by
  intro xs
  induction xs with
  | nil => intro rs h; cases rs <;> simp_all [Pw]
  | cons x xs ih =>
    intro rs h
    cases rs with
    | nil => simp [Pw] at h
    | cons r0 rs =>
      simp only [Pw] at h
      intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨x, h.1⟩
      · exact ih rs h.2 r hr

private theorem cv_pw_unfold {g h : SGraph Addr} {f : Nat} :
    ∀ (xs rs : List Addr) (ts : List (Tree Addr)), Pw (Good g h) xs rs →
      xs.mapM (Graph.unfold g.view f) = some ts →
      ∃ tcs, rs.mapM (Graph.unfold h.view f) = some tcs ∧
        ∀ tc ∈ tcs, ∀ v ∈ constVals tc, g.next ≤ v := by
  intro xs
  induction xs with
  | nil =>
    intro rs ts hp _
    cases rs with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons => simp [Pw] at hp
  | cons x xs ih =>
    intro rs ts hp hm
    cases rs with
    | nil => simp [Pw] at hp
    | cons r rs =>
      simp only [Pw] at hp
      obtain ⟨t0, ts', ht0, hts', rfl⟩ := cv_mapM_cons_inv hm
      obtain ⟨tc, htc, hf⟩ := hp.1.2 f t0 ht0
      obtain ⟨tcs, htcs, hfs⟩ := ih rs ts' hp.2 hts'
      refine ⟨tc :: tcs, by simp [List.mapM_cons, htc, htcs], ?_⟩
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hf
      · exact hfs u hu

/-- Every cached copy is good. -/
private def VInv (g h : SGraph Addr) (C : Cache Addr) : Prop :=
  ∀ a r, findCache C a = some r → Good g h a r

private theorem cv_vinv_mono {g h h' : SGraph Addr} {C : Cache Addr} (hn : h.next ≤ h'.next)
    (hp : ∀ x, x < h.next → h'.cells x = h.cells x) (hi : VInv g h C) : VInv g h' C :=
  fun a r hk => cv_good_mono hn hp (hi a r hk)

private theorem cv_vinv_cons {g h : SGraph Addr} {C : Cache Addr} {a n : Addr}
    (hi : VInv g h C) (hgood : Good g h a n) : VInv g h ((a, n) :: C) := by
  intro k r hk
  by_cases hka : k = a
  · subst hka
    simp [findCache] at hk
    subst hk
    exact hgood
  · simp [findCache, Ne.symm hka] at hk
    exact hi k r hk

private def VSpec (g : SGraph Addr) (D : Nat) (s : Bool) (f : Nat) : Prop :=
  ∀ (a : Addr) (t : Tree Addr) (C : Cache Addr) (h : SGraph Addr),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next → VInv g h C →
    Graph.unfold g.view f a = some t → t.WF D (fun _ => 255) 65535 →
    ∃ (r : Addr) (C' : Cache Addr) (h' : SGraph Addr),
      (tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D) (fun r _ => r)
        f a C).run h = .ok ((r, C'), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧
      VInv g h' C' ∧ Good g h' a r

private theorem cv_fold {g : SGraph Addr} {D f : Nat} {s : Bool} (ih : VSpec g D s f) :
    ∀ (xs : List Addr) (ts : List (Tree Addr)) (acc : List Addr) (C : Cache Addr)
      (h : SGraph Addr),
    (∀ x, x < g.next → h.cells x = g.cells x) → g.next ≤ h.next → VInv g h C →
    xs.mapM (Graph.unfold g.view f) = some ts → (∀ t ∈ ts, t.WF D (fun _ => 255) 65535) →
    ∃ (rs : List Addr) (C' : Cache Addr) (h' : SGraph Addr),
      (xs.foldlM (fun (acc : List Addr × Cache Addr) x => do
        let (r, c2) ← tmrH g D s (leafCopyVH deepcopyH) (fun a _ => pure a) (branchCopyH D)
          (fun r _ => r) f x acc.2
        pure (acc.1 ++ [r], c2)) (acc, C)).run h = .ok ((acc ++ rs, C'), h') ∧
      h.next ≤ h'.next ∧ (∀ x, x < h.next → h'.cells x = h.cells x) ∧ VInv g h' C' ∧
      Pw (Good g h') xs rs := by
  intro xs
  induction xs with
  | nil =>
    intro ts acc C h _ _ hinv _ _
    exact ⟨[], C, h, by simp only [List.foldlM_nil, List.append_nil]; rfl, Nat.le_refl _,
      fun _ _ => rfl, hinv, by simp [Pw]⟩
  | cons x xs ihx =>
    intro ts acc C h hg hgn hinv hts hwf
    obtain ⟨t0, ts', ht0, hts', rfl⟩ := cv_mapM_cons_inv hts
    obtain ⟨r0, C1, h1, hrun0, hn1, hp1, hinv1, hgood1⟩ :=
      ih x t0 C h hg hgn hinv ht0 (hwf t0 (by simp))
    have hg1 : ∀ y, y < g.next → h1.cells y = g.cells y := fun y hy => by
      rw [hp1 y (by omega), hg y hy]
    obtain ⟨rs', C', h', hrun', hn', hp', hinv', hpw'⟩ :=
      ihx ts' (acc ++ [r0]) C1 h1 hg1 (by omega) hinv1 hts' (fun t ht => hwf t (by simp [ht]))
    refine ⟨r0 :: rs', C', h', ?_, by omega, ?_, hinv', ?_⟩
    · simp only [List.foldlM_cons, bind_assoc, pure_bind, cv_run_bind hrun0, hrun']
      simp
    · intro y hy; rw [hp' y (by omega), hp1 y hy]
    · simp only [Pw]
      exact ⟨cv_good_mono hn' hp' hgood1, hpw'⟩

private theorem cv_step {g : SGraph Addr} {D f : Nat} {s : Bool} (ih : VSpec g D s f) :
    VSpec g D s (f + 1) := by
  intro a t C h hg hgn hinv hu hwf
  cases hfind : (if s then findCache C a else none) with
  | some r =>
    have hk : findCache C a = some r := by
      cases s
      · simp at hfind
      · simpa using hfind
    exact ⟨r, C, h, cv_tmr_hit g D s f a C h r hfind, Nat.le_refl _, fun _ _ => rfl, hinv,
      hinv a r hk⟩
  | none =>
    obtain ⟨c, hc, hlen, hcase⟩ := cv_unfold_succS hu
    have hca : h.cells a = some c := by rw [hg a (cv_lt_next hc)]; exact hc
    rcases hcase with ⟨hd, hleaf⟩ | ⟨hd, ts, hts, rfl⟩
    · have hval : c.constant = true → c.val.isSome := by
        intro hcs
        rcases hleaf with ⟨_, v, hv, _⟩ | ⟨hcs', _⟩
        · simp [hv]
        · rw [hcs] at hcs'; cases hcs'
      obtain ⟨n, h1, hrun, hn1, hp1, hgood⟩ := cv_leaf g h hgn a c hval
      refine ⟨n, if s then (a, n) :: C else C, h1,
        cv_tmr_leaf g D s f a C h h1 c n hc hfind hd hrun, hn1, hp1, ?_, hgood⟩
      have hinv1 := cv_vinv_mono hn1 hp1 hinv
      cases s
      · exact hinv1
      · exact cv_vinv_cons hinv1 hgood
    · simp only [Tree.WF] at hwf
      obtain ⟨⟨hpos, hD, _⟩, ⟨_, _, h255⟩, hwfc⟩ := hwf
      obtain ⟨htl, _⟩ := cv_mapM_some _ _ _ hts
      have hdeg : c.degree ≤ D := by omega
      have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hdeg]
      have hgc := cv_getChildren hc hlen hdeg
      obtain ⟨rs, C', hF, hfold, hnF, hpF, hinvF, hpw⟩ :=
        cv_fold ih c.active ts [] C h hg hgn hinv hts hwfc
      have hrsl : rs.length = c.degree := by rw [← cv_pw_length _ _ hpw, hlen]
      have hcaF : hF.cells a = some c := by
        rw [hpF a (Nat.lt_of_lt_of_le (cv_lt_next hc) hgn)]; exact hca
      obtain ⟨h2, hbr, hn2, hcell, hfr2⟩ := cv_branch (D := D) hcaF rs h255 (by omega)
      have hact : SCell.active
          (⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩ : SCell Addr) = rs :=
        cv_active_new D rs c.op (by omega)
      have hpres2 : ∀ x, x < hF.next → h2.cells x = hF.cells x := fun x hx => hfr2 x (by omega)
      have hpw2 : Pw (Good g h2) c.active rs :=
        cv_pw_mono (fun _ _ hgd => cv_good_mono (by omega) hpres2 hgd) _ _ hpw
      have hv2 : h2.view.cells hF.next = some (SCell.toCell
          ⟨rs.length, false, none, 0, c.op, some (slotsOf D (rs.map some))⟩) := by
        simp [SGraph.view, hcell]
      have hgood : Good g h2 a hF.next := by
        refine ⟨fun b ⟨p, hp⟩ => ?_, fun f' t' ht' => ?_⟩
        · cases hp with
          | nil => exact ⟨by omega, by omega⟩
          | @cons _ x _ i q c0 hc0 hi hq =>
            rw [hv2] at hc0
            cases hc0
            have hi' : rs[i]? = some x := by simpa [SCell.toCell, hact] using hi
            obtain ⟨y, hy⟩ := cv_pw_right _ _ hpw2 x (List.mem_iff_getElem?.mpr ⟨i, hi'⟩)
            exact hy.1 b ⟨q, hq⟩
        · cases f' with
          | zero => simp [Graph.unfold] at ht'
          | succ f' =>
            obtain ⟨c1, hc1, _, hcase1⟩ := cv_unfold_succS ht'
            rw [hc] at hc1
            cases hc1
            rcases hcase1 with ⟨hd1, _⟩ | ⟨_, ts1, hts1, _⟩
            · exact absurd hd1 hd
            · obtain ⟨tcs, htcs, hfr⟩ := cv_pw_unfold c.active rs ts1 hpw2 hts1
              refine ⟨.branch c.op tcs, ?_, ?_⟩
              · have hne : rs.length ≠ 0 := by omega
                simp only [Graph.unfold, hv2]
                simp [SCell.toCell, hact, hne, htcs]
              · intro v hv
                simp only [constVals] at hv
                obtain ⟨tc, htc, hvt⟩ := cv_constVals_go v tcs hv
                exact hfr tc htc v hvt
      refine ⟨hF.next, if s then (a, hF.next) :: C' else C', h2, ?_, by rw [hn2]; omega, ?_, ?_,
        hgood⟩
      · rw [List.nil_append] at hfold
        rw [← hnif] at hgc
        exact cv_tmr_branch g D s f a C h hF h2 c rs C' hF.next hc hfind hd hgc hfold hbr
      · intro x hx; rw [hfr2 x (by omega), hpF x hx]
      · have hinv2 : VInv g h2 C' := cv_vinv_mono (by omega) hpres2 hinvF
        cases s
        · exact hinv2
        · exact cv_vinv_cons hinv2 hgood

private theorem cv_all (g : SGraph Addr) (D : Nat) (s : Bool) : ∀ f, VSpec g D s f := by
  intro f
  induction f with
  | zero => intro a t _ _ _ _ _ hu _; simp [Graph.unfold] at hu
  | succ f ih => exact cv_step ih

theorem copy_value_fresh_holds : copy_value_fresh := by
  intro g D fuel root t isGraph bs hu hwf hlive
  have hg : ∀ x, x < g.next → g.cells x = g.cells x := fun _ _ => rfl
  have hinv0 : VInv g g ([] : Cache Addr) := fun _ _ h0 => by simp [findCache] at h0
  obtain ⟨r, C', h', hrun, _, _, _, hreach, hunf⟩ :=
    cv_all g D (isGraph && !bs) fuel root t [] g hg (Nat.le_refl _) hinv0 hu hwf
  obtain ⟨tc, htc, hfr⟩ := hunf fuel t hu
  refine ⟨r, h', tc, ?_, fun b hb => (hreach b hb).1, htc, ?_⟩
  · simp only [copyNodeVH, treeMapreduceH]
    rw [cv_run_bind hrun]
    rfl
  · intro v hv hvt
    have h1 : (v : Nat) < g.next := hlive v hvt
    have h2 : g.next ≤ (v : Nat) := hfr v hv
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h2 h1)

/-- A heap holding one constant leaf whose value object is address 0. -/
private def constLeafHeap : SGraph Addr :=
  mkGraph [{ (blankCell : SCell Addr) with constant := true, val := some 0 }]

example : Graph.unfold constLeafHeap.view 1 0 = some (Tree.const 0) ∧
    (Tree.const 0 : Tree Addr).WF 2 (fun _ => 255) 65535 ∧
    ∀ v ∈ constVals (Tree.const (0 : Addr)), v < constLeafHeap.next := by
  refine ⟨rfl, by simp [Tree.WF], ?_⟩
  intro v hv
  simp [constVals] at hv
  subst hv
  exact (by decide : (0 : Nat) < 1)

end DynExpr.NodeBase
