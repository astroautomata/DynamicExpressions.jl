import DynExpr.NodeBase.TraverseCopy
import DynExpr.NodeBase.TraverseCount
import DynExpr.NodeBase.IterateLength

/-! Heap properties of `NodeBase.Traverse` proven with the copy and count
machinery, and their alias-free companions (each adds `Graph.NoAlias`, an
object reachable along at most one child path). -/

namespace DynExpr.NodeBase
open DynExpr

/-- Companion of `iterate_length`: on alias-free trees (no object reachable
along two child paths), iteration yields exactly `length(tree)` elements. -/
def iterate_length_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (isGraph : Bool) (t : Tree T),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    Graph.NoAlias g.view root →
    ∃ l, iterElemsH g D isGraph fuel root = .ok l ∧ lengthH g D isGraph fuel root = .ok l.length

/-- Companion of `graph_eq_sound`: on alias-free operands, `GraphNode` `==`
returns a `Bool` that is `true` exactly when the trees are equal. -/
def graph_eq_noalias : Prop :=
  ∀ (T : Type) (veq : T → T → Bool), (∀ x y, veq x y = true ↔ x = y) →
    ∀ (g : SGraph T) (D fuel a b : Nat) (ta tb : Tree T),
      Graph.unfold g.view fuel a = some ta → Graph.unfold g.view fuel b = some tb →
      ta.WF D (fun _ => 255) 65535 → tb.WF D (fun _ => 255) 65535 →
      Graph.NoAlias g.view a → Graph.NoAlias g.view b →
      ∃ r, graphEqH g D veq fuel a b = .ok r ∧ (r = true ↔ ta = tb)

/-- Companion of `convert_to_node_noalias` (implied by it since PR #242):
converting an alias-free `GraphNode` tree to `Node` succeeds and yields an
alias-free tree. -/
def convert_to_node_noalias_src : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    Graph.NoAlias g.view root →
    ∃ r h, convertH g D false true false fuel root = .ok (r, h) ∧ Graph.NoAlias h.view r

/-! ## Proofs -/

section CompProofs
variable {T : Type}

/-! ### Monad and list lemmas -/

private theorem cm_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem cm_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem cm_o_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl

private theorem cm_o_some {α β : Type} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

private theorem cm_o_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

private theorem cm_mapM_cons {α β : Type} (F : α → Option β) (x : α) (xs : List α) (ys : List β) :
    (x :: xs).mapM F = some ys ↔ ∃ y ys', F x = some y ∧ xs.mapM F = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons]
  cases hx : F x with
  | none => simp [cm_o_none]
  | some y =>
    cases hxs : xs.mapM F with
    | none => simp [cm_o_some, cm_o_none]
    | some ys' =>
      simp only [cm_o_some, cm_o_pure, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨y, ys', rfl, rfl, rfl⟩
      · rintro ⟨y1, ys1, h1, h2, rfl⟩
        subst h1; subst h2; rfl

private theorem cm_mapM_mem {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ∀ x ∈ xs, ∃ y ∈ ys, F x = some y := by
  intro xs
  induction xs with
  | nil => intro ys _ x hx; simp at hx
  | cons a as ih =>
    intro ys h x hx
    obtain ⟨y, ys', hy, hys, rfl⟩ := (cm_mapM_cons F a as ys).mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hfz⟩ := ih ys' hys x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

private theorem cm_mapM_length {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons a as ih =>
    intro ys h
    obtain ⟨y, ys', _, hys, rfl⟩ := (cm_mapM_cons F a as ys).mp h
    simp [ih ys' hys]

private theorem cm_filterMap_full {α : Type} :
    ∀ l : List (Option α), (l.filterMap id).length = l.length → l = (l.filterMap id).map some := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons o l ih =>
    intro h
    cases o with
    | none =>
      have := List.length_filterMap_le id l
      rw [List.filterMap_cons_none rfl] at h
      simp at h
      omega
    | some x =>
      have e : (some x :: l).filterMap id = x :: l.filterMap id := rfl
      rw [e] at h ⊢
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.map_cons]
      exact congrArg _ (ih h)

private theorem cm_mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

/-! ### Heap cells, unfolding and paths -/

private theorem cm_unfold_succ {g : SGraph T} {f : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ (c.constant = true → ∃ v, c.val = some v ∧ t = .const v) ∧
          (c.constant = false → t = .feature c.feature)) ∨
       (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : g.cells a with
  | none =>
    have hv : g.view.cells a = none := by simp [SGraph.view, hc]
    simp only [Graph.unfold, hv, cm_o_none] at h
    cases h
  | some c =>
    have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    refine ⟨c, rfl, ?_⟩
    simp only [Graph.unfold, hv, cm_o_some, SCell.toCell] at h
    by_cases hlen : c.active.length = c.degree
    · refine ⟨hlen, ?_⟩
      by_cases hd : c.degree = 0
      · left
        refine ⟨hd, ?_, ?_⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
          cases hval : c.val with
          | none => simp only [hval, cm_o_none] at h; cases h
          | some v =>
            simp only [hval, cm_o_some, cm_o_pure, Option.some.injEq] at h
            exact ⟨v, rfl, h.symm⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte, cm_o_pure,
            Bool.false_eq_true, Option.some.injEq] at h
          exact h.symm
      · right
        refine ⟨hd, ?_⟩
        simp only [hlen, hd, ne_eq, not_true_eq_false, ↓reduceIte] at h
        cases hm : c.active.mapM (Graph.unfold g.view f) with
        | none => simp only [hm, cm_o_none] at h; cases h
        | some ts =>
          simp only [hm, cm_o_some, cm_o_pure, Option.some.injEq] at h
          exact ⟨ts, rfl, h.symm⟩
    · simp only [hlen, ne_eq, not_false_eq_true, ↓reduceIte] at h
      cases h

private theorem cm_getChildren {g : SGraph T} {D a : Nat} {c : SCell T}
    (hc : g.cells a = some c) (hlen : c.active.length = c.degree) (hD : c.degree ≤ D) :
    getChildren g D a c.degree = .ok c.active := by
  have hget : ∀ i, i < c.degree → getChild g D a (i + 1) = .ok ((c.active[i]?).getD 0) := by
    intro i hi
    cases hs : c.slots with
    | none =>
      have : c.active = [] := by simp [SCell.active, hs]
      rw [this] at hlen
      simp at hlen
      omega
    | some s =>
      have h1 : c.active = (s.take c.degree).filterMap id := by
        simp only [SCell.active, hs, Option.getD_some]
      have h2 : c.active.length ≤ (s.take c.degree).length := by
        rw [h1]; exact List.length_filterMap_le _ _
      have h3 : (s.take c.degree).length ≤ c.degree := by simp; omega
      have hfull : s.take c.degree = c.active.map some := by
        rw [h1]
        apply cm_filterMap_full
        rw [← h1]
        omega
      have hsi : s[i]? = some (some ((c.active[i]?).getD 0)) := by
        have e1 : (s.take c.degree)[i]? = s[i]? := by simp [hi]
        rw [← e1, hfull]
        have hi' : i < c.active.length := by omega
        simp [List.getElem?_map, List.getElem?_eq_getElem hi']
      have h4 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, Heap.read, hc, hs, h4, hsi, cm_ok_bind, cm_pure]
  unfold getChildren
  rw [cm_mapM_range_ok _ _ c.degree hget]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

private theorem cm_view {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c) :
    g.view.cells a = some c.toCell := by simp [SGraph.view, hc]

private theorem cm_reach_cons {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    (y : Addr) :
    Graph.Reachable g.view a y ↔ y = a ∨ ∃ x ∈ c.active, Graph.Reachable g.view x y := by
  have hv := cm_view hc
  constructor
  · rintro ⟨p, hp⟩
    cases hp with
    | nil => exact Or.inl rfl
    | cons hc' hi hp' =>
      rw [hv] at hc'
      cases hc'
      exact Or.inr ⟨_, List.mem_iff_getElem?.mpr ⟨_, hi⟩, _, hp'⟩
  · rintro (rfl | ⟨x, hx, p, hp⟩)
    · exact ⟨[], .nil _⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      exact ⟨i :: p, .cons hv hi hp⟩

private theorem cm_reach_child {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    {x y : Addr} (hx : x ∈ c.active) (hy : Graph.Reachable g.view x y) :
    Graph.Reachable g.view a y :=
  (cm_reach_cons hc y).mpr (Or.inr ⟨x, hx, hy⟩)

/-- Two objects whose reachable sets are disjoint. -/
private abbrev cmDis (g : SGraph T) (u v : Addr) : Prop :=
  ∀ y, Graph.Reachable g.view u y → Graph.Reachable g.view v y → False

private theorem cm_noAlias_child {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    (hna : Graph.NoAlias g.view a) {x : Addr} (hx : x ∈ c.active) : Graph.NoAlias g.view x := by
  intro p q z hp hq
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have h := hna (i :: p) (i :: q) z (.cons (cm_view hc) hi hp) (.cons (cm_view hc) hi hq)
  exact (List.cons.inj h).2

/-- Without aliasing, distinct child slots reach disjoint sets of objects. -/
private theorem cm_disjoint {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    (hna : Graph.NoAlias g.view a) : c.active.Pairwise (cmDis g) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij y hy1 hy2
  obtain ⟨p, hp⟩ := hy1
  obtain ⟨q, hq⟩ := hy2
  have h := hna (i :: p) (j :: q) y (.cons (cm_view hc) (List.getElem?_eq_getElem hi) hp)
    (.cons (cm_view hc) (List.getElem?_eq_getElem hj) hq)
  have := (List.cons.inj h).1
  omega

private theorem cm_degLe {D : Nat} : ∀ t : Tree T, t.WF D (fun _ => 255) 65535 → DegLe D t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; simp [DegLe]
  | hf i => intro _; simp [DegLe]
  | hb op cs ih =>
    intro h
    simp only [Tree.WF] at h
    simp only [DegLe]
    exact ⟨h.1.2.1, fun c hc => ih c hc (h.2.2 c hc)⟩

/-! ### Iteration -/

theorem iterate_length_noalias_holds : iterate_length_noalias :=
  fun T g D fuel root isGraph t hu hwf _ => iterate_length_holds T g D fuel root isGraph t hu hwf

/-! ### Equality on alias-free operands -/

private def cmEqStep (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat)
    (acc : Bool × (Cache Addr × Cache Addr)) (xy : Addr × Addr) :
    Jl (Bool × (Cache Addr × Cache Addr)) :=
  if acc.1 then innerEqH g D veq f xy.1 xy.2 acc.2 else pure acc

private theorem cm_eq_false_fold (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat) :
    ∀ (zs : List (Addr × Addr)) (m : Cache Addr × Cache Addr),
      zs.foldlM (cmEqStep g D veq f) (false, m) = .ok (false, m)
  | [], _ => rfl
  | z :: zs, m => by
    simp only [List.foldlM_cons, cmEqStep, Bool.false_eq_true, ↓reduceIte, cm_pure, cm_ok_bind]
    exact cm_eq_false_fold g D veq f zs m

/-- The induction hypothesis for `innerEqH` at a given fuel. -/
private def cmEqSpec (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat) : Prop :=
  ∀ (a b : Addr) (ta tb : Tree T) (ma mb : Cache Addr),
    Graph.unfold g.view f a = some ta → Graph.unfold g.view f b = some tb →
    DegLe D ta → DegLe D tb → Graph.NoAlias g.view a → Graph.NoAlias g.view b →
    (∀ y, Graph.Reachable g.view a y → y ∉ ma.map Prod.fst) →
    (∀ y, Graph.Reachable g.view b y → y ∉ mb.map Prod.fst) →
    ∃ r ma' mb', innerEqH g D veq f a b (ma, mb) = .ok (r, (ma', mb')) ∧ (r = true ↔ ta = tb) ∧
      (∀ y ∈ ma'.map Prod.fst, y ∈ ma.map Prod.fst ∨ Graph.Reachable g.view a y) ∧
      (∀ y ∈ mb'.map Prod.fst, y ∈ mb.map Prod.fst ∨ Graph.Reachable g.view b y)

private theorem cm_eq_fold {g : SGraph T} {D : Nat} {veq : T → T → Bool} {f : Nat}
    (ih : cmEqSpec g D veq f) :
    ∀ (xs ys : List Addr) (tsx tsy : List (Tree T)) (ma mb : Cache Addr),
      xs.length = ys.length →
      xs.mapM (Graph.unfold g.view f) = some tsx → ys.mapM (Graph.unfold g.view f) = some tsy →
      (∀ t ∈ tsx, DegLe D t) → (∀ t ∈ tsy, DegLe D t) →
      (∀ x ∈ xs, Graph.NoAlias g.view x) → (∀ y ∈ ys, Graph.NoAlias g.view y) →
      xs.Pairwise (cmDis g) → ys.Pairwise (cmDis g) →
      (∀ x ∈ xs, ∀ z, Graph.Reachable g.view x z → z ∉ ma.map Prod.fst) →
      (∀ y ∈ ys, ∀ z, Graph.Reachable g.view y z → z ∉ mb.map Prod.fst) →
      ∃ r ma' mb', (xs.zip ys).foldlM (cmEqStep g D veq f) (true, (ma, mb)) = .ok (r, (ma', mb')) ∧
        (r = true ↔ tsx = tsy) ∧
        (∀ z ∈ ma'.map Prod.fst, z ∈ ma.map Prod.fst ∨ ∃ x ∈ xs, Graph.Reachable g.view x z) ∧
        (∀ z ∈ mb'.map Prod.fst, z ∈ mb.map Prod.fst ∨ ∃ y ∈ ys, Graph.Reachable g.view y z) := by
  intro xs
  induction xs with
  | nil =>
    intro ys tsx tsy ma mb hl hx hy _ _ _ _ _ _ _ _
    cases ys with
    | cons _ _ => simp at hl
    | nil =>
      simp at hx hy
      subst hx
      subst hy
      exact ⟨true, ma, mb, rfl, by simp, fun z hz => Or.inl hz, fun z hz => Or.inl hz⟩
  | cons x xs ihx =>
    intro ys tsx tsy ma mb hl hx hy hdx hdy hnx hny hpx hpy hmx hmy
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      obtain ⟨tx, tsx', htx, htsx, rfl⟩ := (cm_mapM_cons _ x xs tsx).mp hx
      obtain ⟨ty, tsy', hty, htsy, rfl⟩ := (cm_mapM_cons _ y ys tsy).mp hy
      rw [List.pairwise_cons] at hpx hpy
      obtain ⟨r1, ma1, mb1, h1, hr1, hs1a, hs1b⟩ := ih x y tx ty ma mb htx hty
        (hdx tx (by simp)) (hdy ty (by simp)) (hnx x (by simp)) (hny y (by simp))
        (hmx x (by simp)) (hmy y (by simp))
      have hstep : cmEqStep g D veq f (true, (ma, mb)) (x, y) = .ok (r1, (ma1, mb1)) := h1
      simp only [List.zip_cons_cons, List.foldlM_cons, hstep, cm_ok_bind]
      cases r1 with
      | false =>
        have hne : tx ≠ ty := fun h => by cases hr1.mpr h
        refine ⟨false, ma1, mb1, cm_eq_false_fold g D veq f _ _,
          ⟨fun h => (by cases h), fun h => absurd (List.cons.inj h).1 hne⟩, ?_, ?_⟩
        · intro z hz
          rcases hs1a z hz with h | h
          · exact Or.inl h
          · exact Or.inr ⟨x, by simp, h⟩
        · intro z hz
          rcases hs1b z hz with h | h
          · exact Or.inl h
          · exact Or.inr ⟨y, by simp, h⟩
      | true =>
        have htxy : tx = ty := hr1.mp rfl
        obtain ⟨r, ma', mb', h2, hr, hs2a, hs2b⟩ := ihx ys tsx' tsy' ma1 mb1
          (by simpa using hl) htsx htsy (fun t ht => hdx t (by simp [ht]))
          (fun t ht => hdy t (by simp [ht])) (fun x' hx' => hnx x' (by simp [hx']))
          (fun y' hy' => hny y' (by simp [hy'])) hpx.2 hpy.2
          (by
            intro x' hx' z hz hmem
            rcases hs1a z hmem with h | h
            · exact hmx x' (by simp [hx']) z hz h
            · exact hpx.1 x' hx' z h hz)
          (by
            intro y' hy' z hz hmem
            rcases hs1b z hmem with h | h
            · exact hmy y' (by simp [hy']) z hz h
            · exact hpy.1 y' hy' z h hz)
        refine ⟨r, ma', mb', h2, ?_, ?_, ?_⟩
        · rw [hr, htxy]
          exact ⟨fun h => by rw [h], fun h => (List.cons.inj h).2⟩
        · intro z hz
          rcases hs2a z hz with h | ⟨x', hx', h⟩
          · rcases hs1a z h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨x, by simp, h⟩
          · exact Or.inr ⟨x', by simp [hx'], h⟩
        · intro z hz
          rcases hs2b z hz with h | ⟨y', hy', h⟩
          · rcases hs1b z h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨y, by simp, h⟩
          · exact Or.inr ⟨y', by simp [hy'], h⟩

private theorem cm_sub_cons {G : Graph T} {a b y : Addr} {m : Cache Addr}
    (h : y ∈ ((a, b) :: m).map Prod.fst) : y ∈ m.map Prod.fst ∨ Graph.Reachable G a y := by
  simp only [List.map_cons, List.mem_cons] at h
  rcases h with rfl | h
  · exact Or.inr ⟨[], .nil _⟩
  · exact Or.inl h

private theorem cm_find_key {m : Cache Addr} {a : Addr} (h : a ∉ m.map Prod.fst) :
    findCache m a = none := by
  induction m with
  | nil => rfl
  | cons kv m ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [findCache, Ne.symm h.1, ↓reduceIte]
    exact ih h.2

private theorem cm_leaf_ne {c : SCell T} {t : Tree T}
    (hcst : c.constant = true → ∃ v, c.val = some v ∧ t = .const v)
    (hfeat : c.constant = false → t = .feature c.feature) (o : Nat) (ts : List (Tree T)) :
    t ≠ .branch o ts ∧ Tree.branch o ts ≠ t := by
  cases hk : c.constant
  · rw [hfeat hk]; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · obtain ⟨v, _, rfl⟩ := hcst hk; exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

private theorem cm_eq_step {g : SGraph T} {D : Nat} {veq : T → T → Bool} {f : Nat}
    (hveq : ∀ x y, veq x y = true ↔ x = y) (ih : cmEqSpec g D veq f) :
    cmEqSpec g D veq (f + 1) := by
  intro a b ta tb ma mb hua hub hgA hgB hnaa hnab hma hmb
  have ha : findCache ma a = none := cm_find_key (hma a ⟨[], .nil a⟩)
  have hb : findCache mb b = none := cm_find_key (hmb b ⟨[], .nil b⟩)
  obtain ⟨ca, hca, hlena, hcasea⟩ := cm_unfold_succ hua
  obtain ⟨cb, hcb, hlenb, hcaseb⟩ := cm_unfold_succ hub
  rcases hcasea with ⟨hza, hka, hfa⟩ | ⟨hza, tsa, htsa, rfl⟩ <;>
    rcases hcaseb with ⟨hzb, hkb, hfb⟩ | ⟨hzb, tsb, htsb, rfl⟩
  · -- two leaves
    cases hka' : ca.constant <;> cases hkb' : cb.constant
    · have hta := hfa hka'
      have htb := hfb hkb'
      subst hta
      subst htb
      refine ⟨ca.feature == cb.feature, (a, b) :: ma, (b, a) :: mb, ?_, ?_,
        fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
      · simp [innerEqH, ha, hb, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb', cm_ok_bind,
          cm_pure]
      · simp
    · have hta := hfa hka'
      obtain ⟨vb, hvb, htb⟩ := hkb hkb'
      subst hta
      subst htb
      refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h), fun h => (by cases h)⟩,
        fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
      simp [innerEqH, ha, hb, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb', cm_ok_bind,
        cm_pure]
    · obtain ⟨va, hva, hta⟩ := hka hka'
      have htb := hfb hkb'
      subst hta
      subst htb
      refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h), fun h => (by cases h)⟩,
        fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
      simp [innerEqH, ha, hb, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb', cm_ok_bind,
        cm_pure]
    · obtain ⟨va, hva, hta⟩ := hka hka'
      obtain ⟨vb, hvb, htb⟩ := hkb hkb'
      subst hta
      subst htb
      refine ⟨veq va vb, (a, b) :: ma, (b, a) :: mb, ?_, ?_, fun y hy => cm_sub_cons hy,
        fun y hy => cm_sub_cons hy⟩
      · simp [innerEqH, ha, hb, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb', hva, hvb,
          cm_ok_bind, cm_pure]
      · exact ⟨fun h => by rw [(hveq va vb).mp h], fun h => by cases h; exact (hveq _ _).mpr rfl⟩
  · -- leaf against branch
    have hne : ca.degree ≠ cb.degree := by omega
    refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h), fun h => ?_⟩,
      fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
    · simp [innerEqH, ha, hb, Heap.read, hca, hcb, hne, cm_ok_bind, cm_pure]
    · exact absurd h (cm_leaf_ne hka hfa cb.op tsb).1
  · -- branch against leaf
    have hne : ca.degree ≠ cb.degree := by omega
    refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h), fun h => ?_⟩,
      fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
    · simp [innerEqH, ha, hb, Heap.read, hca, hcb, hne, cm_ok_bind, cm_pure]
    · exact absurd h (cm_leaf_ne hkb hfb ca.op tsa).2
  · -- two branches
    have hla := cm_mapM_length _ _ _ htsa
    have hlb := cm_mapM_length _ _ _ htsb
    by_cases heq : ca.degree = cb.degree
    · by_cases hop : ca.op = cb.op
      · simp only [DegLe] at hgA hgB
        have hD : cb.degree ≤ D := by omega
        have hk : nifDeg D cb.degree = cb.degree := by simp [nifDeg, hD]
        have hcsa : getChildren g D a (nifDeg D cb.degree) = .ok ca.active := by
          rw [hk, ← heq]; exact cm_getChildren hca hlena (by omega)
        have hcsb : getChildren g D b (nifDeg D cb.degree) = .ok cb.active := by
          rw [hk]; exact cm_getChildren hcb hlenb hD
        obtain ⟨r, ma', mb', hfold, hr, hsa, hsb⟩ := cm_eq_fold ih ca.active cb.active tsa tsb ma mb
          (by omega) htsa htsb hgA.2 hgB.2 (fun x hx => cm_noAlias_child hca hnaa hx)
          (fun y hy => cm_noAlias_child hcb hnab hy) (cm_disjoint hca hnaa) (cm_disjoint hcb hnab)
          (fun x hx z hz => hma z (cm_reach_child hca hx hz))
          (fun y hy z hz => hmb z (cm_reach_child hcb hy hz))
        refine ⟨r, (a, b) :: ma', (b, a) :: mb', ?_, ?_, ?_, ?_⟩
        · simp only [innerEqH, ha, hb, Heap.read, hca, hcb, cm_ok_bind, heq, ne_eq,
            not_true_eq_false, hzb, hop, hcsa, hcsb, ↓reduceIte]
          erw [hfold]
          rfl
        · rw [hr, hop]
          exact ⟨fun h => by rw [h], fun h => (Tree.branch.inj h).2⟩
        · intro y hy
          rcases cm_sub_cons (G := g.view) hy with h | h
          · rcases hsa y h with h | ⟨x, hx, h⟩
            · exact Or.inl h
            · exact Or.inr (cm_reach_child hca hx h)
          · exact Or.inr h
        · intro y hy
          rcases cm_sub_cons (G := g.view) hy with h | h
          · rcases hsb y h with h | ⟨x, hx, h⟩
            · exact Or.inl h
            · exact Or.inr (cm_reach_child hcb hx h)
          · exact Or.inr h
      · refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h),
          fun h => absurd (Tree.branch.inj h).1 hop⟩,
          fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
        simp [innerEqH, ha, hb, Heap.read, hca, hcb, heq, hzb, hop, cm_ok_bind, cm_pure]
    · refine ⟨false, (a, b) :: ma, (b, a) :: mb, ?_, ⟨fun h => (by cases h), fun h => ?_⟩,
        fun y hy => cm_sub_cons hy, fun y hy => cm_sub_cons hy⟩
      · simp [innerEqH, ha, hb, Heap.read, hca, hcb, heq, cm_ok_bind, cm_pure]
      · have := congrArg List.length (Tree.branch.inj h).2
        omega

private theorem cm_eq_all (g : SGraph T) (D : Nat) (veq : T → T → Bool)
    (hveq : ∀ x y, veq x y = true ↔ x = y) : ∀ f, cmEqSpec g D veq f := by
  intro f
  induction f with
  | zero => intro a b ta tb ma mb hua; simp [Graph.unfold] at hua
  | succ f ih => exact cm_eq_step hveq ih

theorem graph_eq_noalias_holds : graph_eq_noalias := by
  intro T veq hveq g D fuel a b ta tb hua hub hwa hwb hna hnb
  obtain ⟨r, ma', mb', hrun, hr, _, _⟩ := cm_eq_all g D veq hveq fuel a b ta tb [] [] hua hub
    (cm_degLe ta hwa) (cm_degLe tb hwb) hna hnb (by simp) (by simp)
  refine ⟨r, ?_, hr⟩
  unfold graphEqH
  rw [hrun]
  rfl

/-! ### `convert` to `Node` -/

/-- `convert(Node{T,D}, g::GraphNode)` breaks sharing (`src/base.jl:550`), so
the copy is alias-free by `copy_node_heap`. -/
theorem convert_to_node_noalias_holds : convert_to_node_noalias := by
  intro T g D fuel root t hu hwf
  obtain ⟨r, h, hrun, _, _, _, hna, _⟩ := copy_node_heap_holds T g D fuel root t true true hu hwf
  exact ⟨r, h, hrun, hna rfl⟩

theorem convert_to_node_noalias_src_holds : convert_to_node_noalias_src :=
  fun T g D fuel root t hu hwf _ => convert_to_node_noalias_holds T g D fuel root t hu hwf

/-! ### Satisfiable hypotheses -/

private theorem cm_oneLeaf_path {p : List Nat} {a : Addr} (hp : Graph.Path oneLeaf.view 0 p a) :
    p = [] := by
  cases hp with
  | nil => rfl
  | cons hc hi _ =>
    simp [oneLeaf, SGraph.view, Heap.alloc, Heap.empty] at hc
    subst hc
    simp [SCell.toCell, SCell.active, blankCell] at hi

private theorem cm_oneLeaf_noAlias : Graph.NoAlias oneLeaf.view 0 := by
  intro p q a hp hq
  rw [cm_oneLeaf_path hp, cm_oneLeaf_path hq]

example : Graph.unfold oneLeaf.view 1 0 = some (Tree.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 ∧ Graph.NoAlias oneLeaf.view 0 :=
  ⟨rfl, by simp [Tree.WF], cm_oneLeaf_noAlias⟩

example : (∀ x y : Nat, (x == y) = true ↔ x = y) ∧
    Graph.unfold oneLeaf.view 1 0 = some (Tree.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 ∧ Graph.NoAlias oneLeaf.view 0 :=
  ⟨fun x y => by simp, rfl, by simp [Tree.WF], cm_oneLeaf_noAlias⟩

example : Graph.unfold oneLeaf.view 1 0 = some (Tree.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 ∧ Graph.NoAlias oneLeaf.view 0 :=
  ⟨rfl, by simp [Tree.WF], cm_oneLeaf_noAlias⟩

end CompProofs

end DynExpr.NodeBase
