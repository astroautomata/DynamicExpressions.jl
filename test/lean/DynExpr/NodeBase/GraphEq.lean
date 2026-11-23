import DynExpr.NodeBase.Traverse

/-! Soundness of `==` on `GraphNode` (`src/base.jl:196-245`). Every pair
`(a, b)` recorded in the first identity map of a call that returns `true`
unfolds to equal trees: a fresh comparison records its pair only after
comparing it, and a `false` anywhere makes every enclosing comparison
`false`, because the children loop and the parent are conjunctions. A lookup
hit returns `true` only when `a` is mapped to `b`, so it inherits the
equality of the recorded pair. -/

namespace DynExpr.NodeBase
open DynExpr

section GraphEqProofs
variable {T : Type}

/-! ### Monad and list lemmas -/

private theorem ge_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem ge_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem ge_o_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl

private theorem ge_o_some {α β : Type} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

private theorem ge_o_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

private theorem ge_mapM_cons {α β : Type} (F : α → Option β) (x : α) (xs : List α) (ys : List β) :
    (x :: xs).mapM F = some ys ↔ ∃ y ys', F x = some y ∧ xs.mapM F = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons]
  cases hx : F x with
  | none => simp [ge_o_none]
  | some y =>
    cases hxs : xs.mapM F with
    | none => simp [ge_o_some, ge_o_none]
    | some ys' =>
      simp only [ge_o_some, ge_o_pure, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨y, ys', rfl, rfl, rfl⟩
      · rintro ⟨y1, ys1, h1, h2, rfl⟩
        subst h1; subst h2; rfl

private theorem ge_mapM_length {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons a as ih =>
    intro ys h
    obtain ⟨y, ys', _, hys, rfl⟩ := (ge_mapM_cons F a as ys).mp h
    simp [ih ys' hys]

private theorem ge_mapM_det {α β : Type} {F G : α → Option β}
    (hFG : ∀ x u v, F x = some u → G x = some v → u = v) :
    ∀ (xs : List α) (us vs : List β), xs.mapM F = some us → xs.mapM G = some vs → us = vs
  | [], us, vs, hu, hv => by
    simp at hu hv
    subst hu
    subst hv
    rfl
  | x :: xs, us, vs, hu, hv => by
    obtain ⟨u, us', hu1, hu2, rfl⟩ := (ge_mapM_cons F x xs us).mp hu
    obtain ⟨v, vs', hv1, hv2, rfl⟩ := (ge_mapM_cons G x xs vs).mp hv
    rw [hFG x u v hu1 hv1, ge_mapM_det hFG xs us' vs' hu2 hv2]

private theorem ge_filterMap_full {α : Type} :
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

private theorem ge_mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
    ∀ k, (∀ i, i < k → f i = .ok (h i)) → (List.range k).mapM f = .ok ((List.range k).map h) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hf
    rw [List.range_succ, List.mapM_append, ih (fun i hi => hf i (by omega))]
    simp [List.mapM_cons, hf k (by omega)]
    rfl

/-! ### Heap cells and unfolding -/

private theorem ge_unfold_succ {g : SGraph T} {f : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ (c.constant = true → ∃ v, c.val = some v ∧ t = .const v) ∧
          (c.constant = false → t = .feature c.feature)) ∨
       (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : g.cells a with
  | none =>
    have hv : g.view.cells a = none := by simp [SGraph.view, hc]
    simp only [Graph.unfold, hv, ge_o_none] at h
    cases h
  | some c =>
    have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    refine ⟨c, rfl, ?_⟩
    simp only [Graph.unfold, hv, ge_o_some, SCell.toCell] at h
    by_cases hlen : c.active.length = c.degree
    · refine ⟨hlen, ?_⟩
      by_cases hd : c.degree = 0
      · left
        refine ⟨hd, ?_, ?_⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
          cases hval : c.val with
          | none => simp only [hval, ge_o_none] at h; cases h
          | some v =>
            simp only [hval, ge_o_some, ge_o_pure, Option.some.injEq] at h
            exact ⟨v, rfl, h.symm⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte, ge_o_pure,
            Bool.false_eq_true, Option.some.injEq] at h
          exact h.symm
      · right
        refine ⟨hd, ?_⟩
        simp only [hlen, hd, ne_eq, not_true_eq_false, ↓reduceIte] at h
        cases hm : c.active.mapM (Graph.unfold g.view f) with
        | none => simp only [hm, ge_o_none] at h; cases h
        | some ts =>
          simp only [hm, ge_o_some, ge_o_pure, Option.some.injEq] at h
          exact ⟨ts, rfl, h.symm⟩
    · simp only [hlen, ne_eq, not_false_eq_true, ↓reduceIte] at h
      cases h

/-- An object unfolds to the same tree at every fuel that suffices. -/
private theorem ge_unfold_det {g : SGraph T} :
    ∀ (n m : Nat) (a : Addr) (u v : Tree T),
      Graph.unfold g.view n a = some u → Graph.unfold g.view m a = some v → u = v
  | 0, _, _, _, _, h, _ => by simp [Graph.unfold] at h
  | _ + 1, 0, _, _, _, _, h => by simp [Graph.unfold] at h
  | n + 1, m + 1, a, u, v, hu, hv => by
    obtain ⟨c, hc, _, hu'⟩ := ge_unfold_succ hu
    obtain ⟨c', hc', _, hv'⟩ := ge_unfold_succ hv
    rw [hc] at hc'
    cases hc'
    rcases hu' with ⟨hd, hk, hf⟩ | ⟨hd, us, hus, rfl⟩ <;>
      rcases hv' with ⟨hd', hk', hf'⟩ | ⟨hd', vs, hvs, rfl⟩
    · cases hkc : c.constant
      · rw [hf hkc, hf' hkc]
      · obtain ⟨w, hw, rfl⟩ := hk hkc
        obtain ⟨w', hw', rfl⟩ := hk' hkc
        rw [hw] at hw'
        cases hw'
        rfl
    · exact absurd hd hd'
    · exact absurd hd' hd
    · rw [ge_mapM_det (fun x u v hu hv => ge_unfold_det n m x u v hu hv) c.active us vs hus hvs]

private theorem ge_getChildren {g : SGraph T} {D a : Nat} {c : SCell T}
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
        apply ge_filterMap_full
        rw [← h1]
        omega
      have hsi : s[i]? = some (some ((c.active[i]?).getD 0)) := by
        have e1 : (s.take c.degree)[i]? = s[i]? := by simp [hi]
        rw [← e1, hfull]
        have hi' : i < c.active.length := by omega
        simp [List.getElem?_map, List.getElem?_eq_getElem hi']
      have h4 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, Heap.read, hc, hs, h4, hsi, ge_ok_bind, ge_pure]
  unfold getChildren
  rw [ge_mapM_range_ok _ _ c.degree hget]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

private theorem ge_degLe {D : Nat} : ∀ t : Tree T, t.WF D (fun _ => 255) 65535 → DegLe D t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; simp [DegLe]
  | hf i => intro _; simp [DegLe]
  | hb op cs ih =>
    intro h
    simp only [Tree.WF] at h
    simp only [DegLe]
    exact ⟨h.1.2.1, fun c hc => ih c hc (h.2.2 c hc)⟩

/-! ### The identity-map invariant -/

/-- Two objects that unfold to the same tree. -/
private def geEqv (g : SGraph T) (k v : Addr) : Prop :=
  ∃ f t, Graph.unfold g.view f k = some t ∧ Graph.unfold g.view f v = some t

/-- Every pair recorded in the first identity map unfolds to equal trees. -/
private def geInv (g : SGraph T) (m : Cache Addr) : Prop := ∀ k v, (k, v) ∈ m → geEqv g k v

private theorem ge_find_mem : ∀ (m : Cache Addr) (a b : Addr), findCache m a = some b → (a, b) ∈ m
  | [], _, _, h => by simp [findCache] at h
  | (k, v) :: m, a, b, h => by
    by_cases hk : k = a
    · subst hk
      simp [findCache] at h
      subst h
      exact List.mem_cons_self
    · simp only [findCache, hk, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ge_find_mem m a b h)

private theorem ge_record {g : SGraph T} {f : Nat} {a b : Addr} {ta tb : Tree T}
    {mp : Cache Addr} (hua : Graph.unfold g.view f a = some ta)
    (hub : Graph.unfold g.view f b = some tb) (h : ta = tb ∧ geInv g mp) :
    ta = tb ∧ geInv g ((a, b) :: mp) := by
  refine ⟨h.1, ?_⟩
  intro k v hkv
  rcases List.mem_cons.mp hkv with e | e
  · cases e
    exact ⟨f, ta, hua, by rw [h.1]; exact hub⟩
  · exact h.2 k v e

/-! ### Induction on fuel -/

private def geStep (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat)
    (acc : Bool × (Cache Addr × Cache Addr)) (xy : Addr × Addr) :
    Jl (Bool × (Cache Addr × Cache Addr)) :=
  if acc.1 then innerEqH g D veq f xy.1 xy.2 acc.2 else pure acc

private theorem ge_false_fold (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat) :
    ∀ (zs : List (Addr × Addr)) (m : Cache Addr × Cache Addr),
      zs.foldlM (geStep g D veq f) (false, m) = .ok (false, m)
  | [], _ => rfl
  | z :: zs, m => by
    simp only [List.foldlM_cons, geStep, Bool.false_eq_true, ↓reduceIte, ge_pure, ge_ok_bind]
    exact ge_false_fold g D veq f zs m

/-- The induction hypothesis for `innerEqH` at a given fuel. -/
private def geSpec (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat) : Prop :=
  ∀ (a b : Addr) (ta tb : Tree T) (m : Cache Addr × Cache Addr),
    Graph.unfold g.view f a = some ta → Graph.unfold g.view f b = some tb →
    DegLe D ta → DegLe D tb → geInv g m.1 →
    ∃ r m', innerEqH g D veq f a b m = .ok (r, m') ∧ (r = true → ta = tb ∧ geInv g m'.1)

private theorem ge_fold {g : SGraph T} {D : Nat} {veq : T → T → Bool} {f : Nat}
    (ih : geSpec g D veq f) :
    ∀ (xs ys : List Addr) (tsx tsy : List (Tree T)) (m : Cache Addr × Cache Addr),
      xs.length = ys.length →
      xs.mapM (Graph.unfold g.view f) = some tsx → ys.mapM (Graph.unfold g.view f) = some tsy →
      (∀ t ∈ tsx, DegLe D t) → (∀ t ∈ tsy, DegLe D t) → geInv g m.1 →
      ∃ r m', (xs.zip ys).foldlM (geStep g D veq f) (true, m) = .ok (r, m') ∧
        (r = true → tsx = tsy ∧ geInv g m'.1) := by
  intro xs
  induction xs with
  | nil =>
    intro ys tsx tsy m hl hx hy _ _ hm
    cases ys with
    | cons _ _ => simp at hl
    | nil =>
      simp at hx hy
      subst hx
      subst hy
      exact ⟨true, m, rfl, fun _ => ⟨rfl, hm⟩⟩
  | cons x xs ihx =>
    intro ys tsx tsy m hl hx hy hdx hdy hm
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      obtain ⟨tx, tsx', htx, htsx, rfl⟩ := (ge_mapM_cons _ x xs tsx).mp hx
      obtain ⟨ty, tsy', hty, htsy, rfl⟩ := (ge_mapM_cons _ y ys tsy).mp hy
      obtain ⟨r1, m1, h1, hr1⟩ := ih x y tx ty m htx hty (hdx tx (by simp)) (hdy ty (by simp)) hm
      have hstep : geStep g D veq f (true, m) (x, y) = .ok (r1, m1) := h1
      simp only [List.zip_cons_cons, List.foldlM_cons, hstep, ge_ok_bind]
      cases r1 with
      | false => exact ⟨false, m1, ge_false_fold g D veq f _ _, fun h => by cases h⟩
      | true =>
        obtain ⟨htxy, hm1⟩ := hr1 rfl
        obtain ⟨r, m', h2, hr⟩ := ihx ys tsx' tsy' m1 (by simpa using hl) htsx htsy
          (fun t ht => hdx t (by simp [ht])) (fun t ht => hdy t (by simp [ht])) hm1
        refine ⟨r, m', h2, fun h => ?_⟩
        obtain ⟨h3, h4⟩ := hr h
        exact ⟨by rw [htxy, h3], h4⟩

private theorem ge_step {g : SGraph T} {D : Nat} {veq : T → T → Bool} {f : Nat}
    (hveq : ∀ x y, veq x y = true ↔ x = y) (ih : geSpec g D veq f) :
    geSpec g D veq (f + 1) := by
  intro a b ta tb m hua hub hgA hgB hm
  obtain ⟨m1, m2⟩ := m
  cases h1 : findCache m1 a with
  | some b' =>
    cases h2 : findCache m2 b with
    | some a' =>
      refine ⟨b' == b && a' == a, (m1, m2), by simp [innerEqH, h1, h2, ge_pure], ?_⟩
      intro hr
      have hb' : b' = b := by simp at hr; exact hr.1
      rw [hb'] at h1
      obtain ⟨f', t, hfa, hfb⟩ := hm a b (ge_find_mem m1 a b h1)
      exact ⟨(ge_unfold_det _ _ a ta t hua hfa).trans (ge_unfold_det _ _ b t tb hfb hub), hm⟩
    | none =>
      exact ⟨false, (m1, m2), by simp [innerEqH, h1, h2, ge_pure], fun h => by cases h⟩
  | none =>
    cases h2 : findCache m2 b with
    | some a' =>
      exact ⟨false, (m1, m2), by simp [innerEqH, h1, h2, ge_pure], fun h => by cases h⟩
    | none =>
      have hm1 : geInv g m1 := hm
      obtain ⟨ca, hca, hlena, hcasea⟩ := ge_unfold_succ hua
      obtain ⟨cb, hcb, hlenb, hcaseb⟩ := ge_unfold_succ hub
      rcases hcasea with ⟨hza, hka, hfa⟩ | ⟨hza, tsa, htsa, rfl⟩ <;>
        rcases hcaseb with ⟨hzb, hkb, hfb⟩ | ⟨hzb, tsb, htsb, rfl⟩
      · -- two leaves
        cases hka' : ca.constant <;> cases hkb' : cb.constant
        · have hta := hfa hka'
          have htb := hfb hkb'
          subst hta
          subst htb
          refine ⟨ca.feature == cb.feature, ((a, b) :: m1, (b, a) :: m2), ?_,
            fun hr => ge_record hua hub ⟨?_, hm1⟩⟩
          · simp [innerEqH, h1, h2, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb',
              ge_ok_bind, ge_pure]
          · simp at hr
            rw [hr]
        · refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
          simp [innerEqH, h1, h2, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb',
            ge_ok_bind, ge_pure]
        · refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
          simp [innerEqH, h1, h2, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb',
            ge_ok_bind, ge_pure]
        · obtain ⟨va, hva, hta⟩ := hka hka'
          obtain ⟨vb, hvb, htb⟩ := hkb hkb'
          subst hta
          subst htb
          refine ⟨veq va vb, ((a, b) :: m1, (b, a) :: m2), ?_,
            fun hr => ge_record hua hub ⟨?_, hm1⟩⟩
          · simp [innerEqH, h1, h2, Heap.read, hca, hcb, hza, hzb, leafEqH, hka', hkb', hva,
              hvb, ge_ok_bind, ge_pure]
          · rw [(hveq va vb).mp hr]
      · -- leaf against branch
        have hne : ca.degree ≠ cb.degree := by omega
        refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
        simp [innerEqH, h1, h2, Heap.read, hca, hcb, hne, ge_ok_bind, ge_pure]
      · -- branch against leaf
        have hne : ca.degree ≠ cb.degree := by omega
        refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
        simp [innerEqH, h1, h2, Heap.read, hca, hcb, hne, ge_ok_bind, ge_pure]
      · -- two branches
        have hla := ge_mapM_length _ _ _ htsa
        have hlb := ge_mapM_length _ _ _ htsb
        by_cases heq : ca.degree = cb.degree
        · by_cases hop : ca.op = cb.op
          · simp only [DegLe] at hgA hgB
            have hD : cb.degree ≤ D := by omega
            have hk : nifDeg D cb.degree = cb.degree := by simp [nifDeg, hD]
            have hcsa : getChildren g D a (nifDeg D cb.degree) = .ok ca.active := by
              rw [hk, ← heq]; exact ge_getChildren hca hlena (by omega)
            have hcsb : getChildren g D b (nifDeg D cb.degree) = .ok cb.active := by
              rw [hk]; exact ge_getChildren hcb hlenb hD
            obtain ⟨r, mp, hfold, hr⟩ := ge_fold ih ca.active cb.active tsa tsb (m1, m2)
              (by omega) htsa htsb hgA.2 hgB.2 hm1
            refine ⟨r, ((a, b) :: mp.1, (b, a) :: mp.2), ?_, fun h => ?_⟩
            · simp only [innerEqH, h1, h2, Heap.read, hca, hcb, ge_ok_bind, heq, ne_eq,
                not_true_eq_false, hzb, hop, hcsa, hcsb, ↓reduceIte]
              erw [hfold]
              rfl
            · obtain ⟨hts, hmp⟩ := hr h
              exact ge_record hua hub ⟨by rw [hop, hts], hmp⟩
          · refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
            simp [innerEqH, h1, h2, Heap.read, hca, hcb, heq, hzb, hop, ge_ok_bind, ge_pure]
        · refine ⟨false, ((a, b) :: m1, (b, a) :: m2), ?_, fun h => by cases h⟩
          simp [innerEqH, h1, h2, Heap.read, hca, hcb, heq, ge_ok_bind, ge_pure]

private theorem ge_all (g : SGraph T) (D : Nat) (veq : T → T → Bool)
    (hveq : ∀ x y, veq x y = true ↔ x = y) : ∀ f, geSpec g D veq f := by
  intro f
  induction f with
  | zero => intro a b ta tb m hua; simp [Graph.unfold] at hua
  | succ f ih => exact ge_step hveq ih

theorem graph_eq_sound_holds : graph_eq_sound := by
  intro T veq hveq g D fuel a b ta tb hua hub hwa hwb
  obtain ⟨r, m', hrun, hr⟩ := ge_all g D veq hveq fuel a b ta tb ([], []) hua hub
    (ge_degLe ta hwa) (ge_degLe tb hwb) (fun _ _ h => by cases h)
  refine ⟨r, ?_, fun h => (hr h).1⟩
  unfold graphEqH
  rw [hrun]
  rfl

example : (∀ x y : Nat, (x == y) = true ↔ x = y) ∧
    Graph.unfold sharedSum.view 3 1 = some (.branch 1 [.feature 1, .feature 1]) ∧
    (Tree.branch 1 [.feature 1, .feature 1] : Tree Nat).WF 2 (fun _ => 255) 65535 :=
  ⟨fun x y => by simp, rfl, by simp [Tree.WF]⟩

end GraphEqProofs

end DynExpr.NodeBase
