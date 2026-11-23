import DynExpr.NodeBase.Traverse

/-! Properties of the heap `tree_mapreduce` (`src/base.jl:77-166`): node
counts with and without sharing, and reflexivity of `GraphNode` `==`. -/

namespace DynExpr.NodeBase
open DynExpr

/-- `count_nodes` on the heap: with `break_sharing = Val(true)` (and on plain
`Node` by default) it counts unfolded occurrences; on `GraphNode` by default
it counts each reachable object exactly once (`f_on_shared` returns 0 on
repeat visits through the identity map). -/
def count_nodes_graph : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T),
    Graph.unfold g.view fuel root = some t → DegLe D t →
    (∀ isGraph, countNodesH g D isGraph true fuel root = .ok t.size) ∧
    countNodesH g D false false fuel root = .ok t.size ∧
    ∃ l : List Addr, l.Nodup ∧ (∀ a, a ∈ l ↔ Graph.Reachable g.view root a) ∧
      countNodesH g D true false fuel root = .ok l.length

/-- `==` on `GraphNode` is reflexive on well-formed trees whose element `==`
is reflexive (no NaN-like constants). -/
def graph_eq_refl : Prop :=
  ∀ (T : Type) (veq : T → T → Bool), (∀ x, veq x x = true) →
    ∀ (g : SGraph T) (D fuel a : Nat) (t : Tree T),
      Graph.unfold g.view fuel a = some t → DegLe D t → graphEqH g D veq fuel a a = .ok true

/-! ## Proofs -/

section CountProofs
variable {T : Type}

private theorem tc_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem tc_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem tc_o_none {α β : Type} (f : α → Option β) : ((none : Option α) >>= f) = none := rfl

private theorem tc_o_some {α β : Type} (a : α) (f : α → Option β) : ((some a : Option α) >>= f) = f a :=
  rfl

private theorem tc_o_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

/-! ### Lists -/

private theorem tc_mapM_cons {α β : Type} (F : α → Option β) (x : α) (xs : List α) (ys : List β) :
    (x :: xs).mapM F = some ys ↔ ∃ y ys', F x = some y ∧ xs.mapM F = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons]
  cases hx : F x with
  | none => simp [tc_o_none]
  | some y =>
    cases hxs : xs.mapM F with
    | none => simp [tc_o_some, tc_o_none]
    | some ys' =>
      simp only [tc_o_some, tc_o_pure, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨y, ys', rfl, rfl, rfl⟩
      · rintro ⟨y1, ys1, h1, h2, rfl⟩
        subst h1; subst h2; rfl

private theorem tc_mapM_mem {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ∀ x ∈ xs, ∃ y ∈ ys, F x = some y := by
  intro xs
  induction xs with
  | nil => intro ys _ x hx; simp at hx
  | cons a as ih =>
    intro ys h x hx
    obtain ⟨y, ys', hy, hys, rfl⟩ := (tc_mapM_cons F a as ys).mp h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, hy⟩
    · obtain ⟨z, hz, hfz⟩ := ih ys' hys x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hfz⟩

private theorem tc_mapM_length {α β : Type} (F : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; rfl
  | cons a as ih =>
    intro ys h
    obtain ⟨y, ys', _, hys, rfl⟩ := (tc_mapM_cons F a as ys).mp h
    simp [ih ys' hys]

private theorem tc_mapM_snoc {α β : Type} (F : α → Option β) (x : α) (y : β) (hx : F x = some y) :
    ∀ (xs : List α) (ys : List β), xs.mapM F = some ys → (xs ++ [x]).mapM F = some (ys ++ [y]) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases h
    exact (tc_mapM_cons F x [] [y]).mpr ⟨y, [], hx, rfl, rfl⟩
  | cons a as ih =>
    intro ys h
    obtain ⟨z, zs, hz, hzs, rfl⟩ := (tc_mapM_cons F a as ys).mp h
    exact (tc_mapM_cons F a (as ++ [x]) _).mpr ⟨z, zs ++ [y], hz, ih zs hzs, rfl⟩

private theorem tc_filterMap_full {α : Type} :
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

private theorem tc_mapM_range_ok {α : Type} (f : Nat → Jl α) (h : Nat → α) :
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

private theorem tc_unfold_succ {g : SGraph T} {f : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view (f + 1) a = some t) :
    ∃ c, g.cells a = some c ∧ c.active.length = c.degree ∧
      ((c.degree = 0 ∧ (c.constant = true → ∃ v, c.val = some v ∧ t = .const v) ∧
          (c.constant = false → t = .feature c.feature)) ∨
       (c.degree ≠ 0 ∧ ∃ ts, c.active.mapM (Graph.unfold g.view f) = some ts ∧
          t = .branch c.op ts)) := by
  cases hc : g.cells a with
  | none =>
    have hv : g.view.cells a = none := by simp [SGraph.view, hc]
    simp only [Graph.unfold, hv, tc_o_none] at h
    cases h
  | some c =>
    have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
    refine ⟨c, rfl, ?_⟩
    simp only [Graph.unfold, hv, tc_o_some, SCell.toCell] at h
    by_cases hlen : c.active.length = c.degree
    · refine ⟨hlen, ?_⟩
      by_cases hd : c.degree = 0
      · left
        refine ⟨hd, ?_, ?_⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte] at h
          cases hval : c.val with
          | none => simp only [hval, tc_o_none] at h; cases h
          | some v =>
            simp only [hval, tc_o_some, tc_o_pure, Option.some.injEq] at h
            exact ⟨v, rfl, h.symm⟩
        · intro hk
          simp only [hlen, hd, hk, ne_eq, not_true_eq_false, ↓reduceIte, tc_o_pure,
            Bool.false_eq_true, Option.some.injEq] at h
          exact h.symm
      · right
        refine ⟨hd, ?_⟩
        simp only [hlen, hd, ne_eq, not_true_eq_false, ↓reduceIte] at h
        cases hm : c.active.mapM (Graph.unfold g.view f) with
        | none => simp only [hm, tc_o_none] at h; cases h
        | some ts =>
          simp only [hm, tc_o_some, tc_o_pure, Option.some.injEq] at h
          exact ⟨ts, rfl, h.symm⟩
    · simp only [hlen, ne_eq, not_false_eq_true, ↓reduceIte] at h
      cases h

private theorem tc_getChildren {g : SGraph T} {D a : Nat} {c : SCell T}
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
        apply tc_filterMap_full
        rw [← h1]
        omega
      have hsi : s[i]? = some (some ((c.active[i]?).getD 0)) := by
        have e1 : (s.take c.degree)[i]? = s[i]? := by simp [hi]
        rw [← e1, hfull]
        have hi' : i < c.active.length := by omega
        simp [List.getElem?_map, List.getElem?_eq_getElem hi']
      have h4 : 1 ≤ i + 1 ∧ i + 1 ≤ D := by omega
      simp [getChild, Heap.read, hc, hs, h4, hsi, tc_ok_bind, tc_pure]
  unfold getChildren
  rw [tc_mapM_range_ok _ _ c.degree hget]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

private theorem tc_path_fuel {g : SGraph T} {a b : Addr} {p : List Nat}
    (hp : Graph.Path g.view a p b) :
    ∀ fuel (t : Tree T), Graph.unfold g.view fuel a = some t →
      p.length < fuel ∧ ∃ t', Graph.unfold g.view (fuel - p.length) b = some t' := by
  induction hp with
  | nil a =>
    intro fuel t h
    cases fuel with
    | zero => simp [Graph.unfold] at h
    | succ f => exact ⟨by simp, t, by simpa using h⟩
  | @cons a x z i p c hc hi _ ih =>
    intro fuel t h
    cases fuel with
    | zero => simp [Graph.unfold] at h
    | succ f =>
      obtain ⟨c', hc', hlen, hcase⟩ := tc_unfold_succ h
      have hcc : c = c'.toCell := by
        simp only [SGraph.view, hc', Option.map_some, Option.some.injEq] at hc
        exact hc.symm
      subst hcc
      have hi' : c'.active[i]? = some x := hi
      rcases hcase with ⟨hd, _, _⟩ | ⟨_, ts, hts, _⟩
      · have hnil : c'.active = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [hnil] at hi'
        simp at hi'
      · obtain ⟨tx, _, htx⟩ := tc_mapM_mem _ _ _ hts x (List.mem_iff_getElem?.mpr ⟨i, hi'⟩)
        obtain ⟨hl, t', ht'⟩ := ih f tx htx
        refine ⟨by simp; omega, t', ?_⟩
        simpa using ht'

private theorem tc_path_pow {G : Graph T} {a : Addr} {q : List Nat} (hq : Graph.Path G a q a) :
    ∀ k, ∃ p, Graph.Path G a p a ∧ p.length = k * q.length := by
  intro k
  induction k with
  | zero => exact ⟨[], .nil a, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hl⟩ := ih
    exact ⟨p ++ q, hp.append hq, by simp [hl, Nat.succ_mul]⟩

private theorem tc_no_cycle {g : SGraph T} {fuel : Nat} {a : Addr} {t : Tree T}
    (h : Graph.unfold g.view fuel a = some t) {q : List Nat} (hq : Graph.Path g.view a q a) :
    q = [] := by
  cases q with
  | nil => rfl
  | cons i q' =>
    obtain ⟨p, hp, hl⟩ := tc_path_pow hq fuel
    have h1 := (tc_path_fuel hp fuel t h).1
    have h2 := Nat.mul_le_mul_left fuel (show 1 ≤ (i :: q').length by simp)
    rw [Nat.mul_one] at h2
    omega

private theorem tc_reach_cons {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c)
    (y : Addr) :
    Graph.Reachable g.view a y ↔ y = a ∨ ∃ x ∈ c.active, Graph.Reachable g.view x y := by
  have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
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

private theorem tc_reach_trans {G : Graph T} {a b c : Addr} :
    Graph.Reachable G a b → Graph.Reachable G b c → Graph.Reachable G a c
  | ⟨p, hp⟩, ⟨q, hq⟩ => ⟨p ++ q, hp.append hq⟩

/-- A child of a successfully unfolded node does not reach the node. -/
private theorem tc_child_not_reach {g : SGraph T} {fuel : Nat} {a x : Addr} {t : Tree T} {c : SCell T}
    (h : Graph.unfold g.view fuel a = some t) (hc : g.cells a = some c) (hx : x ∈ c.active)
    (hr : Graph.Reachable g.view x a) : False := by
  obtain ⟨q, hq⟩ := hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have hv : g.view.cells a = some c.toCell := by simp [SGraph.view, hc]
  have := tc_no_cycle h (Graph.Path.cons hv hi hq)
  cases this

/-! ### The traversal with `countNodesH` callbacks -/

private abbrev cntT (g : SGraph T) (D : Nat) (sh : Bool) :=
  tmrH (σ := Unit) (R := Nat) (B := Nat) g D sh (fun _ _ => pure 1) (fun _ _ => pure 1)
    (fun b rs => pure (b + rs.sum)) (fun c s => if s then 0 else c)

private def tcStep (g : SGraph T) (D : Nat) (sh : Bool) (fuel : Nat) (acc : List Nat × Cache Nat)
    (x : Addr) : StateT Unit Jl (List Nat × Cache Nat) := do
  let (r, c2) ← cntT g D sh fuel x acc.2
  pure (acc.1 ++ [r], c2)

private theorem tc_hit {g : SGraph T} {D f a r : Nat} {C : Cache Nat}
    (hfind : findCache C a = some r) : (cntT g D true (f + 1) a C).run () = .ok ((0, C), ()) := by
  simp only [cntT, tmrH, hfind, ↓reduceIte, StateT.run_pure, tc_pure]

private theorem tc_leaf {g : SGraph T} {D : Nat} {sh : Bool} {f a : Nat} {C : Cache Nat} {c : SCell T}
    (hfind : (if sh then findCache C a else none) = none) (hc : g.cells a = some c)
    (hd : c.degree = 0) :
    (cntT g D sh (f + 1) a C).run () = .ok ((1, if sh then (a, 1) :: C else C), ()) := by
  simp only [cntT, tmrH, hfind, StateT.run_bind, StateT.run_lift, Heap.read, hc, tc_ok_bind, hd,
    ↓reduceIte, StateT.run_pure, tc_pure]
  cases sh <;> rfl

private theorem tc_branch {g : SGraph T} {D : Nat} {sh : Bool} {f a : Nat} {C C' : Cache Nat}
    {c : SCell T} {cs : List Addr} {rs : List Nat}
    (hfind : (if sh then findCache C a else none) = none) (hc : g.cells a = some c)
    (hd : c.degree ≠ 0) (hcs : getChildren g D a (nifDeg D c.degree) = .ok cs)
    (hfold : (cs.foldlM (tcStep g D sh f) ([], C)).run () = .ok ((rs, C'), ())) :
    (cntT g D sh (f + 1) a C).run () =
      .ok ((1 + rs.sum, if sh then (a, 1 + rs.sum) :: C' else C'), ()) := by
  simp only [cntT, tmrH, hfind, StateT.run_bind, StateT.run_lift, Heap.read, hc, tc_ok_bind, hd,
    ↓reduceIte, StateT.run_pure, tc_pure, hcs]
  erw [hfold]
  cases sh <;> rfl

private theorem tc_step_run {g : SGraph T} {D : Nat} {sh : Bool} {f x n : Nat} {rs : List Nat}
    {C' C'' : Cache Nat} (h : (cntT g D sh f x C').run () = .ok ((n, C''), ())) :
    (tcStep g D sh f (rs, C') x).run () = .ok ((rs ++ [n], C''), ()) := by
  simp only [tcStep, StateT.run_bind, h, tc_ok_bind, StateT.run_pure, tc_pure]

private theorem tc_fold {α β : Type} (F : β → α → StateT Unit Jl β) (P : List α → β → Prop)
    (xs : List α)
    (hstep : ∀ done x b, P done b → x ∈ xs → ∃ b', (F b x).run () = .ok (b', ()) ∧ P (done ++ [x]) b') :
    ∀ ys done init, (∀ y ∈ ys, y ∈ xs) → P done init →
      ∃ b, (ys.foldlM F init).run () = .ok (b, ()) ∧ P (done ++ ys) b := by
  intro ys
  induction ys with
  | nil => intro done init _ hP; exact ⟨init, rfl, by simpa using hP⟩
  | cons y ys ih =>
    intro done init hsub hP
    obtain ⟨b', hb', hP'⟩ := hstep done y init hP (hsub y List.mem_cons_self)
    obtain ⟨b, hb, hP⟩ := ih (done ++ [y]) b' (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hP'
    refine ⟨b, ?_, by simpa using hP⟩
    simp only [List.foldlM_cons, StateT.run_bind, hb', tc_ok_bind]
    exact hb

private theorem tc_count_eq (g : SGraph T) (D : Nat) (isGraph bs : Bool) (fuel root n : Nat)
    (C' : Cache Nat) (h : (cntT g D (isGraph && !bs) fuel root []).run () = .ok ((n, C'), ())) :
    countNodesH g D isGraph bs fuel root = .ok n := by
  unfold countNodesH treeMapreduceH
  simp only [StateT.run'_eq, StateT.run_bind]
  erw [h]
  rfl

/-- Without the identity map the traversal counts unfolded occurrences. -/
private theorem tc_plain (g : SGraph T) (D : Nat) : ∀ fuel a (t : Tree T) (C : Cache Nat),
    Graph.unfold g.view fuel a = some t → DegLe D t →
    (cntT g D false fuel a C).run () = .ok ((t.size, C), ()) := by
  intro fuel
  induction fuel with
  | zero => intro a t C h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t C h hdeg
    obtain ⟨c, hc, hlen, hcase⟩ := tc_unfold_succ h
    have hfind : (if false then findCache C a else none) = none := rfl
    rcases hcase with ⟨hd, hcst, hfeat⟩ | ⟨hd, ts, hts, rfl⟩
    · have hsz : t.size = 1 := by
        cases hk : c.constant
        · rw [hfeat hk]; simp [Tree.size]
        · obtain ⟨v, _, rfl⟩ := hcst hk; simp [Tree.size]
      rw [hsz, tc_leaf hfind hc hd]
      rfl
    · simp only [DegLe] at hdeg
      have hlen' : c.degree ≤ D := by have := tc_mapM_length _ _ _ hts; omega
      have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlen']
      have hcs : getChildren g D a (nifDeg D c.degree) = .ok c.active := by
        rw [hnif]; exact tc_getChildren hc hlen hlen'
      let P : List Addr → List Nat × Cache Nat → Prop := fun done b =>
        b.2 = C ∧ ∃ ts', done.mapM (Graph.unfold g.view f) = some ts' ∧ b.1 = ts'.map Tree.size
      have hstep : ∀ done x b, P done b → x ∈ c.active →
          ∃ b', (tcStep g D false f b x).run () = .ok (b', ()) ∧ P (done ++ [x]) b' := by
        rintro done x ⟨rs, C'⟩ ⟨hb2, ts', hts', hb1⟩ hx
        simp only at hb2 hb1
        subst hb2
        obtain ⟨tx, htxm, htx⟩ := tc_mapM_mem _ _ _ hts x hx
        refine ⟨(rs ++ [tx.size], C'), tc_step_run (ih x tx C' htx (hdeg.2 tx htxm)), rfl,
          ts' ++ [tx], tc_mapM_snoc _ x tx htx done ts' hts', ?_⟩
        simp [hb1]
      obtain ⟨⟨rs, C'⟩, hb, hb2, ts', hts', hb1⟩ :=
        tc_fold (tcStep g D false f) P c.active hstep c.active [] ([], C) (fun _ h => h)
          ⟨rfl, [], rfl, rfl⟩
      simp only [List.nil_append] at hts'
      simp only at hb2 hb1
      subst hb2
      rw [hts] at hts'
      cases hts'
      rw [tc_branch hfind hc hd hcs hb, hb1]
      simp [Tree.size_branch]

private def tcInv (V : Graph T) (C : Cache Nat) : Prop :=
  (C.map Prod.fst).Nodup ∧ ∀ k ∈ C.map Prod.fst, ∀ y, Graph.Reachable V k y → y ∈ C.map Prod.fst

private theorem tc_inv_app {V : Graph T} {C new : Cache Nat} (R : Addr → Prop)
    (hR : ∀ y z, R y → Graph.Reachable V y z → R z)
    (hC : tcInv V C) (hn : (new.map Prod.fst).Nodup)
    (hk : ∀ y, y ∈ new.map Prod.fst ↔ R y ∧ y ∉ C.map Prod.fst) : tcInv V (new ++ C) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hn, hC.1, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact ((hk x).mp hx).2 hy
  · intro k hk' y hy
    rw [List.map_append, List.mem_append] at hk' ⊢
    rcases hk' with hk' | hk'
    · have hRy := hR k y ((hk k).mp hk').1 hy
      by_cases hyC : y ∈ C.map Prod.fst
      · exact Or.inr hyC
      · exact Or.inl ((hk y).mpr ⟨hRy, hyC⟩)
    · exact Or.inr (hC.2 k hk' y hy)

private theorem tc_find_none {C : Cache Nat} {a : Addr} (h : a ∉ C.map Prod.fst) :
    findCache C a = none := by
  induction C with
  | nil => rfl
  | cons kv C ih =>
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [findCache, Ne.symm h.1, ↓reduceIte]
    exact ih h.2

private theorem tc_find_some {C : Cache Nat} {a : Addr} (h : a ∈ C.map Prod.fst) :
    ∃ r, findCache C a = some r := by
  induction C with
  | nil => simp at h
  | cons kv C ih =>
    obtain ⟨k, v⟩ := kv
    by_cases hk : k = a
    · exact ⟨v, by simp [findCache, hk]⟩
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h.symm hk
      · obtain ⟨r, hr⟩ := ih h
        exact ⟨r, by simp [findCache, hk, hr]⟩

/-- With the identity map, a traversal from cache `C` adds exactly the
reachable objects not yet cached, each once, and returns their number. -/
private theorem tc_share (g : SGraph T) (D : Nat) : ∀ fuel a (t : Tree T) (C : Cache Nat),
    Graph.unfold g.view fuel a = some t → DegLe D t → tcInv g.view C →
    ∃ new : Cache Nat, (cntT g D true fuel a C).run () = .ok ((new.length, new ++ C), ()) ∧
      (new.map Prod.fst).Nodup ∧
      ∀ y, y ∈ new.map Prod.fst ↔ Graph.Reachable g.view a y ∧ y ∉ C.map Prod.fst := by
  intro fuel
  induction fuel with
  | zero => intro a t C h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t C h hdeg hinv
    by_cases ha : a ∈ C.map Prod.fst
    · obtain ⟨r, hr⟩ := tc_find_some ha
      refine ⟨[], ?_, List.nodup_nil, ?_⟩
      · simpa using tc_hit (g := g) (D := D) (f := f) hr
      · intro y
        simp only [List.map_nil, List.not_mem_nil, false_iff, not_and, Classical.not_not]
        exact fun hy => hinv.2 a ha y hy
    · have hfind : (if true then findCache C a else none) = none := by
        simp only [↓reduceIte]; exact tc_find_none ha
      obtain ⟨c, hc, hlen, hcase⟩ := tc_unfold_succ h
      rcases hcase with ⟨hd, _, _⟩ | ⟨hd, ts, hts, rfl⟩
      · have hnil : c.active = [] := List.eq_nil_of_length_eq_zero (by omega)
        refine ⟨[(a, 1)], ?_, by simp, ?_⟩
        · simpa using tc_leaf (D := D) (f := f) hfind hc hd
        · intro y
          rw [tc_reach_cons hc, hnil]
          simp only [List.map_cons, List.map_nil, List.mem_singleton, List.not_mem_nil,
            false_and, exists_false, or_false]
          constructor
          · rintro rfl; exact ⟨rfl, ha⟩
          · exact fun h => h.1
      · simp only [DegLe] at hdeg
        have hlen' : c.degree ≤ D := by have := tc_mapM_length _ _ _ hts; omega
        have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlen']
        have hcs : getChildren g D a (nifDeg D c.degree) = .ok c.active := by
          rw [hnif]; exact tc_getChildren hc hlen hlen'
        let P : List Addr → List Nat × Cache Nat → Prop := fun done b =>
          ∃ new : Cache Nat, b.2 = new ++ C ∧ (new.map Prod.fst).Nodup ∧
            (∀ y, y ∈ new.map Prod.fst ↔
              (∃ x ∈ done, Graph.Reachable g.view x y) ∧ y ∉ C.map Prod.fst) ∧
            b.1.sum = new.length
        have hstep : ∀ done x b, P done b → x ∈ c.active →
            ∃ b', (tcStep g D true f b x).run () = .ok (b', ()) ∧ P (done ++ [x]) b' := by
          rintro done x ⟨rs, C'⟩ ⟨new, hC', hnd, hkeys, hsum⟩ hx
          simp only at hC' hsum
          subst hC'
          have hinv' : tcInv g.view (new ++ C) :=
            tc_inv_app (fun y => ∃ x ∈ done, Graph.Reachable g.view x y)
              (fun y z ⟨x, hx, hxy⟩ hyz => ⟨x, hx, tc_reach_trans hxy hyz⟩) hinv hnd hkeys
          obtain ⟨tx, htxm, htx⟩ := tc_mapM_mem _ _ _ hts x hx
          obtain ⟨new1, hrun1, hnd1, hk1⟩ := ih x tx (new ++ C) htx (hdeg.2 tx htxm) hinv'
          refine ⟨(rs ++ [new1.length], new1 ++ (new ++ C)), tc_step_run hrun1, new1 ++ new,
            by simp, ?_, ?_, ?_⟩
          · rw [List.map_append, List.nodup_append]
            refine ⟨hnd1, hnd, ?_⟩
            intro u hu v hv huv
            subst huv
            have := ((hk1 u).mp hu).2
            rw [List.map_append, List.mem_append] at this
            exact this (Or.inl hv)
          · intro y
            rw [List.map_append, List.mem_append, hk1 y, hkeys y, List.map_append,
              List.mem_append]
            constructor
            · rintro (⟨hr, hn⟩ | ⟨⟨x', hx', hr⟩, hC⟩)
              · exact ⟨⟨x, List.mem_append_right _ (List.mem_singleton_self x), hr⟩,
                  fun h => hn (Or.inr h)⟩
              · exact ⟨⟨x', List.mem_append_left _ hx', hr⟩, hC⟩
            · rintro ⟨⟨x', hx', hr⟩, hC⟩
              rcases List.mem_append.mp hx' with hx' | hx'
              · exact Or.inr ⟨⟨x', hx', hr⟩, hC⟩
              · rw [List.mem_singleton] at hx'
                subst hx'
                by_cases hyn : y ∈ new.map Prod.fst
                · exact Or.inr ((hkeys y).mp hyn)
                · exact Or.inl ⟨hr, fun h => h.elim hyn hC⟩
          · simp only [List.sum_append, List.sum_cons, List.sum_nil, List.length_append, hsum]
            omega
        obtain ⟨⟨rs, C'⟩, hb, new, hC', hnd, hkeys, hsum⟩ :=
          tc_fold (tcStep g D true f) P c.active hstep c.active [] ([], C) (fun _ h => h)
            ⟨[], rfl, List.nodup_nil, by simp, rfl⟩
        simp only at hC' hsum
        subst hC'
        simp only [List.nil_append] at hkeys
        refine ⟨(a, 1 + rs.sum) :: new, ?_, ?_, ?_⟩
        · rw [tc_branch hfind hc hd hcs hb]
          simp [hsum, Nat.add_comm]
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hmem => ?_, hnd⟩
          obtain ⟨⟨x, hx, hr⟩, _⟩ := (hkeys a).mp hmem
          exact tc_child_not_reach h hc hx hr
        · intro y
          rw [tc_reach_cons hc, List.map_cons, List.mem_cons, hkeys y]
          constructor
          · rintro (rfl | ⟨hr, hC⟩)
            · exact ⟨Or.inl rfl, ha⟩
            · exact ⟨Or.inr hr, hC⟩
          · rintro ⟨rfl | hr, hC⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hr, hC⟩

theorem count_nodes_graph_holds : count_nodes_graph := by
  intro T g D fuel root t h hdeg
  have hplain : ∀ isGraph bs, (isGraph && !bs) = false →
      countNodesH g D isGraph bs fuel root = .ok t.size := by
    intro isGraph bs hsh
    exact tc_count_eq g D isGraph bs fuel root t.size []
      (by rw [hsh]; exact tc_plain g D fuel root t [] h hdeg)
  refine ⟨fun isGraph => hplain isGraph true (by simp), hplain false false rfl, ?_⟩
  obtain ⟨new, hrun, hnd, hkeys⟩ :=
    tc_share g D fuel root t [] h hdeg ⟨List.nodup_nil, by simp⟩
  refine ⟨new.map Prod.fst, hnd, fun a => by simpa using hkeys a, ?_⟩
  have := tc_count_eq g D true false fuel root new.length (new ++ []) hrun
  simpa using this

example : Graph.unfold oneLeaf.view 1 0 = some (.feature 1) ∧ DegLe 2 (Tree.feature 1 : Tree Nat) :=
  ⟨rfl, by simp [DegLe]⟩

/-! ### Equality -/

private def teStep (g : SGraph T) (D : Nat) (veq : T → T → Bool) (f : Nat)
    (acc : Bool × (Cache Addr × Cache Addr)) (xy : Addr × Addr) :
    Jl (Bool × (Cache Addr × Cache Addr)) :=
  if acc.1 then innerEqH g D veq f xy.1 xy.2 acc.2 else pure acc

/-- An identity map that sends every object to itself. -/
private abbrev TeId (m : Cache Addr) : Prop := ∀ k v, (k, v) ∈ m → v = k

private theorem te_id_cons {m : Cache Addr} (a : Addr) (hm : TeId m) : TeId ((a, a) :: m) := by
  intro k v h
  rcases List.mem_cons.mp h with e | e
  · cases e; rfl
  · exact hm k v e

private theorem te_find_self : ∀ (m : Cache Addr), TeId m → ∀ a v, findCache m a = some v → v = a
  | [], _, _, _, h => by simp [findCache] at h
  | (k, w) :: m, hm, a, v, h => by
    by_cases hk : k = a
    · subst hk
      simp [findCache] at h
      rw [← h]
      exact hm k w List.mem_cons_self
    · simp only [findCache, hk, ↓reduceIte] at h
      exact te_find_self m (fun k' v' h' => hm k' v' (List.mem_cons_of_mem _ h')) a v h

private theorem te_fold {α β : Type} (F : β → α → Jl β) (P : β → Prop) (xs : List α)
    (hstep : ∀ x b, P b → x ∈ xs → ∃ b', F b x = .ok b' ∧ P b') :
    ∀ (ys : List α) init, (∀ y ∈ ys, y ∈ xs) → P init → ∃ b, ys.foldlM F init = .ok b ∧ P b := by
  intro ys
  induction ys with
  | nil => intro init _ hP; exact ⟨init, rfl, hP⟩
  | cons y ys ih =>
    intro init hsub hP
    obtain ⟨b', hb', hP'⟩ := hstep y init hP (hsub y List.mem_cons_self)
    obtain ⟨b, hb, hP⟩ := ih b' (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hP'
    refine ⟨b, ?_, hP⟩
    simp only [List.foldlM_cons, hb', tc_ok_bind]
    exact hb

private theorem te_zip_self {α : Type} : ∀ (l : List α) (u v : α), (u, v) ∈ l.zip l → u = v ∧ u ∈ l
  | [], _, _, h => by simp at h
  | x :: l, u, v, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · cases h; exact ⟨rfl, List.mem_cons_self⟩
    · obtain ⟨huv, hu⟩ := te_zip_self l u v h
      exact ⟨huv, List.mem_cons_of_mem _ hu⟩

private theorem te_self (g : SGraph T) (D : Nat) (veq : T → T → Bool) (hveq : ∀ x, veq x x = true) :
    ∀ fuel a (t : Tree T) (m : Cache Addr), Graph.unfold g.view fuel a = some t → DegLe D t →
      TeId m → ∃ m', innerEqH g D veq fuel a a (m, m) = .ok (true, (m', m')) ∧ TeId m' := by
  intro fuel
  induction fuel with
  | zero => intro a t m h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t m h hdeg hid
    cases hm : findCache m a with
    | none =>
      obtain ⟨c, hc, hlen, hcase⟩ := tc_unfold_succ h
      rcases hcase with ⟨hd, hcst, _⟩ | ⟨hd, ts, hts, rfl⟩
      · refine ⟨(a, a) :: m, ?_, te_id_cons a hid⟩
        cases hk : c.constant
        · simp [innerEqH, hm, Heap.read, hc, hd, leafEqH, hk, tc_ok_bind, tc_pure]
        · obtain ⟨v, hv, _⟩ := hcst hk
          simp [innerEqH, hm, Heap.read, hc, hd, leafEqH, hk, hv, hveq, tc_ok_bind, tc_pure]
      · simp only [DegLe] at hdeg
        have hlen' : c.degree ≤ D := by have := tc_mapM_length _ _ _ hts; omega
        have hnif : nifDeg D c.degree = c.degree := by simp [nifDeg, hlen']
        have hcs : getChildren g D a (nifDeg D c.degree) = .ok c.active := by
          rw [hnif]; exact tc_getChildren hc hlen hlen'
        let P : Bool × (Cache Addr × Cache Addr) → Prop :=
          fun b => ∃ m', b = (true, (m', m')) ∧ TeId m'
        have hstep : ∀ xy b, P b → xy ∈ c.active.zip c.active →
            ∃ b', teStep g D veq f b xy = .ok b' ∧ P b' := by
          rintro ⟨u, v⟩ b ⟨m', rfl, hid'⟩ hxy
          obtain ⟨rfl, hu⟩ := te_zip_self _ u v hxy
          obtain ⟨tu, htum, htu⟩ := tc_mapM_mem _ _ _ hts u hu
          obtain ⟨m'', hm'', hid''⟩ := ih u tu m' htu (hdeg.2 tu htum) hid'
          exact ⟨_, by simp only [teStep, ↓reduceIte]; exact hm'', m'', rfl, hid''⟩
        obtain ⟨b, hb, m', rfl, hid'⟩ :=
          te_fold (teStep g D veq f) P (c.active.zip c.active) hstep _ (true, (m, m))
            (fun _ h => h) ⟨m, rfl, hid⟩
        refine ⟨(a, a) :: m', ?_, te_id_cons a hid'⟩
        simp only [innerEqH, hm, Heap.read, hc, tc_ok_bind, ne_eq, not_true_eq_false, hd,
          ↓reduceIte, hcs]
        erw [hb]
        rfl
    | some v =>
      have hv : v = a := te_find_self m hid a v hm
      subst hv
      exact ⟨m, by simp [innerEqH, hm, tc_pure], hid⟩

theorem graph_eq_refl_holds : graph_eq_refl := by
  intro T veq hveq g D fuel a t h hdeg
  obtain ⟨m', hm', _⟩ := te_self g D veq hveq fuel a t [] h hdeg (fun _ _ h => by cases h)
  unfold graphEqH
  rw [hm']
  rfl

example : (∀ x : Nat, (x == x) = true) ∧ Graph.unfold oneLeaf.view 1 0 = some (.feature 1) ∧
    DegLe 2 (Tree.feature 1 : Tree Nat) :=
  ⟨fun x => by simp, rfl, by simp [DegLe]⟩

end CountProofs

end DynExpr.NodeBase
