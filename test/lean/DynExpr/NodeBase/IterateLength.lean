import DynExpr.NodeBase.TraverseCount

/-! `iterate` and `length` on the heap agree (`src/base.jl:451-459`): both run
`tree_mapreduce` with the default `break_sharing`, so `collect` (through
`filter_map`, `src/base.jl:308-360`) visits exactly the objects that
`count_nodes` counts, whether or not the identity map is used. -/

namespace DynExpr.NodeBase
open DynExpr

section IterateProofs
variable {T : Type}

private theorem il_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem il_err_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

private theorem il_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem il_degLe {D : Nat} : ∀ t : Tree T, t.WF D (fun _ => 255) 65535 → DegLe D t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; simp [DegLe]
  | hf i => intro _; simp [DegLe]
  | hb op cs ih =>
    intro h
    simp only [Tree.WF] at h
    simp only [DegLe]
    exact ⟨h.1.2.1, fun c hc => ih c hc (h.2.2 c hc)⟩

/-- Two identity maps with the same keys hit on the same objects. -/
private theorem il_find_keys {α β : Type} {C : Cache α} {C' : Cache β} (a : Addr)
    (h : C.map Prod.fst = C'.map Prod.fst) :
    (findCache C a).isSome = (findCache C' a).isSome := by
  induction C generalizing C' with
  | nil =>
    cases C' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons kv C ih =>
    cases C' with
    | nil => simp at h
    | cons kv' C' =>
      obtain ⟨k, v⟩ := kv
      obtain ⟨k', v'⟩ := kv'
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      by_cases hk : k = a
      · simp [findCache, hk]
      · simp only [findCache, hk, ↓reduceIte]
        exact ih h2

/-! ### The two traversals -/

/-- The `count_nodes` traversal (`src/base.jl:271-280`). -/
private abbrev ilCnt (g : SGraph T) (D : Nat) (sh : Bool) :=
  tmrH (σ := Unit) (R := Nat) (B := Nat) g D sh (fun _ _ => pure 1) (fun _ _ => pure 1)
    (fun b rs => pure (b + rs.sum)) (fun c s => if s then 0 else c)

private def ilCntStep (g : SGraph T) (D : Nat) (sh : Bool) (fuel : Nat)
    (acc : List Nat × Cache Nat) (x : Addr) : StateT Unit Jl (List Nat × Cache Nat) := do
  let (r, c2) ← ilCnt g D sh fuel x acc.2
  pure (acc.1 ++ [r], c2)

/-- The `foreach` traversal of `collect` with the `filter_map!` callback
(`src/base.jl:287-298,333-338`). -/
private abbrev ilFill (g : SGraph T) (D : Nat) (sh : Bool) :=
  tmrH (σ := Nat × List (Option Addr)) (R := Unit) (B := Unit) g D sh
    (fmStepH (fun _ _ => true) (fun a _ => some a)) (fmStepH (fun _ _ => true) (fun a _ => some a))
    (fun (_ : Unit) (_ : List Unit) => pure ()) (fun r _ => r)

private def ilFillStep (g : SGraph T) (D : Nat) (sh : Bool) (f : Nat)
    (acc : List Unit × Cache Unit) (x : Addr) :
    StateT (Nat × List (Option Addr)) Jl (List Unit × Cache Unit) := do
  let (r, c2) ← ilFill g D sh f x acc.2
  pure (acc.1 ++ [r], c2)

private theorem il_cnt_step_ok {g : SGraph T} {D : Nat} {sh : Bool} {f x n : Nat} {rs : List Nat}
    {C' C'' : Cache Nat} (h : (ilCnt g D sh f x C').run () = .ok ((n, C''), ())) :
    (ilCntStep g D sh f (rs, C') x).run () = .ok ((rs ++ [n], C''), ()) := by
  simp only [ilCntStep, StateT.run_bind, h, il_ok_bind, StateT.run_pure, il_pure]

private theorem il_cnt_step_err {g : SGraph T} {D : Nat} {sh : Bool} {f x : Nat} {rs : List Nat}
    {C' : Cache Nat} {e : JlError} (h : (ilCnt g D sh f x C').run () = .error e) :
    (ilCntStep g D sh f (rs, C') x).run () = .error e := by
  simp only [ilCntStep, StateT.run_bind, h, il_err_bind]

private theorem il_fill_step {g : SGraph T} {D : Nat} {sh : Bool} {f : Nat} {x : Addr}
    {us : List Unit} {C C' : Cache Unit} {st st' : Nat × List (Option Addr)}
    (h : (ilFill g D sh f x C).run st = .ok (((), C'), st')) :
    (ilFillStep g D sh f (us, C) x).run st = .ok ((us ++ [()], C'), st') := by
  simp only [ilFillStep, StateT.run_bind, h, il_ok_bind, StateT.run_pure, il_pure]

private theorem il_fm_step (a : Addr) (c : SCell T) (k : Nat) (l : List (Option Addr))
    (h : k + 1 ≤ l.length) :
    (fmStepH (fun _ _ => true) (fun a _ => some a) a c).run (k, l) =
      .ok ((), (k + 1, l.set k (some a))) := by
  simp [fmStepH, h, StateT.run_bind] <;> rfl

/-! ### Simulation: `foreach` calls the callback once per counted node -/

/-- At a given fuel: whenever the counting traversal succeeds with result `n`,
the filling traversal from an identity map with the same keys succeeds, writes
`n` consecutive slots (if they fit), and ends with the same cache keys. -/
private def ilSim (g : SGraph T) (D : Nat) (sh : Bool) (f : Nat) : Prop :=
  ∀ (a : Addr) (C' C'' : Cache Nat) (n : Nat),
    (ilCnt g D sh f a C').run () = .ok ((n, C''), ()) →
    ∀ (C : Cache Unit) (k : Nat) (l : List (Option Addr)),
      C.map Prod.fst = C'.map Prod.fst → k + n ≤ l.length →
      ∃ C2 l', (ilFill g D sh f a C).run (k, l) = .ok (((), C2), (k + n, l')) ∧
        C2.map Prod.fst = C''.map Prod.fst ∧ l'.length = l.length

private theorem il_fold {g : SGraph T} {D : Nat} {sh : Bool} {f : Nat} (ih : ilSim g D sh f) :
    ∀ (xs : List Addr) (rs rs' : List Nat) (C' C'' : Cache Nat),
      (xs.foldlM (ilCntStep g D sh f) (rs, C')).run () = .ok ((rs', C''), ()) →
      ∃ ns, rs' = rs ++ ns ∧
        ∀ (us : List Unit) (C : Cache Unit) (k : Nat) (l : List (Option Addr)),
          C.map Prod.fst = C'.map Prod.fst → k + ns.sum ≤ l.length →
          ∃ us' C2 l', (xs.foldlM (ilFillStep g D sh f) (us, C)).run (k, l) =
              .ok ((us', C2), (k + ns.sum, l')) ∧
            C2.map Prod.fst = C''.map Prod.fst ∧ l'.length = l.length := by
  intro xs
  induction xs with
  | nil =>
    intro rs rs' C' C'' h
    have e : (([] : List Addr).foldlM (ilCntStep g D sh f) (rs, C')).run () =
        .ok ((rs, C'), ()) := rfl
    rw [e] at h
    have h' := Except.ok.inj h
    cases h'
    refine ⟨[], by simp, ?_⟩
    intro us C k l hC _
    exact ⟨us, C, l, rfl, hC, rfl⟩
  | cons x xs ihx =>
    intro rs rs' C' C'' h
    simp only [List.foldlM_cons, StateT.run_bind] at h
    rcases hres : (ilCnt g D sh f x C').run () with e | ⟨⟨n, C1⟩, ⟨⟩⟩
    · rw [il_cnt_step_err hres, il_err_bind] at h
      exact nomatch h
    · rw [il_cnt_step_ok hres] at h
      simp only [il_ok_bind] at h
      obtain ⟨ns', hns', hfill'⟩ := ihx (rs ++ [n]) rs' C1 C'' h
      refine ⟨n :: ns', by simp [hns'], ?_⟩
      intro us C k l hC hk
      simp only [List.sum_cons] at hk
      obtain ⟨C2, l1, hr1, hC2, hl1⟩ := ih x C' C1 n hres C k l hC (by omega)
      obtain ⟨us', C3, l2, hr2, hC3, hl2⟩ := hfill' (us ++ [()]) C2 (k + n) l1 hC2 (by omega)
      refine ⟨us', C3, l2, ?_, hC3, by rw [hl2, hl1]⟩
      simp only [List.foldlM_cons, StateT.run_bind, il_fill_step hr1, il_ok_bind]
      rw [hr2, List.sum_cons, Nat.add_assoc]

private theorem il_step {g : SGraph T} {D : Nat} {sh : Bool} {f : Nat} (ih : ilSim g D sh f) :
    ilSim g D sh (f + 1) := by
  intro a C' C'' n h C k l hC hk
  by_cases hhit : sh = true ∧ (findCache C' a).isSome = true
  · obtain ⟨rfl, hs⟩ := hhit
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ((il_find_keys a hC).trans hs)
    have e1 : (ilCnt g D true (f + 1) a C').run () = .ok ((0, C'), ()) := by
      simp only [ilCnt, tmrH, hr, ↓reduceIte, StateT.run_pure, il_pure]
    rw [e1] at h
    have h' := Except.ok.inj h
    cases h'
    refine ⟨C, l, ?_, hC, rfl⟩
    simp only [ilFill, tmrH, hu, ↓reduceIte, StateT.run_pure, il_pure]
    rfl
  · have hg' : (if sh then findCache C' a else none) = none := by
      cases sh
      · rfl
      · simp only [↓reduceIte]
        cases hf : findCache C' a with
        | none => rfl
        | some _ => exact absurd ⟨rfl, by simp [hf]⟩ hhit
    have hg : (if sh then findCache C a else none) = none := by
      cases sh
      · rfl
      · simp only [↓reduceIte]
        cases hf : findCache C a with
        | none => rfl
        | some _ => exact absurd ⟨rfl, by rw [← il_find_keys a hC, hf]; rfl⟩ hhit
    cases hr : g.read a with
    | error e =>
      have e1 : (ilCnt g D sh (f + 1) a C').run () = .error e := by
        simp only [ilCnt, tmrH, hg', StateT.run_bind, StateT.run_lift, hr, il_err_bind]
      rw [e1] at h
      exact nomatch h
    | ok c =>
      by_cases hd : c.degree = 0
      · have e1 : (ilCnt g D sh (f + 1) a C').run () =
            .ok ((1, if sh then (a, 1) :: C' else C'), ()) := by
          simp only [ilCnt, tmrH, hg', StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
            ↓reduceIte, StateT.run_pure, il_pure]
          cases sh <;> rfl
        rw [e1] at h
        have h' := Except.ok.inj h
        cases h'
        refine ⟨if sh then (a, ()) :: C else C, l.set k (some a), ?_, ?_, by simp⟩
        · simp only [ilFill, tmrH, hg, StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
            ↓reduceIte, StateT.run_pure, il_pure]
          erw [il_fm_step a c k l hk]
          cases sh <;> rfl
        · cases sh <;> simp [hC]
      · cases hcs : getChildren g D a (nifDeg D c.degree) with
        | error e =>
          have e1 : (ilCnt g D sh (f + 1) a C').run () = .error e := by
            simp only [ilCnt, tmrH, hg', StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
              ↓reduceIte, StateT.run_pure, il_pure, hcs, il_err_bind]
          rw [e1] at h
          exact nomatch h
        | ok cs =>
          rcases hfold : (cs.foldlM (ilCntStep g D sh f) ([], C')).run () with
            e | ⟨⟨rs, C1⟩, ⟨⟩⟩
          · have e1 : (ilCnt g D sh (f + 1) a C').run () = .error e := by
              simp only [ilCnt, tmrH, hg', StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
                ↓reduceIte, StateT.run_pure, il_pure, hcs]
              erw [hfold]
              rfl
            rw [e1] at h
            exact nomatch h
          · have e1 : (ilCnt g D sh (f + 1) a C').run () =
                .ok ((1 + rs.sum, if sh then (a, 1 + rs.sum) :: C1 else C1), ()) := by
              simp only [ilCnt, tmrH, hg', StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
                ↓reduceIte, StateT.run_pure, il_pure, hcs]
              erw [hfold]
              cases sh <;> rfl
            rw [e1] at h
            have h' := Except.ok.inj h
            cases h'
            obtain ⟨ns, hns, hfill⟩ := il_fold ih cs [] rs C' C1 hfold
            simp only [List.nil_append] at hns
            subst hns
            have hk1 : k + 1 ≤ l.length := by omega
            obtain ⟨us', C2, l', hr2, hC2, hl'⟩ :=
              hfill [] C (k + 1) (l.set k (some a)) hC (by simp; omega)
            refine ⟨if sh then (a, ()) :: C2 else C2, l', ?_, ?_, by rw [hl']; simp⟩
            · rw [← Nat.add_assoc]
              simp only [ilFill, tmrH, hg, StateT.run_bind, StateT.run_lift, hr, il_ok_bind, hd,
                ↓reduceIte, StateT.run_pure, il_pure, hcs]
              erw [il_fm_step a c k l hk1]
              simp only [il_ok_bind]
              erw [hr2]
              cases sh <;> rfl
            · cases sh <;> simp [hC2]

private theorem il_sim_all (g : SGraph T) (D : Nat) (sh : Bool) : ∀ f, ilSim g D sh f := by
  intro f
  induction f with
  | zero =>
    intro a C' C'' n h
    have e : (ilCnt g D sh 0 a C').run () = .error (.errorException "StackOverflowError") := rfl
    rw [e] at h
    exact nomatch h
  | succ f ih => exact il_step ih

private theorem il_count_run {g : SGraph T} {D : Nat} {isGraph : Bool} {fuel root : Nat}
    {res : Jl ((Nat × Cache Nat) × Unit)} (h : (ilCnt g D isGraph fuel root []).run () = res) :
    countNodesH g D isGraph false fuel root = res.map (fun p => p.1.1) := by
  unfold countNodesH treeMapreduceH
  simp only [StateT.run'_eq, StateT.run_bind, Bool.not_false, Bool.and_true]
  erw [h]
  cases res <;> rfl

/-- Iteration yields `length(tree)` elements (`src/base.jl:451-459`): the
`collect` pass writes one slot per object counted by `count_nodes`, which is
at least the root. -/
theorem iterate_length_holds : iterate_length := by
  intro T g D fuel root isGraph t hu hwf
  have hdeg := il_degLe t hwf
  obtain ⟨n, hcnt, hn1⟩ : ∃ n, countNodesH g D isGraph false fuel root = .ok n ∧ 1 ≤ n := by
    have hc := count_nodes_graph_holds T g D fuel root t hu hdeg
    cases isGraph
    · exact ⟨t.size, hc.2.1, by have := Tree.size_pos t; omega⟩
    · obtain ⟨L, _, hL, hcount⟩ := hc.2.2
      refine ⟨L.length, hcount, ?_⟩
      have hm : root ∈ L := (hL root).mpr ⟨[], .nil _⟩
      cases L with
      | nil => simp at hm
      | cons _ _ => simp
  rcases hres : (ilCnt g D isGraph fuel root []).run () with e | ⟨⟨m, C''⟩, ⟨⟩⟩
  · have := (il_count_run hres).symm.trans hcnt
    cases this
  · have hmn : m = n := Except.ok.inj ((il_count_run hres).symm.trans hcnt)
    subst hmn
    obtain ⟨C2, l', hfill, _, hlen⟩ :=
      il_sim_all g D isGraph fuel root [] C'' m hres [] 0 (List.replicate m none) rfl (by simp)
    have hcntH : countH g D isGraph false (fun _ _ => true) 0 fuel root = .ok m := by
      have e : countH g D isGraph false (fun _ _ => true) 0 fuel root =
          countNodesH g D isGraph false fuel root >>= fun n => pure (n + 0) := rfl
      rw [e, hcnt]
      rfl
    have hfe : (foreachH g D isGraph false (fmStepH (fun _ _ => true) (fun a _ => some a)) fuel
        root).run (0, List.replicate m none) = .ok ((), (0 + m, l')) := by
      unfold foreachH treeMapreduceH
      simp only [Bool.not_false, Bool.and_true, StateT.run_bind]
      erw [hfill]
      rfl
    have hcol : collectH g D isGraph false fuel root = .ok l' := by
      unfold collectH filterMapH
      rw [hcntH]
      simp only [il_ok_bind]
      erw [hfe]
      rfl
    refine ⟨some root :: l'.drop 1, ?_, ?_⟩
    · unfold iterElemsH
      rw [hcol]
      rfl
    · have hl : (some root :: l'.drop 1).length = m := by
        simp only [List.length_cons, List.length_drop, hlen, List.length_replicate]
        omega
      unfold lengthH
      rw [hl]
      exact hcnt

end IterateProofs

end DynExpr.NodeBase
