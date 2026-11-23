import DynExpr.Simplify.EnumProps

namespace DynExpr.Simplify
open DynExpr

private def putPairs (qs : List (Int × List Fn)) (a : List (List Fn)) :=
  qs.foldl (fun a q => a.set (q.1.toNat - 1) q.2) a

private theorem pairs_fold_ok (qs : List (Int × List Fn)) (a : List (List Fn))
    (hp : DegreesPos qs) :
    qs.foldlM (fun arr q => if q.1 < 1 then
      throw (.argumentError s!"Degree must be ≥ 1, got {q.1}")
      else pure (arr.set (q.1.toNat - 1) q.2)) a = (.ok (putPairs qs a) : Jl _) := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih =>
    have hq := hp q (by simp)
    have ht : DegreesPos qs := fun r hr => hp r (by simp [hr])
    simpa [List.foldlM_cons, putPairs, List.foldl_cons, show ¬ q.1 < 1 by omega]
      using ih (a.set (q.1.toNat - 1) q.2) ht

private theorem putPairs_length (qs : List (Int × List Fn)) (a : List (List Fn)) :
    (putPairs qs a).length = a.length := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih => simpa [putPairs, List.foldl_cons] using ih (a.set _ q.2)

private theorem max_fold_bounds (qs : List (Int × List Fn)) (m : Int) :
    m ≤ qs.foldl (fun m q => max m q.1) m ∧
    ∀ q ∈ qs, q.1 ≤ qs.foldl (fun m q => max m q.1) m := by
  induction qs generalizing m with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨hle, hall⟩ := ih (max m q.1)
    simp only [List.foldl_cons]
    constructor
    · exact Int.le_trans (Int.le_max_left _ _) hle
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Int.le_trans (Int.le_max_right _ _) hle
      · exact hall r hr

private theorem putPairs_hole (qs : List (Int × List Fn)) (a : List (List Fn)) (k : Nat)
    (h : ∀ q ∈ qs, q.1.toNat - 1 ≠ k) : (putPairs qs a)[k]? = a[k]? := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih =>
    change (putPairs qs (a.set (q.1.toNat - 1) q.2))[k]? = _
    rw [ih _ (fun r hr => h r (by simp [hr])), List.getElem?_set_ne (h q (by simp))]

private theorem putPairs_slot (qs : List (Int × List Fn)) (a : List (List Fn))
    (hp : DegreesPos qs) (hn : (qs.map Prod.fst).Nodup)
    (hb : ∀ q ∈ qs, q.1.toNat - 1 < a.length) :
    ∀ q ∈ qs, (putPairs qs a)[q.1.toNat - 1]? = some q.2 := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs ih =>
    have hp' : DegreesPos qs := fun r hr => hp r (by simp [hr])
    have hn' := (List.nodup_cons.mp hn).2
    have hne := (List.nodup_cons.mp hn).1
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      change (putPairs qs (a.set (q.1.toNat - 1) q.2))[q.1.toNat - 1]? = _
      rw [putPairs_hole]
      · exact List.getElem?_set_self (hb q (by simp))
      · intro r hr heq
        have hqp := hp q (by simp)
        have hrp := hp' r hr
        have he : r.1 = q.1 := by omega
        exact hne (List.mem_map.mpr ⟨r, hr, he⟩)
    · exact ih _ hp' hn' (by simpa using fun r hr => hb r (by simp [hr])) r hr

theorem enum_pairs_layout_proof : enum_pairs_layout := by
  intro p ps hp hn
  let m := ps.foldl (fun m q => max m q.1) p.1
  let a : List (List Fn) := List.replicate m.toNat []
  have hm : ∀ q ∈ p :: ps, q.1 ≤ m := by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · subst q
      exact (max_fold_bounds ps p.1).1
    · exact (max_fold_bounds ps p.1).2 q hq
  have hb : ∀ q ∈ p :: ps, q.1.toNat - 1 < a.length := by
    intro q hq
    have hpos := hp q hq
    have hle := Int.toNat_le_toNat (hm q hq)
    simp only [a, List.length_replicate]
    omega
  refine ⟨putPairs (p :: ps) a, pairs_fold_ok _ _ hp, ?_, putPairs_slot _ _ hp hn hb, ?_⟩
  · simp [putPairs_length, a, m]
  · intro d hd hlen hh
    rw [putPairs_hole]
    · simp only [a, List.getElem?_replicate]
      have hlen' : d ≤ m.toNat := by simpa [putPairs_length, a] using hlen
      simp [show d - 1 < m.toNat by omega]
    · intro q hq he
      have hpq := hp q hq
      apply hh q hq
      omega

theorem enum_pairs_keep_all_operators_proof : enum_pairs_keep_all_operators := by
  intro p ps hp
  let m := ps.foldl (fun m q => max m q.1) p.1
  let a : List (List Fn) := List.replicate m.toNat []
  have hm : ∀ q ∈ p :: ps, q.1 ≤ m := by
    intro q hq
    rcases List.mem_cons.mp hq with he | hq
    · subst q
      exact (max_fold_bounds ps p.1).1
    · exact (max_fold_bounds ps p.1).2 q hq
  have hb : ∀ q ∈ p :: ps, q.1.toNat - 1 < a.length := by
    intro q hq
    have hpos := hp q hq
    have hle := Int.toNat_le_toNat (hm q hq)
    simp only [a, List.length_replicate]
    omega
  refine ⟨putPairs (p :: ps) a, pairs_fold_ok _ _ hp, ?_, ?_, ?_⟩
  · simp [putPairs_length, a, m]
  · intro before q after he hh
    have hq : q ∈ p :: ps := by rw [he]; simp
    have hpos := hp q hq
    have hbound := hb q hq
    rw [he]
    simp only [putPairs, List.foldl_append, List.foldl_cons]
    change (putPairs after ((putPairs before a).set (q.1.toNat - 1) q.2))[q.1.toNat - 1]? = _
    rw [putPairs_hole]
    · exact List.getElem?_set_self (by simpa [putPairs_length] using hbound)
    · intro r hr hidx
      have hr' : r ∈ p :: ps := by rw [he]; simp [hr]
      have hrpos := hp r hr'
      apply hh r hr
      omega
  · intro d hd hlen hh
    rw [putPairs_hole]
    · simp only [a, List.getElem?_replicate]
      have hlen' : d ≤ m.toNat := by simpa [putPairs_length, a] using hlen
      simp [show d - 1 < m.toNat by omega]
    · intro q hq he
      have hpq := hp q hq
      apply hh q hq
      omega

example : DegreesPos ((1, [.plain 0]) :: [(1, [.plain 1]), (3, [])]) := by
  intro q hq
  simp at hq
  rcases hq with rfl | rfl | rfl <;> decide

private theorem pairs_fold_bad (qs : List (Int × List Fn)) (a : List (List Fn))
    (h : ∃ q ∈ qs, q.1 < 1) :
    ∃ msg, qs.foldlM (fun arr q => if q.1 < 1 then
      throw (.argumentError s!"Degree must be ≥ 1, got {q.1}")
      else pure (arr.set (q.1.toNat - 1) q.2)) a = (.error (.argumentError msg) : Jl _) := by
  induction qs generalizing a with
  | nil => simp at h
  | cons q qs ih =>
    by_cases hq : q.1 < 1
    · exact ⟨_, by simp [List.foldlM_cons, hq]; rfl⟩
    · obtain ⟨r, hr, hbad⟩ := h
      have hr' : r ∈ qs := by rcases List.mem_cons.mp hr with rfl | hr; contradiction; exact hr
      obtain ⟨msg, hm⟩ := ih (a.set (q.1.toNat - 1) q.2) ⟨r, hr', hbad⟩
      exact ⟨msg, by simpa [List.foldlM_cons, hq] using hm⟩

theorem enum_pairs_nonpositive_rejected_proof : enum_pairs_nonpositive_rejected := by
  intro p ps h
  exact pairs_fold_bad _ _ h

theorem set_default_variable_names_copies_proof : set_default_variable_names_copies := by
  intro h v names st hr
  let a := (h.alloc names).1
  let h1 := (h.alloc names).2
  have hne : a ≠ v := by
    intro he
    have hc := Heap.alloc_fresh h names
    have hv : h.cells v ≠ none := by intro hn; simp [Heap.read, hn] at hr
    exact hv (he ▸ hc)
  refine ⟨a, h1, {st with varNames := a}, ?_, rfl, Heap.read_alloc_same _ _, ?_⟩
  · simp [setDefaultVariableNames, hr, a, h1]
    rfl
  · intro newNames h2 hw
    exact (Heap.read_write_other h1 h2 v a newNames hw hne).trans (Heap.read_alloc_same _ _)

example : DegreesPos ((1, [.plain 0]) :: [(3, [.plain 1])]) ∧
    ([((1 : Int), [Fn.plain 0]), (3, [Fn.plain 1])].map Prod.fst).Nodup := by
  constructor
  · intro q hq; simp at hq; rcases hq with rfl | rfl <;> decide
  · decide

example : ∃ q ∈ ([(0, [.plain 0])] : List (Int × List Fn)), q.1 < 1 := by decide

example : (Heap.empty.alloc (["x"] : List String)).2.read
    (Heap.empty.alloc (["x"] : List String)).1 = .ok ["x"] := Heap.read_alloc_same _ _

private theorem forM_guard (xs : List α) (bad : α → Bool) (e : JlError) :
    xs.forM (fun a => if bad a then (Except.error e : Jl PUnit) else pure ()) =
      if xs.any bad then .error e else .ok () := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (do let _ ← (if bad a then (Except.error e : Jl PUnit) else pure ())
               xs.forM (fun a => if bad a then (Except.error e : Jl PUnit) else pure ())) =
      (if bad a || xs.any bad then .error e else .ok ())
    rw [ih]
    cases bad a <;> cases xs.any bad <;> rfl

private def badOp (ops : List (List Fn)) : Fn → Bool
  | .plain _ => false
  | .bcast n => ops.any (fun t => t.contains (.plain n))

private theorem validate_formula (ops : List (List Fn)) :
    validateBroadcasts ops =
      if ops.any (fun t => t.any (badOp ops)) then
        .error (.argumentError "Usage of both broadcasted and unbroadcasted operator is ambiguous")
      else .ok () := by
  unfold validateBroadcasts
  have hinner : ∀ tup : List Fn,
      tup.forM (fun op => match op with
        | .bcast n => if ops.any (fun other => other.contains (.plain n)) then
            throw (.argumentError "Usage of both broadcasted and unbroadcasted operator is ambiguous")
          else pure ()
        | .plain _ => pure ()) =
      (if tup.any (badOp ops) then
        .error (.argumentError "Usage of both broadcasted and unbroadcasted operator is ambiguous")
      else .ok () : Jl PUnit) := by
    intro tup
    rw [← forM_guard tup (badOp ops) (.argumentError "Usage of both broadcasted and unbroadcasted operator is ambiguous")]
    congr 1
    funext op
    cases op <;> rfl
  exact (congrArg (fun g : List Fn → Jl PUnit => ops.forM g) (funext hinner)).trans
    (forM_guard ops (fun t => t.any (badOp ops)) _)

private theorem conflict_iff (ops : List (List Fn)) :
    ops.any (fun t => t.any (badOp ops)) = true ↔
      ∃ n, (∃ t ∈ ops, Fn.bcast n ∈ t) ∧ (∃ t ∈ ops, Fn.plain n ∈ t) := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, f, hf, hb⟩
    cases f with
    | plain n => simp [badOp] at hb
    | bcast n =>
      simp only [badOp, List.any_eq_true, List.contains_iff_mem] at hb
      exact ⟨n, ⟨t, ht, hf⟩, hb⟩
  · rintro ⟨n, ⟨t, ht, hf⟩, hs⟩
    exact ⟨t, ht, .bcast n, hf, by simpa [badOp, List.any_eq_true] using hs⟩

private theorem validate_ok (ops : List (List Fn))
    (h : ∀ n, (∃ t ∈ ops, Fn.bcast n ∈ t) → ∀ t ∈ ops, Fn.plain n ∉ t) :
    validateBroadcasts ops = .ok () := by
  rw [validate_formula]
  have hn : ops.any (fun t => t.any (badOp ops)) ≠ true := by
    intro hc
    obtain ⟨n, hb, t, ht, hf⟩ := (conflict_iff ops).mp hc
    exact h n hb t ht hf
  simp [hn]

private def putOp (inBase : Fn → Bool) (skip : Bool) (d : Nat) (st : Globals)
    (f : Fn) (i : Nat) : Globals :=
  let st := {st with mapping := fun d' f' =>
    if d' = d ∧ f' = f then some i else st.mapping d' f'}
  if !inBase f && skip then st
  else {st with defined := fun d' f' => decide (d' = d ∧ f' = f) || st.defined d' f'}

private def putTuple (inBase : Fn → Bool) (skip : Bool) (d : Nat) :
    Nat → List Fn → Globals → Globals
  | _, [], st => st
  | i, f :: fs, st => putTuple inBase skip d (i + 1) fs (putOp inBase skip d st f i)

private theorem tuple_run (inBase : Fn → Bool) (skip : Bool) (d n : Nat)
    (xs : List Fn) (st : Globals) (hb : n + xs.length ≤ 256) :
    (enumFrom n xs).foldlM (registerOp inBase skip d) st =
      .ok (putTuple inBase skip d n xs st) := by
  induction xs generalizing n st with
  | nil => rfl
  | cons f fs ih =>
    have hn : ¬ 255 < n := by simp only [List.length_cons] at hb; omega
    have hr : registerOp inBase skip d st (f, n) = .ok (putOp inBase skip d st f n) := by
      cases hs : (!inBase f && skip) <;> simp [registerOp, putOp, hn, hs] <;> rfl
    rw [show enumFrom n (f :: fs) = (f, n) :: enumFrom (n + 1) fs from rfl, List.foldlM_cons, hr]
    exact ih (n + 1) (putOp inBase skip d st f n) (by simp_all; omega)

private def lastIndex : Nat → List Fn → Fn → Option Nat
  | _, [], _ => none
  | n, f :: fs, g => (lastIndex (n + 1) fs g).orElse (fun _ => if g = f then some n else none)

private theorem tuple_mapping (inBase : Fn → Bool) (skip : Bool) (d n : Nat)
    (xs : List Fn) (st : Globals) (e : Nat) (f : Fn) :
    (putTuple inBase skip d n xs st).mapping e f =
      if e = d then (lastIndex n xs f).orElse (fun _ => st.mapping e f) else st.mapping e f := by
  induction xs generalizing n st with
  | nil => simp [putTuple, lastIndex]
  | cons g gs ih =>
    simp only [putTuple, ih, lastIndex]
    by_cases hed : e = d
    · simp only [hed, ↓reduceIte]
      cases hl : lastIndex (n + 1) gs f <;>
        cases hs : (!inBase g && skip) <;>
        by_cases hfg : f = g <;> simp [putOp, hs, hfg]
    · cases hs : (!inBase g && skip) <;> simp [putOp, hs, hed]

private theorem lastIndex_none (n : Nat) (xs : List Fn) (f : Fn) :
    lastIndex n xs f = none ↔ f ∉ xs := by
  induction xs generalizing n with
  | nil => simp [lastIndex]
  | cons g gs ih =>
    cases hl : lastIndex (n + 1) gs f with
    | none => by_cases hfg : f = g <;> simp_all [lastIndex]
    | some j =>
      have hm : f ∈ gs := by
        apply Classical.byContradiction
        intro hnot
        have := (ih (n + 1)).mpr hnot
        simp [hl] at this
      simp [lastIndex, hl, hm]

private theorem lastIndex_sound (n : Nat) (xs : List Fn) (f : Fn) (i : Nat)
    (hi : lastIndex n xs f = some i) :
    n ≤ i ∧ xs[i - n]? = some f := by
  induction xs generalizing n i with
  | nil => simp [lastIndex] at hi
  | cons g gs ih =>
    cases hl : lastIndex (n + 1) gs f with
    | some j =>
      simp [lastIndex, hl] at hi
      subst i
      obtain ⟨hj, hs⟩ := ih (n + 1) j hl
      exact ⟨by omega, by simpa [show j - n = (j - (n + 1)) + 1 by omega] using hs⟩
    | none =>
      by_cases hf : f = g
      · have hi' : n = i := by simpa only [lastIndex, hl, Option.orElse_none, ite_eq_left hf, Option.some.injEq] using hi
        subst i
        exact ⟨Nat.le_refl _, by simp [hf]⟩
      · simp [lastIndex, hl, hf] at hi


private def putOps (inBase : Fn → Bool) (skip : Bool) :
    Nat → List (List Fn) → Globals → Globals
  | _, [], st => st
  | d, t :: ts, st => putOps inBase skip (d + 1) ts (putTuple inBase skip d 1 t st)

private theorem ops_run (inBase : Fn → Bool) (skip : Bool) (d : Nat)
    (ops : List (List Fn)) (st : Globals) (hb : ∀ t ∈ ops, t.length ≤ 255) :
    (enumFrom d ops).foldlM (fun st dq =>
      (enumFrom 1 dq.1).foldlM (registerOp inBase skip dq.2) st) st =
        .ok (putOps inBase skip d ops st) := by
  induction ops generalizing d st with
  | nil => rfl
  | cons t ts ih =>
    simp only [enumFrom, List.foldlM_cons]
    rw [tuple_run _ _ _ _ _ _ (by have := hb t (by simp); omega)]
    exact ih (d + 1) (putTuple inBase skip d 1 t st)
      (fun u hu => hb u (by simp [hu]))

private theorem ops_mapping (inBase : Fn → Bool) (skip : Bool) (d : Nat)
    (ops : List (List Fn)) (st : Globals) (e : Nat) (f : Fn) :
    (putOps inBase skip d ops st).mapping e f =
      if d ≤ e then (lastIndex 1 (ops[e - d]?.getD []) f).orElse (fun _ => st.mapping e f)
      else st.mapping e f := by
  induction ops generalizing d st with
  | nil => simp [putOps, lastIndex]
  | cons t ts ih =>
    simp only [putOps, ih, tuple_mapping]
    by_cases he : e = d
    · subst e
      simp [show ¬ d + 1 ≤ d by omega]
    · by_cases hlt : e < d
      · simp [show ¬ d ≤ e by omega, show ¬ d + 1 ≤ e by omega, he]
      · have hle : d + 1 ≤ e := by omega
        have hidx : e - d = (e - (d + 1)) + 1 := by omega
        simp [hle, show d ≤ e by omega, he, hidx]

private theorem tuple_defined (inBase : Fn → Bool) (skip : Bool) (d n : Nat)
    (xs : List Fn) (st : Globals) (e : Nat) (f : Fn) :
    (putTuple inBase skip d n xs st).defined e f = true ↔
      st.defined e f = true ∨ (e = d ∧ f ∈ xs ∧ (inBase f = true ∨ skip = false)) := by
  induction xs generalizing n st with
  | nil => simp [putTuple]
  | cons g gs ih =>
    simp only [putTuple, ih]
    cases hb : inBase g <;> cases hs : skip <;>
      by_cases he : e = d <;> by_cases hf : f = g <;>
      simp_all [putOp, List.mem_cons] <;> grind

private theorem ops_preserve_defined (inBase : Fn → Bool) (skip : Bool) (d : Nat)
    (ops : List (List Fn)) (st : Globals) (e : Nat) (f : Fn)
    (h : st.defined e f = true) : (putOps inBase skip d ops st).defined e f = true := by
  induction ops generalizing d st with
  | nil => exact h
  | cons t ts ih =>
    exact ih (d + 1) _ ((tuple_defined _ _ _ _ _ _ _ _).mpr (Or.inl h))

private theorem ops_defined (inBase : Fn → Bool) (skip : Bool) (d : Nat)
    (ops : List (List Fn)) (st : Globals) (e : Nat) (f : Fn)
    (hle : d ≤ e) (hf : f ∈ (ops[e - d]?.getD []))
    (hb : inBase f = true ∨ skip = false) :
    (putOps inBase skip d ops st).defined e f = true := by
  induction ops generalizing d st with
  | nil => simp at hf
  | cons t ts ih =>
    by_cases he : e = d
    · subst e
      have hft : f ∈ t := by simpa using hf
      exact ops_preserve_defined inBase skip (d + 1) ts (putTuple inBase skip d 1 t st) d f
        ((tuple_defined inBase skip d 1 t st d f).mpr (Or.inr ⟨rfl, hft, hb⟩))
    · have hle' : d + 1 ≤ e := by omega
      have hidx : e - d = (e - (d + 1)) + 1 := by omega
      exact ih (d + 1) _ hle' (by simpa [hidx] using hf)

private theorem extend_run (inBase : Fn → Bool) (skip : Bool) (ops : List (List Fn))
    (emptyOld : Bool) (st : Globals) (hb : ∀ t ∈ ops, t.length ≤ 255)
    (hv : validateBroadcasts ops = .ok ()) :
    extendOperators inBase skip ops emptyOld st =
      .ok (putOps inBase skip 1 ops (if emptyOld then {st with mapping := fun _ _ => none} else st)) := by
  simp only [extendOperators, hv]
  exact ops_run inBase skip 1 ops _ hb

private theorem mem_set_subset (a : List α) (i : Nat) (v t : α)
    (h : t ∈ a.set i v) : t = v ∨ t ∈ a := by
  induction a generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero =>
      simp at h
      rcases h with he | ht
      · exact Or.inl he
      · exact Or.inr (by simp [ht])
    | succ i =>
      simp at h
      rcases h with he | ht
      · exact Or.inr (by simp [he])
      · rcases ih i ht with he | ht
        · exact Or.inl he
        · exact Or.inr (by simp [ht])

private theorem pairs_values (qs : List (Int × List Fn)) (a : List (List Fn)) :
    ∀ t ∈ putPairs qs a, t ∈ a ∨ ∃ q ∈ qs, t = q.2 := by
  induction qs generalizing a with
  | nil => intro t ht; exact Or.inl ht
  | cons q qs ih =>
    intro t ht
    rcases ih (a.set (q.1.toNat - 1) q.2) t ht with ht | ⟨r, hr, he⟩
    · have : t = q.2 ∨ t ∈ a := mem_set_subset a _ _ t ht
      rcases this with he | ha
      · exact Or.inr ⟨q, by simp, he⟩
      · exact Or.inl ha
    · exact Or.inr ⟨r, by simp [hr], he⟩

private theorem input_ops (p : Int × List Fn) (ps : List (Int × List Fn))
    (h : EnumInput p ps) :
    ∃ ops, pairsToOpsTuple p ps = .ok ops ∧ (∀ t ∈ ops, t.length ≤ 255) ∧
      (∀ n, (∃ t ∈ ops, Fn.bcast n ∈ t) → ∀ t ∈ ops, Fn.plain n ∉ t) := by
  let a : List (List Fn) := List.replicate (ps.foldl (fun m q => max m q.1) p.1).toNat []
  refine ⟨putPairs (p :: ps) a, pairs_fold_ok _ _ h.1, ?_, ?_⟩
  · intro t ht
    rcases pairs_values _ _ t ht with ha | ⟨q, hq, rfl⟩
    · have : t = [] := (List.mem_replicate.mp ha).2
      simp [this]
    · exact h.2.1 q hq
  · intro n ⟨t, ht, hf⟩ u hu hp
    have hb : ∃ q ∈ p :: ps, Fn.bcast n ∈ q.2 := by
      rcases pairs_values _ _ t ht with ha | ⟨q, hq, rfl⟩
      · have : t = [] := (List.mem_replicate.mp ha).2
        simp [this] at hf
      · exact ⟨q, hq, hf⟩
    obtain ⟨q, hq, hbf⟩ := hb
    rcases pairs_values _ _ u hu with ha | ⟨r, hr, rfl⟩
    · have : u = [] := (List.mem_replicate.mp ha).2
      simp [this] at hp
    · exact h.2.2 q hq n hbf r hr hp


private theorem make_ready (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st : Globals) (h : EnumInput p ps) :
    ∃ ops st', makeEnum inBase kind p ps true true st = .ok (ops, st') ∧
      (∀ d f, 1 ≤ d → st'.mapping d f = lastIndex 1 (ops[d - 1]?.getD []) f) ∧
      (∀ d f, 1 ≤ d → f ∈ (ops[d - 1]?.getD []) → inBase f = true → st'.defined d f = true) := by
  obtain ⟨ops, hp, hb, hv⟩ := input_ops p ps h
  let s := putOps inBase true 1 ops {st with mapping := fun _ _ => none}
  refine ⟨ops, {s with latest := some (kind, ops)}, ?_, ?_, ?_⟩
  · rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true ops true st
               pure (ops, {s with latest := some (kind, ops)})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok ops hv)]
    rfl
  · intro d f hd
    simp [s, ops_mapping, hd]
  · intro d f hd hf hfbase
    exact ops_defined _ _ _ _ _ _ _ hd hf (Or.inl hfbase)

private theorem mapping_member (ops : List (List Fn)) (st : Globals)
    (hm : ∀ d f, 1 ≤ d → st.mapping d f = lastIndex 1 (ops[d - 1]?.getD []) f)
    (d : Nat) (f : Fn) (hd : 1 ≤ d) (hf : f ∈ (ops[d - 1]?.getD [])) :
    ∃ i, st.mapping d f = some i ∧ (ops[d - 1]?.getD [])[i - 1]? = some f ∧ 1 ≤ i := by
  cases hi : lastIndex 1 (ops[d - 1]?.getD []) f with
  | none => exact False.elim ((lastIndex_none _ _ _).mp hi hf)
  | some i =>
    obtain ⟨hpos, hslot⟩ := lastIndex_sound _ _ _ _ hi
    exact ⟨i, (hm d f hd).trans hi, hslot, hpos⟩

theorem enum_lookup_inverts_proof : enum_lookup_inverts := by
  intro inBase kind p ps st h
  obtain ⟨ops, st', hmk, hm, _⟩ := make_ready inBase kind p ps st h
  refine ⟨ops, st', hmk, ?_⟩
  intro d f hd
  constructor
  · intro hf
    obtain ⟨i, hi, hs, hp⟩ := mapping_member ops st' hm d f hd hf
    exact ⟨i, by simp [lookupOp, hi]; rfl, hs, hp⟩
  · intro hf
    have hi : st'.mapping d f = none := (hm d f hd).trans ((lastIndex_none _ _ _).mpr hf)
    exact ⟨⟨_, by simp [lookupOp, hi]; rfl⟩, by simp [lookupOp, hi]; rfl⟩

private theorem op_lookup (I : Fn → List T → T) (ops : List (List Fn)) (d i : Nat)
    (f : Fn) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hs : (ops[d - 1]?.getD [])[i - 1]? = some f) :
    (opEnumOf I ops).lookup d i = some (I f) := by
  simp only [OpEnum.lookup, show ¬ (d = 0 ∨ i = 0) by omega, ↓reduceIte,
    opEnumOf, List.getElem?_map]
  cases ht : ops[d - 1]? with
  | none => simp [ht] at hs
  | some t => simpa [ht, List.getElem?_map, hs] using congrArg (Option.map I) hs

private def unaryTree (I : Fn → List T → T) (f : Fn) (i : Nat) : Tree T → Tree T
  | .const a => .const (I f [a])
  | l => .branch i [l]

private def binaryTree (I : Fn → List T → T) (f : Fn) (i : Nat) : Tree T → Tree T → Tree T
  | .const a, .const b => .const (I f [a, b])
  | l, r => .branch i [l, r]

private theorem unary_correct (I : Fn → List T → T) (ops : List (List Fn)) (st : Globals)
    (f : Fn) (i : Nat) (hdef : st.defined 1 f = true) (hm : st.mapping 1 f = some i)
    (hl : (opEnumOf I ops).lookup 1 i = some (I f)) (l : Tree T) :
    ∃ t', callUnary I st f l = .ok t' ∧ ∀ x,
      t'.denote (opEnumOf I ops) x = (do let a ← l.denote (opEnumOf I ops) x; pure (I f [a])) := by
  refine ⟨unaryTree I f i l, ?_, ?_⟩
  · cases l <;> simp [unaryTree, callUnary, hdef, lookupOp, hm] <;> rfl
  · intro x
    cases l <;> simp [unaryTree, Tree.denote, hl, List.mapM_cons, Option.bind_assoc] <;> rfl

private theorem binary_correct (I : Fn → List T → T) (ops : List (List Fn)) (st : Globals)
    (f : Fn) (i : Nat) (hdef : st.defined 2 f = true) (hm : st.mapping 2 f = some i)
    (hl : (opEnumOf I ops).lookup 2 i = some (I f)) (l r : Tree T) :
    ∃ t', callBinary I st f l r = .ok t' ∧ ∀ x,
      t'.denote (opEnumOf I ops) x =
        (do let a ← l.denote (opEnumOf I ops) x
            let b ← r.denote (opEnumOf I ops) x
            pure (I f [a, b])) := by
  refine ⟨binaryTree I f i l r, ?_, ?_⟩
  · cases l <;> cases r <;> simp [binaryTree, callBinary, hdef, lookupOp, hm] <;> rfl
  · intro x
    cases l <;> cases r <;> simp [binaryTree, Tree.denote, hl, List.mapM_cons] <;>
      first | rfl | (simp only [Option.bind_assoc]; rfl)

private theorem ns_correct (I : Fn → List T → T) (ops : List (List Fn)) (st : Globals)
    (f : Fn) (i : Nat) (hdef : st.defined 2 f = true) (hm : st.mapping 2 f = some i)
    (hl : (opEnumOf I ops).lookup 2 i = some (I f)) (l : Tree T) (b : T) :
    ∃ t', callBinaryNS I st f l b = .ok t' ∧ ∀ x,
      t'.denote (opEnumOf I ops) x = (do let a ← l.denote (opEnumOf I ops) x; pure (I f [a, b])) := by
  obtain ⟨t, ht, hd⟩ := binary_correct I ops st f i hdef hm hl l (.const b)
  refine ⟨t, ?_, ?_⟩
  · have he : callBinaryNS I st f l b = callBinary I st f l (.const b) := by
      cases l <;> simp [callBinaryNS, callBinary]
    exact he.trans ht
  · intro x; simpa [Tree.denote] using hd x

private theorem sn_correct (I : Fn → List T → T) (ops : List (List Fn)) (st : Globals)
    (f : Fn) (i : Nat) (hdef : st.defined 2 f = true) (hm : st.mapping 2 f = some i)
    (hl : (opEnumOf I ops).lookup 2 i = some (I f)) (a : T) (r : Tree T) :
    ∃ t', callBinarySN I st f a r = .ok t' ∧ ∀ x,
      t'.denote (opEnumOf I ops) x = (do let b ← r.denote (opEnumOf I ops) x; pure (I f [a, b])) := by
  obtain ⟨t, ht, hd⟩ := binary_correct I ops st f i hdef hm hl (.const a) r
  refine ⟨t, ?_, ?_⟩
  · have he : callBinarySN I st f a r = callBinary I st f (.const a) r := by
      cases r <;> simp [callBinarySN, callBinary]
    exact he.trans ht
  · intro x; simpa [Tree.denote] using hd x

theorem enum_overload_denote_proof : enum_overload_denote := by
  intro T I inBase kind p ps st h
  obtain ⟨ops, st', hmk, hm, hd⟩ := make_ready inBase kind p ps st h
  refine ⟨ops, st', hmk, ?_⟩
  intro f hfbase
  constructor
  · intro hf l
    obtain ⟨i, hi, hs, hp⟩ := mapping_member ops st' hm 1 f (by decide) hf
    exact unary_correct I ops st' f i (hd 1 f (by decide) hf hfbase) hi
      (op_lookup I ops 1 i f (by decide) hp hs) l
  · intro hf
    obtain ⟨i, hi, hs, hp⟩ := mapping_member ops st' hm 2 f (by decide) hf
    have hdef := hd 2 f (by decide) hf hfbase
    have hl := op_lookup I ops 2 i f (by decide) hp hs
    exact ⟨binary_correct I ops st' f i hdef hi hl,
      ns_correct I ops st' f i hdef hi hl, sn_correct I ops st' f i hdef hi hl⟩

theorem extend_operators_user_ops_proof : extend_operators_user_ops := by
  intro T I inBase ops st hb hv
  let s := putOps inBase false 1 ops {st with mapping := fun _ _ => none}
  refine ⟨s, extend_run _ _ _ _ _ hb (validate_ok ops hv), ?_⟩
  intro f hf l r
  have hm : ∀ d f, 1 ≤ d → s.mapping d f = lastIndex 1 (ops[d - 1]?.getD []) f := by
    intro d f hd; simp [s, ops_mapping, hd]
  obtain ⟨i, hi, hs, hp⟩ := mapping_member ops s hm 2 f (by decide) hf
  exact binary_correct I ops s f i (ops_defined _ _ _ _ _ _ _ (by decide) hf (Or.inr rfl)) hi
    (op_lookup I ops 2 i f (by decide) hp hs) l r


theorem enum_kw_shape_proof : enum_kw_shape := by
  intro inBase kind binary unary helpers emptyOld st h
  have hp : pairsToOpsTuple (1, unary.getD []) [(2, binary.getD [])] =
      .ok [unary.getD [], binary.getD []] := rfl
  cases helpers with
  | false =>
    refine ⟨st, ?_⟩
    simp [makeEnumKw, makeEnum, hp]
    rfl
  | true =>
    obtain ⟨ops, hpair, hb, hv⟩ := input_ops _ _ (h rfl)
    rw [hp] at hpair
    cases hpair
    let s := putOps inBase true 1 [unary.getD [], binary.getD []]
      (if emptyOld then {st with mapping := fun _ _ => none} else st)
    refine ⟨{s with latest := some (kind, [unary.getD [], binary.getD []])}, ?_⟩
    unfold makeEnumKw
    rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true [unary.getD [], binary.getD []] emptyOld st
               pure ([unary.getD [], binary.getD []], {s with latest := some (kind, [unary.getD [], binary.getD []])})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok _ hv)]
    rfl

theorem enum_generic_same_ops_proof : enum_generic_same_ops := by
  intro inBase p ps emptyOld st h
  obtain ⟨ops, hp, hb, hv⟩ := input_ops p ps h
  let s := putOps inBase true 1 ops (if emptyOld then {st with mapping := fun _ _ => none} else st)
  have hk (kind : EnumKind) : makeEnum inBase kind p ps true emptyOld st =
      .ok (ops, {s with latest := some (kind, ops)}) := by
    rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true ops emptyOld st
               pure (ops, {s with latest := some (kind, ops)})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok _ hv)]
    rfl
  refine ⟨ops, {s with latest := some (.operatorEnum, ops)},
    {s with latest := some (.genericOperatorEnum, ops)}, hk _, hk _, rfl, rfl, rfl, ?_⟩
  simp [makeEnum, hp]
  rfl

private theorem pair_output_subset (p : Int × List Fn) (ps : List (Int × List Fn))
    (ops : List (List Fn)) (hp : DegreesPos (p :: ps)) (h : pairsToOpsTuple p ps = .ok ops) :
    ∀ t ∈ ops, t = [] ∨ ∃ q ∈ p :: ps, t = q.2 := by
  have hs := pairs_fold_ok (p :: ps)
    (List.replicate (ps.foldl (fun m q => max m q.1) p.1).toNat []) hp
  change pairsToOpsTuple p ps = _ at hs
  rw [h] at hs
  cases hs
  intro t ht
  rcases pairs_values _ _ t ht with ha | hq
  · exact Or.inl (List.mem_replicate.mp ha).2
  · exact Or.inr hq

private theorem pair_operator_membership (p : Int × List Fn) (ps : List (Int × List Fn))
    (ops : List (List Fn)) (hp : DegreesPos (p :: ps)) (h : pairsToOpsTuple p ps = .ok ops)
    (hslot : ∀ q ∈ p :: ps, ops[q.1.toNat - 1]? = some q.2) (f : Fn) :
    (∃ q ∈ p :: ps, f ∈ q.2) ↔ (∃ t ∈ ops, f ∈ t) := by
  constructor
  · rintro ⟨q, hq, hf⟩
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp (hslot q hq)
    exact ⟨q.2, List.mem_iff_getElem.mpr ⟨q.1.toNat - 1, hi, he⟩, hf⟩
  · rintro ⟨t, ht, hf⟩
    rcases pair_output_subset p ps ops hp h t ht with he | ⟨q, hq, he⟩
    · simp [he] at hf
    · exact ⟨q, hq, he ▸ hf⟩

theorem enum_broadcast_validation_proof : enum_broadcast_validation := by
  intro inBase kind p ps emptyOld st hp hn hb
  obtain ⟨ops, hpair, _, hslot, _⟩ := enum_pairs_layout_proof p ps hp hn
  have hlen : ∀ t ∈ ops, t.length ≤ 255 := by
    intro t ht
    rcases pair_output_subset p ps ops hp hpair t ht with he | ⟨q, hq, he⟩
    · simp [he]
    · simpa [he] using hb q hq
  have hc : (∃ n, (∃ q ∈ p :: ps, Fn.bcast n ∈ q.2) ∧
      (∃ q ∈ p :: ps, Fn.plain n ∈ q.2)) ↔
      ops.any (fun t => t.any (badOp ops)) = true := by
    rw [conflict_iff]
    constructor
    · rintro ⟨n, h1, h2⟩
      exact ⟨n, (pair_operator_membership p ps ops hp hpair hslot _).mp h1,
        (pair_operator_membership p ps ops hp hpair hslot _).mp h2⟩
    · rintro ⟨n, h1, h2⟩
      exact ⟨n, (pair_operator_membership p ps ops hp hpair hslot _).mpr h1,
        (pair_operator_membership p ps ops hp hpair hslot _).mpr h2⟩
  rw [hc]
  cases hbad : ops.any (fun t => t.any (badOp ops)) with
  | true =>
    constructor
    · intro _
      refine ⟨"Usage of both broadcasted and unbroadcasted operator is ambiguous", ?_⟩
      have hv : validateBroadcasts ops = .error (.argumentError
          "Usage of both broadcasted and unbroadcasted operator is ambiguous") := by
        simp [validate_formula, hbad]
      rw [makeEnum, hpair]
      change (do let s ← extendOperators inBase true ops emptyOld st
                 pure (ops, {s with latest := some (kind, ops)})) = _
      simp [extendOperators, hv]
      rfl
    · intro _; rfl
  | false =>
    have hv : validateBroadcasts ops = .ok () := by simp [validate_formula, hbad]
    have hm : makeEnum inBase kind p ps true emptyOld st =
        .ok (ops, {putOps inBase true 1 ops
          (if emptyOld then {st with mapping := fun _ _ => none} else st)
          with latest := some (kind, ops)}) := by
      rw [makeEnum, hpair]
      change (do let s ← extendOperators inBase true ops emptyOld st
                 pure (ops, {s with latest := some (kind, ops)})) = _
      rw [extend_run _ _ _ _ _ hlen hv]
      rfl
    simp [hm]

private theorem make_preserves_defined (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st st' : Globals)
    (ops : List (List Fn)) (h : EnumInput p ps)
    (hmk : makeEnum inBase kind p ps true true st = .ok (ops, st'))
    (d : Nat) (f : Fn) (hd : st.defined d f = true) : st'.defined d f = true := by
  obtain ⟨ops0, hp, hb, hv⟩ := input_ops p ps h
  have he : makeEnum inBase kind p ps true true st =
      .ok (ops0, {putOps inBase true 1 ops0 {st with mapping := fun _ _ => none}
        with latest := some (kind, ops0)}) := by
    rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true ops0 true st
               pure (ops0, {s with latest := some (kind, ops0)})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok _ hv)]
    rfl
  rw [he] at hmk
  cases hmk
  exact ops_preserve_defined _ _ _ _ _ _ _ hd

theorem enum_nary_chain_proof : enum_nary_chain := by
  intro T I chainable inBase kind p ps st f h hchain hbase hinit
  obtain ⟨ops, st', hmk, hm, hd⟩ := make_ready inBase kind p ps st h
  refine ⟨ops, st', hmk, ?_⟩
  intro hf hnot a b c hnconst
  have hdef := make_preserves_defined inBase kind p ps st st' ops h hmk 3 f hinit
  obtain ⟨i, hi, hs, hp⟩ := mapping_member ops st' hm 2 f (by decide) hf
  have hb := hd 2 f (by decide) hf hbase
  have hl := op_lookup I ops 2 i f (by decide) hp hs
  obtain ⟨ab, hab, habden⟩ := binary_correct I ops st' f i hb hi hl a b
  obtain ⟨abc, habc, habcden⟩ := binary_correct I ops st' f i hb hi hl ab c
  have hnone : st'.mapping 3 f = none := (hm 3 f (by decide)).trans ((lastIndex_none _ _ _).mpr hnot)
  refine ⟨abc, ?_, ?_⟩
  · simp [callNary, hdef, hnconst, lookupOp, hnone, hchain]
    change (do let t ← callBinary I st' f a b; callBinary I st' f t c) = _
    rw [hab]
    exact habc
  · intro x
    rw [habcden x, habden x]
    cases ha : a.denote (opEnumOf I ops) x <;>
      cases hb : b.denote (opEnumOf I ops) x <;>
      cases hc : c.denote (opEnumOf I ops) x <;> simp <;> rfl

private theorem sample_input : EnumInput (1, [.plain 0]) [(2, [.plain 1])] := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; simp at hq; rcases hq with rfl | rfl <;> decide
  · intro q hq; simp at hq; rcases hq with rfl | rfl <;> decide
  · intro q hq n hf; simp at hq; rcases hq with rfl | rfl <;> simp at hf

example : EnumInput (1, [.plain 0]) [(2, [.plain 1])] := sample_input

example : EnumInput (1, [.plain 0]) [(2, [.plain 1])] ∧
    (fun _ : Fn => true) (.plain 1) = true := ⟨sample_input, rfl⟩

example : (∀ t ∈ ([[], [.plain 1]] : List (List Fn)), t.length ≤ 255) ∧
    (∀ n, (∃ t ∈ ([[], [.plain 1]] : List (List Fn)), Fn.bcast n ∈ t) →
      ∀ t ∈ ([[], [.plain 1]] : List (List Fn)), Fn.plain n ∉ t) := by
  constructor
  · intro t ht; simp at ht; rcases ht with rfl | rfl <;> decide
  · intro n h; simp at h

example : true = true → EnumInput (1, (some [Fn.plain 0]).getD [])
    [(2, (some [Fn.plain 1]).getD [])] := fun _ => sample_input

example : EnumInput (1, [.plain 0]) [(2, [.plain 1])] := sample_input

example : DegreesPos ((1, [.plain 0]) :: [(2, [.plain 1])]) ∧
    ([((1 : Int), [Fn.plain 0]), (2, [Fn.plain 1])].map Prod.fst).Nodup ∧
    (∀ q ∈ ([(1, [Fn.plain 0]), (2, [Fn.plain 1])] : List (Int × List Fn)), q.2.length ≤ 255) :=
  ⟨sample_input.1, by decide, sample_input.2.1⟩

private def sampleGlobals : Globals := ⟨none, fun _ _ => none, fun _ _ => true, 0⟩

example : ∃ ops st',
    EnumInput (2, [Fn.plain 0]) [] ∧
    makeEnum (fun _ => true) .operatorEnum (2, [Fn.plain 0]) [] true true sampleGlobals = .ok (ops, st') ∧
    (fun _ : Fn => true) (Fn.plain 0) = true ∧
    (fun _ : Fn => true) (Fn.plain 0) = true ∧
    sampleGlobals.defined 3 (Fn.plain 0) = true ∧
    Fn.plain 0 ∈ (ops[1]?.getD []) ∧ Fn.plain 0 ∉ (ops[2]?.getD []) ∧
    st'.defined 3 (Fn.plain 0) = true ∧
    ([Tree.feature 1, Tree.const 2, Tree.feature 3].mapM leafConst?) = (none : Option (List Nat)) := by
  let s := putOps (fun _ => true) true 1 [[], [Fn.plain 0]] sampleGlobals
  refine ⟨[[], [Fn.plain 0]], {s with latest := some (.operatorEnum, [[], [Fn.plain 0]])},
    ?_, ?_, rfl, rfl, rfl, by simp, by simp, ?_, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq; simp at hq; subst q; decide
    · intro q hq; simp at hq; subst q; decide
    · intro q hq n hf; simp at hq; subst q; simp at hf
  · rfl
  · exact ops_preserve_defined (fun _ => true) true 1 [[], [Fn.plain 0]] sampleGlobals 3 (.plain 0) rfl


private theorem lastIndex_max (n : Nat) (xs : List Fn) (f : Fn) (i : Nat)
    (hi : lastIndex n xs f = some i) :
    ∀ k, xs[k]? = some f → n + k ≤ i := by
  induction xs generalizing n i with
  | nil => simp [lastIndex] at hi
  | cons g gs ih =>
    cases hl : lastIndex (n + 1) gs f with
    | some j =>
      have he : j = i := by simpa only [lastIndex, hl, Option.orElse_some, Option.some.injEq] using hi
      subst i
      intro k hk
      cases k with
      | zero => have := (lastIndex_sound _ _ _ _ hl).1; omega
      | succ k => have := ih (n + 1) j hl k (by simpa using hk); omega
    | none =>
      by_cases hf : f = g
      · have he : n = i := by simpa only [lastIndex, hl, Option.orElse_none, ite_eq_left hf, Option.some.injEq] using hi
        subst i
        intro k hk
        cases k with
        | zero => omega
        | succ k =>
          have hs : gs[k]? = some f := by simpa using hk
          obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hs
          exact False.elim ((lastIndex_none _ _ _).mp hl
            (List.mem_iff_getElem.mpr ⟨k, hbound, hget⟩))
      · simp [lastIndex, hl, hf] at hi

theorem extend_operators_mapping_last (inBase : Fn → Bool) (skip : Bool)
    (ops : List (List Fn)) (st st' : Globals) (hb : ∀ t ∈ ops, t.length ≤ 255)
    (hv : validateBroadcasts ops = .ok ())
    (hr : extendOperators inBase skip ops true st = .ok st') :
    (∀ d f i, 1 ≤ d → (st'.mapping d f = some i ↔
      1 ≤ i ∧ (ops[d - 1]?.getD [])[i - 1]? = some f ∧
        ∀ j, 1 ≤ j → (ops[d - 1]?.getD [])[j - 1]? = some f → j ≤ i)) ∧
    (∀ d f, 1 ≤ d → (st'.mapping d f = none ↔ f ∉ (ops[d - 1]?.getD []))) ∧
    (∀ d f, st.defined d f = true → st'.defined d f = true) ∧
    (∀ d f, 1 ≤ d → f ∈ (ops[d - 1]?.getD []) →
      inBase f = true ∨ skip = false → st'.defined d f = true) := by
  rw [extend_run _ _ _ _ _ hb hv] at hr
  simp only [↓reduceIte] at hr
  cases hr
  have hm : ∀ d f, 1 ≤ d →
      (putOps inBase skip 1 ops {st with mapping := fun _ _ => none}).mapping d f =
        lastIndex 1 (ops[d - 1]?.getD []) f := by
    intro d f hd; simp [ops_mapping, hd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d f i hd
    rw [hm d f hd]
    constructor
    · intro hi
      obtain ⟨hp, hs⟩ := lastIndex_sound _ _ _ _ hi
      refine ⟨hp, hs, ?_⟩
      intro j hj hget
      have hmax := lastIndex_max _ _ _ _ hi (j - 1) hget
      omega
    · rintro ⟨hp, hs, hmax⟩
      have hf : f ∈ (ops[d - 1]?.getD []) := by
        obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hs
        exact List.mem_iff_getElem.mpr ⟨i - 1, hbound, hget⟩
      cases hlast : lastIndex 1 (ops[d - 1]?.getD []) f with
      | none => exact False.elim ((lastIndex_none _ _ _).mp hlast hf)
      | some j =>
        obtain ⟨hjp, hjs⟩ := lastIndex_sound _ _ _ _ hlast
        have hji := hmax j hjp hjs
        have hij := lastIndex_max _ _ _ _ hlast (i - 1) hs
        have he : j = i := by omega
        simp [he]
  · intro d f hd; rw [hm d f hd]; exact lastIndex_none _ _ _
  · intro d f hdef; exact ops_preserve_defined _ _ _ _ _ _ _ hdef
  · intro d f hd hf hbase; exact ops_defined _ _ _ _ _ _ _ hd hf hbase

theorem extend_operators_success_iff (inBase : Fn → Bool) (skip : Bool)
    (ops : List (List Fn)) (emptyOld : Bool) (st : Globals)
    (hb : ∀ t ∈ ops, t.length ≤ 255) :
    (∃ st', extendOperators inBase skip ops emptyOld st = .ok st') ↔
      validateBroadcasts ops = .ok () := by
  constructor
  · rintro ⟨st', hr⟩
    cases hv : validateBroadcasts ops with
    | error e =>
      have he : extendOperators inBase skip ops emptyOld st = .error e := by
        simp [extendOperators, hv]; rfl
      rw [he] at hr
      cases hr
    | ok u => cases u; rfl
  · intro hv; exact ⟨_, extend_run _ _ _ _ _ hb hv⟩


theorem make_enum_pairs_tuple (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (helpers emptyOld : Bool)
    (st st' : Globals) (ops : List (List Fn))
    (h : makeEnum inBase kind p ps helpers emptyOld st = .ok (ops, st')) :
    pairsToOpsTuple p ps = .ok ops := by
  cases hp : pairsToOpsTuple p ps with
  | error e =>
    have he : makeEnum inBase kind p ps helpers emptyOld st = .error e := by
      rw [makeEnum, hp]; rfl
    rw [he] at h
    cases h
  | ok xs =>
    cases helpers with
    | false =>
      have he : makeEnum inBase kind p ps false emptyOld st = .ok (xs, st) := by
        rw [makeEnum, hp]; rfl
      rw [he] at h
      cases h
      rfl
    | true =>
      cases hs : extendOperators inBase true xs emptyOld st with
      | error e =>
        have he : makeEnum inBase kind p ps true emptyOld st = .error e := by
          rw [makeEnum, hp]
          change (do let s ← extendOperators inBase true xs emptyOld st
                     pure (xs, {s with latest := some (kind, xs)})) = _
          rw [hs]; rfl
        rw [he] at h
        cases h
      | ok s =>
        have he : makeEnum inBase kind p ps true emptyOld st =
            .ok (xs, {s with latest := some (kind, xs)}) := by
          rw [makeEnum, hp]
          change (do let s ← extendOperators inBase true xs emptyOld st
                     pure (xs, {s with latest := some (kind, xs)})) = _
          rw [hs]; rfl
        rw [he] at h
        cases h
        rfl

example : ((extendOperators (fun _ => true) true [[], [Fn.plain 0, Fn.plain 1, Fn.plain 0]]
    true sampleGlobals).map (fun st => st.mapping 2 (.plain 0))).toOption = some (some 3) := by decide


theorem enum_overload_latest_enum_cleared_proof : enum_overload_latest_enum_cleared := by
  intro T I inBase kind p ps st h
  obtain ⟨ops, st', hmk, hm, _⟩ := make_ready inBase kind p ps st h
  refine ⟨ops, st', hmk, ?_⟩
  intro f l r
  cases hdef : st'.defined 2 f with
  | false =>
    exact Or.inl ⟨.methodError "no method", by simp [callBinary, hdef]; rfl⟩
  | true =>
    cases hi : st'.mapping 2 f with
    | some i =>
      have hlast : lastIndex 1 (ops[1]?.getD []) f = some i :=
        (hm 2 f (by decide)).symm.trans hi
      obtain ⟨hp, hs⟩ := lastIndex_sound _ _ _ _ hlast
      exact Or.inr (binary_correct I ops st' f i hdef hi
        (op_lookup I ops 2 i f (by decide) hp hs) l r)
    | none =>
      cases l with
      | const a =>
        cases r with
        | const b =>
          exact Or.inr ⟨.const (I f [a, b]), by simp [callBinary, hdef]; rfl,
            by intro x; simp [Tree.denote]⟩
        | feature k =>
          exact Or.inl ⟨.errorException "Convenience constructor for operator is out-of-date",
            by simp [callBinary, hdef, lookupOp, hi]; rfl⟩
        | branch op cs =>
          exact Or.inl ⟨.errorException "Convenience constructor for operator is out-of-date",
            by simp [callBinary, hdef, lookupOp, hi]; rfl⟩
      | feature k =>
        cases r <;> exact Or.inl ⟨.errorException "Convenience constructor for operator is out-of-date",
          by simp [callBinary, hdef, lookupOp, hi]; rfl⟩
      | branch op cs =>
        cases r <;> exact Or.inl ⟨.errorException "Convenience constructor for operator is out-of-date",
          by simp [callBinary, hdef, lookupOp, hi]; rfl⟩

example : EnumInput (1, [.plain 0]) [(2, [.plain 1])] := sample_input

private theorem binary_success_shape (I : Fn → List T → T) (st : Globals)
    (f : Fn) (l r t : Tree T) (hc : callBinary I st f l r = .ok t) :
    (∃ a b, l = .const a ∧ r = .const b ∧ t = .const (I f [a, b])) ∨
      ∃ i, st.mapping 2 f = some i ∧ t = .branch i [l, r] := by
  classical
  cases hdef : st.defined 2 f with
  | false =>
    have he : callBinary I st f l r = .error (.methodError "no method") := by
      simp [callBinary, hdef]; rfl
    rw [he] at hc
    cases hc
  | true =>
    by_cases hconst : ∃ a b, l = .const a ∧ r = .const b
    · obtain ⟨a, b, rfl, rfl⟩ := hconst
      have he : callBinary I st f (.const a) (.const b) = .ok (.const (I f [a, b])) := by
        simp [callBinary, hdef]; rfl
      rw [he] at hc
      cases hc
      exact Or.inl ⟨a, b, rfl, rfl, rfl⟩
    · have he : callBinary I st f l r =
          (do let i ← lookupOp st f 2 false; pure (.branch i [l, r])) := by
        cases l <;> cases r <;>
          first | exact False.elim (hconst ⟨_, _, rfl, rfl⟩) | simp [callBinary, hdef]
      rw [he] at hc
      cases hm : st.mapping 2 f with
      | none =>
        have hl : lookupOp st f 2 false = .error (.errorException "Convenience constructor for operator is out-of-date") := by
          simp [lookupOp, hm]; rfl
        rw [hl] at hc
        change (Except.error (.errorException "Convenience constructor for operator is out-of-date") : Jl (Tree T)) = .ok t at hc
        cases hc
      | some i =>
        have hl : lookupOp st f 2 false = .ok i := by simp [lookupOp, hm]; rfl
        rw [hl] at hc
        change (Except.ok (.branch i [l, r]) : Jl (Tree T)) = .ok t at hc
        cases hc
        exact Or.inr ⟨i, rfl, rfl⟩

theorem enum_keep_old_mappings_proof : enum_keep_old_mappings := by
  intro T I inBase kind p ps st h
  obtain ⟨ops, hp, hb, hv⟩ := input_ops p ps h
  let s := putOps inBase true 1 ops st
  let st' := {s with latest := some (kind, ops)}
  have hm : ∀ d f, 1 ≤ d → st'.mapping d f =
      (lastIndex 1 (ops[d - 1]?.getD []) f).orElse (fun _ => st.mapping d f) := by
    intro d f hd
    simp [st', s, ops_mapping, hd]
  have hmember : ∀ d f, 1 ≤ d → f ∈ (ops[d - 1]?.getD []) →
      ∃ i, st'.mapping d f = some i ∧ 1 ≤ i ∧ (ops[d - 1]?.getD [])[i - 1]? = some f := by
    intro d f hd hf
    cases hi : lastIndex 1 (ops[d - 1]?.getD []) f with
    | none => exact False.elim ((lastIndex_none _ _ _).mp hi hf)
    | some i =>
      obtain ⟨hpos, hslot⟩ := lastIndex_sound _ _ _ _ hi
      refine ⟨i, ?_, hpos, hslot⟩
      rw [hm d f hd, hi]
      rfl
  refine ⟨ops, st', ?_, ?_, hmember, binary_success_shape I st', ?_⟩
  · rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true ops false st
               pure (ops, {s with latest := some (kind, ops)})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok _ hv)]
    rfl
  · intro d f hf hd
    rw [hm d f hd, (lastIndex_none _ _ _).mpr hf]
    rfl
  · intro f hf l r
    cases hdef : st'.defined 2 f with
    | false => exact Or.inl ⟨.methodError "no method", by simp [callBinary, hdef]; rfl⟩
    | true =>
      obtain ⟨i, hi, hpos, hslot⟩ := hmember 2 f (by decide) hf
      exact Or.inr (binary_correct I ops st' f i hdef hi
        (op_lookup I ops 2 i f (by decide) hpos hslot) l r)

private def priorGlobals : Globals :=
  ⟨none, fun d f => if d = 2 ∧ f = Fn.plain 7 then some 9 else none, fun _ _ => true, 0⟩

example : ∃ ops st',
    EnumInput (2, [Fn.plain 0]) [] ∧
    makeEnum (fun _ => true) .operatorEnum (2, [Fn.plain 0]) [] true false priorGlobals = .ok (ops, st') ∧
    st'.mapping 2 (Fn.plain 7) = some 9 ∧ st'.mapping 2 (Fn.plain 0) = some 1 := by
  let s := putOps (fun _ => true) true 1 [[], [Fn.plain 0]] priorGlobals
  refine ⟨[[], [Fn.plain 0]], {s with latest := some (.operatorEnum, [[], [Fn.plain 0]])},
    ?_, rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; simp at hq; subst q; decide
  · intro q hq; simp at hq; subst q; decide
  · intro q hq n hf; simp at hq; subst q; simp at hf


theorem makeEnum_ok_layout (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (helpers emptyOld : Bool) (st : Globals)
    (h : EnumInput p ps) (hn : ((p :: ps).map Prod.fst).Nodup) :
    ∃ ops st', makeEnum inBase kind p ps helpers emptyOld st = .ok (ops, st') ∧
      ∀ q ∈ p :: ps, ops[q.1.toNat - 1]? = some q.2 := by
  obtain ⟨ops, hp, _, hslot, _⟩ := enum_pairs_layout_proof p ps h.1 hn
  cases helpers with
  | false =>
    refine ⟨ops, st, ?_, hslot⟩
    rw [makeEnum, hp]
    rfl
  | true =>
    obtain ⟨ops0, hp0, hb, hv⟩ := input_ops p ps h
    rw [hp] at hp0
    cases hp0
    let s := putOps inBase true 1 ops (if emptyOld then {st with mapping := fun _ _ => none} else st)
    refine ⟨ops, {s with latest := some (kind, ops)}, ?_, hslot⟩
    rw [makeEnum, hp]
    change (do let s ← extendOperators inBase true ops emptyOld st
               pure (ops, {s with latest := some (kind, ops)})) = _
    rw [extend_run _ _ _ _ _ hb (validate_ok _ hv)]
    rfl

end DynExpr.Simplify
