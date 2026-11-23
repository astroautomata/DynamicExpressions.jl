import DynExpr.Deriv.HeapGrad

/-! Object-identity mirror of `eval_diff_tree_array`: leaves allocate value and
derivative vectors, fused kernels overwrite the first child's vectors in place,
and the input matrix is a heap object. Each sample of the result is proven
equal to the scalar mirror `diffScalar` (and so to `Tree.denoteDeriv`),
src/EvaluateDerivative.jl:40-172. -/

namespace DynExpr.Deriv

@[simp] private theorem dBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem dPure (a : α) : (pure a : Jl α) = .ok a := rfl

/-- Reading a child's `x_cumulator_i` and `dx_cumulator_i`,
src/EvaluateDerivative.jl:143-144. -/
def readPairVec (h : Heap Obj) (r : HRes) : Jl (List JF × List JF) := do
  let a ← h.read r.va
  let d ← h.read r.ga
  match a, d with
  | .vec a, .vec d => pure (a, d)
  | _, _ => .error (.methodError "cumulator vectors expected")

/-- The fused loop's values: `op` and its supplied partials at every sample,
src/EvaluateDerivative.jl:112-120. -/
def diffColumns (op : DOp) (ns : Nat) (ps : List (List JF × List JF)) : List (JF × JF) :=
  (List.range ns).map fun j => diffKernel op (ps.map fun p => (p.1[j]!, p.2[j]!))

/-- In-place writes into the first child's vectors, src/EvaluateDerivative.jl:118-121. -/
def diffWrite (out : List (JF × JF)) (rs : List HRes) (h : Heap Obj) : Jl (HRes × Heap Obj) :=
  match rs with
  | [] => .error (.undefinedBehavior "no cumulator")
  | r1 :: _ => do
      let h2 ← h.write r1.va (.vec (out.map Prod.fst))
      let h3 ← h2.write r1.ga (.vec (out.map Prod.snd))
      pure (⟨r1.va, r1.ga, true⟩, h3)

mutual
/-- Heap mirror of `_eval_diff_tree_array`, `diff_deg0_eval` and
`dispatch_diff_degn_eval`, src/EvaluateDerivative.jl:72-172. Leaves use
`deg0_eval` with a fresh `EvalContext()` (`fill` or the copy `X[feature, :]`)
and `fill_similar`. -/
def diffTreeH (o : DEnum) (xa dir : Nat) : Tree JF → Heap Obj → Jl (HRes × Heap Obj)
  | .const v, h => do
      let X ← readInput h xa
      pure (allocPair (.vec (List.replicate X.ncols v)) (.vec (List.replicate X.ncols zero)) true h)
  | .feature k, h => do
      let X ← readInput h xa
      let vals ← X.row k
      pure (allocPair (.vec vals.toList)
        (.vec (List.replicate X.ncols (if k = dir then one else zero))) true h)
  | .branch idx cs, h => do
      let (res, h1) ← diffListH o xa dir cs h
      match res with
      | .inl e => pure (e, h1)
      | .inr rs =>
          match o.lookup cs.length idx with
          | none => .error (.undefinedBehavior "generated operator dispatch has no matching arm")
          | some op => do
              let X ← readInput h1 xa
              let ps ← rs.mapM (readPairVec h1)
              diffWrite (diffColumns op X.ncols ps) rs h1

/-- The children loop with `!result_i.ok && return result_i`,
src/EvaluateDerivative.jl:136-142. -/
def diffListH (o : DEnum) (xa dir : Nat) :
    List (Tree JF) → Heap Obj → Jl ((HRes ⊕ List HRes) × Heap Obj)
  | [], h => pure (.inr [], h)
  | c :: cs, h => do
      let (r, h1) ← diffTreeH o xa dir c h
      if !r.complete then pure (.inl r, h1)
      else do
        let (rest, h2) ← diffListH o xa dir cs h1
        match rest with
        | .inl e => pure (.inl e, h2)
        | .inr rs => pure (.inr (r :: rs), h2)
end

/-- Sample `j` (zero-based) as read by `eval_diff_tree_array`. -/
def diffSample (X : JMat JF) (j : Nat) : Nat → Option JF := fun k => (X.get? k (j + 1)).toOption

theorem get?_row (X : JMat JF) (k j : Nat) (vals : JVec JF) (hrow : X.row k = .ok vals)
    (hj : j < X.ncols) : X.get? k (j + 1) = .ok vals.toList[j]! := by
  have hk : 1 ≤ k ∧ k ≤ X.nrows := by
    unfold JMat.row at hrow
    split at hrow
    · assumption
    · cases hrow
  have hdef : X.get? k (j + 1) = (if hb : (1 ≤ k ∧ k ≤ X.nrows) ∧ (1 ≤ j + 1 ∧ j + 1 ≤ X.ncols) then
      Except.ok (X.data[X.nrows * (j + 1 - 1) + (k - 1)]'(offset_bound X k (j + 1) hb))
    else Except.error .boundsError) := rfl
  rw [hdef]
  split
  · unfold JMat.row at hrow
    split at hrow
    · cases hrow
      simp [Array.toList_ofFn, hj]
    · contradiction
  · rename_i hn
    exact absurd ⟨hk, by omega, by omega⟩ hn

/-- A child's vectors read back with one value and derivative per sample,
matching the scalar mirror at every sample. -/
def DReads (h : Heap Obj) (o : DEnum) (X : JMat JF) (dir : Nat) :
    List HRes → List (Tree JF) → List (List JF × List JF) → Prop
  | [], [], [] => True
  | r :: rs, c :: cs, p :: ps => h.read r.va = .ok (.vec p.1) ∧ h.read r.ga = .ok (.vec p.2) ∧
      p.1.length = X.ncols ∧ p.2.length = X.ncols ∧
      (∀ j < X.ncols, diffScalar o (diffSample X j) dir c = some (p.1[j]!, p.2[j]!)) ∧
      DReads h o X dir rs cs ps
  | _, _, _ => False

/-- One call's result: two fresh distinct vectors equal to the scalar mirror
per sample, with every pre-existing object unchanged. -/
def DAgree (o : DEnum) (X : JMat JF) (dir : Nat) (t : Tree JF) (h h' : Heap Obj) (res : HRes) :
    Prop :=
  ∃ vals ders, h'.read res.va = .ok (.vec vals) ∧ h'.read res.ga = .ok (.vec ders) ∧
    vals.length = X.ncols ∧ ders.length = X.ncols ∧
    (∀ j < X.ncols, diffScalar o (diffSample X j) dir t = some (vals[j]!, ders[j]!)) ∧
    res.complete = true ∧ res.va ≠ res.ga ∧ h.next ≤ res.va ∧ h.next ≤ res.ga ∧
    res.va < h'.next ∧ res.ga < h'.next ∧ h.next ≤ h'.next ∧
    ∀ p, p < h.next → h'.read p = h.read p

theorem dreads_keep (h1 h2 : Heap Obj) (o : DEnum) (X : JMat JF) (dir : Nat) :
    ∀ (ress : List HRes) (cs : List (Tree JF)) (ps : List (List JF × List JF)) (lo hi : Nat),
      DReads h1 o X dir ress cs ps → Sep lo ress hi → (∀ p, p < hi → h2.read p = h1.read p) →
      DReads h2 o X dir ress cs ps := by
  intro ress
  induction ress with
  | nil => intro cs ps lo hi hr _ _; cases cs <;> cases ps <;> simp_all [DReads]
  | cons r ress ih =>
    intro cs ps lo hi hr hs hk
    cases cs with
    | nil => cases ps <;> simp [DReads] at hr
    | cons c cs =>
      cases ps with
      | nil => simp [DReads] at hr
      | cons p ps =>
        obtain ⟨hv, hg, hl1, hl2, hj, hrest⟩ := hr
        have hb := (sep_bounds _ lo hi hs).2 r (by simp)
        obtain ⟨mid, _, _, _, _, _, hs'⟩ := hs
        exact ⟨by rw [hk _ hb.2.2.1, hv], by rw [hk _ hb.2.2.2, hg], hl1, hl2, hj,
          ih cs ps mid hi hrest hs' hk⟩

theorem dreads_mapM (h : Heap Obj) (o : DEnum) (X : JMat JF) (dir : Nat) :
    ∀ (ress : List HRes) (cs : List (Tree JF)) (ps : List (List JF × List JF)),
      DReads h o X dir ress cs ps → ress.mapM (readPairVec h) = .ok ps := by
  intro ress
  induction ress with
  | nil => intro cs ps hr; cases cs <;> cases ps <;> simp_all [DReads]
  | cons r ress ih =>
    intro cs ps hr
    cases cs with
    | nil => cases ps <;> simp [DReads] at hr
    | cons c cs =>
      cases ps with
      | nil => simp [DReads] at hr
      | cons p ps =>
        obtain ⟨hv, hg, _, _, _, hrest⟩ := hr
        simp only [List.mapM_cons, readPairVec, hv, hg, dBind, ih cs ps hrest, dPure]

theorem dreads_scalar (h : Heap Obj) (o : DEnum) (X : JMat JF) (dir : Nat) (j : Nat)
    (hj : j < X.ncols) : ∀ (ress : List HRes) (cs : List (Tree JF)) (ps : List (List JF × List JF)),
      DReads h o X dir ress cs ps →
      cs.mapM (diffScalar o (diffSample X j) dir) = some (ps.map fun p => (p.1[j]!, p.2[j]!)) := by
  intro ress
  induction ress with
  | nil => intro cs ps hr; cases cs <;> cases ps <;> simp_all [DReads]
  | cons r ress ih =>
    intro cs ps hr
    cases cs with
    | nil => cases ps <;> simp [DReads] at hr
    | cons c cs =>
      cases ps with
      | nil => simp [DReads] at hr
      | cons p ps =>
        obtain ⟨_, _, _, _, hd, hrest⟩ := hr
        simp [List.mapM_cons, hd j hj, ih cs ps hrest]

theorem dreads_length (h : Heap Obj) (o : DEnum) (X : JMat JF) (dir : Nat) :
    ∀ (ress : List HRes) (cs : List (Tree JF)) (ps : List (List JF × List JF)),
      DReads h o X dir ress cs ps → ress.length = cs.length := by
  intro ress
  induction ress with
  | nil => intro cs ps hr; cases cs <;> cases ps <;> simp_all [DReads]
  | cons r ress ih =>
    intro cs ps hr
    cases cs with
    | nil => cases ps <;> simp [DReads] at hr
    | cons c cs =>
      cases ps with
      | nil => simp [DReads] at hr
      | cons p ps => simp [ih cs ps hr.2.2.2.2.2]

theorem diffListH_agree (o : DEnum) (X : JMat JF) (xa dir D : Nat) :
    ∀ (cs : List (Tree JF)),
      (∀ c ∈ cs, ∀ h, c.WF D o.nops X.nrows → h.read xa = .ok (.input X) →
        ∃ res h', diffTreeH o xa dir c h = .ok (res, h') ∧ DAgree o X dir c h h' res) →
      ∀ h, (∀ c ∈ cs, c.WF D o.nops X.nrows) → h.read xa = .ok (.input X) →
        ∃ ress ps h', diffListH o xa dir cs h = .ok (.inr ress, h') ∧
          DReads h' o X dir ress cs ps ∧ Sep h.next ress h'.next ∧
          ∀ p, p < h.next → h'.read p = h.read p := by
  intro cs
  induction cs with
  | nil =>
    intro _ h _ _
    exact ⟨[], [], h, rfl, trivial, Nat.le_refl _, fun _ _ => rfl⟩
  | cons c cs ih =>
    intro ihc h hwf hx
    obtain ⟨res1, h1, hh1, vals, ders, hv, hd, hl1, hl2, hj, hc, hne, hlv, hld, hhv, hhd, hg1, hk1⟩ :=
      ihc c (by simp) h (hwf c (by simp)) hx
    have hx1 : h1.read xa = .ok (.input X) := by rw [hk1 xa (read_lt h xa _ hx), hx]
    obtain ⟨ress, ps, h2, hh2, hreads, hsep, hk2⟩ :=
      ih (fun c' hc' => ihc c' (by simp [hc'])) h1 (fun c' hc' => hwf c' (by simp [hc'])) hx1
    refine ⟨res1 :: ress, (vals, ders) :: ps, h2, ?_, ?_, ?_, ?_⟩
    · simp only [diffListH, hh1, dBind, hc, Bool.not_true, Bool.false_eq_true, ite_false, hh2]
      rfl
    · exact ⟨by rw [hk2 _ hhv, hv], by rw [hk2 _ hhd, hd], hl1, hl2, hj, hreads⟩
    · exact ⟨h1.next, hlv, hld, hhv, hhd, hne, hsep⟩
    · intro p hp
      rw [hk2 p (by omega), hk1 p hp]

theorem leafD (o : DEnum) (X : JMat JF) (dir : Nat) (t : Tree JF) (h : Heap Obj)
    (vals ders : List JF) (hl1 : vals.length = X.ncols) (hl2 : ders.length = X.ncols)
    (hj : ∀ j < X.ncols, diffScalar o (diffSample X j) dir t = some (vals[j]!, ders[j]!)) :
    DAgree o X dir t h (allocPair (.vec vals) (.vec ders) true h).2
      (allocPair (.vec vals) (.vec ders) true h).1 :=
  ⟨vals, ders, by rw [allocPair_va, allocPair_read_va], by rw [allocPair_ga, allocPair_read_ga],
    hl1, hl2, hj, rfl, by rw [allocPair_va, allocPair_ga]; omega, by rw [allocPair_va]; omega,
    by rw [allocPair_ga]; omega, by rw [allocPair_va, allocPair_next]; omega,
    by rw [allocPair_ga, allocPair_next]; omega, by rw [allocPair_next]; omega,
    fun p hp => allocPair_keep _ _ _ h p hp⟩

theorem diffTreeH_agree (o : DEnum) (X : JMat JF) (xa dir D : Nat) :
    ∀ (t : Tree JF) (h : Heap Obj), t.WF D o.nops X.nrows → h.read xa = .ok (.input X) →
      ∃ res h', diffTreeH o xa dir t h = .ok (res, h') ∧ DAgree o X dir t h h' res := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro h _ hx
    refine ⟨_, _, by simp only [diffTreeH, readInput_of h xa X hx, dBind, dPure],
      leafD o X dir _ h (List.replicate X.ncols v) (List.replicate X.ncols zero) (by simp) (by simp) ?_⟩
    intro j hj
    simp [diffScalar, hj]
  | hf k =>
    intro h hwf hx
    simp only [Tree.WF] at hwf
    obtain ⟨vals, hrow, hsize⟩ := X.row_exists k hwf.1 hwf.2.1
    refine ⟨_, _, by simp only [diffTreeH, readInput_of h xa X hx, dBind, hrow, dPure],
      leafD o X dir _ h vals.toList (List.replicate X.ncols (if k = dir then one else zero))
        (by simp [hsize]) (by simp) ?_⟩
    intro j hj
    simp [diffScalar, diffSample, get?_row X k j vals hrow hj, List.getElem!_eq_getElem?_getD, hj,
      Except.toOption]
  | hb idx cs ih =>
    intro h hwf hx
    simp only [Tree.WF] at hwf
    obtain ⟨ress, ps, h1, hh1, hreads, hsep, hk1⟩ :=
      diffListH_agree o X xa dir D cs (fun c hc h hw hx => ih c hc h hw hx) h hwf.2.2 hx
    obtain ⟨op, hop⟩ := lookup_exists o cs.length idx hwf.1.1 hwf.2.1.1 hwf.2.1.2.1
    have hx1 : h1.read xa = .ok (.input X) := by rw [hk1 xa (read_lt h xa _ hx), hx]
    have hrl := dreads_length h1 o X dir ress cs ps hreads
    obtain ⟨res1, rest, rfl⟩ : ∃ res1 rest, ress = res1 :: rest := by
      cases ress with
      | nil => simp at hrl; omega
      | cons a b => exact ⟨a, b, rfl⟩
    obtain ⟨mid, hlov, hlog, hhiv, hhig, hne, hsep'⟩ := hsep
    have hhi := (sep_bounds rest mid h1.next hsep').1
    cases cs with
    | nil => simp at hrl
    | cons c cs' =>
    cases ps with
    | nil => simp [DReads] at hreads
    | cons p1 ps' =>
    obtain ⟨hv1, hg1, _, _, _, _⟩ := id hreads
    obtain ⟨h2, hw2⟩ := write_exists h1 res1.va
      (.vec ((diffColumns op X.ncols (p1 :: ps')).map Prod.fst)) _ hv1
    have hg2 : h2.read res1.ga = .ok (.vec p1.2) := by
      rw [Heap.read_write_other _ _ res1.va res1.ga _ hw2 (Ne.symm hne), hg1]
    obtain ⟨h3, hw3⟩ := write_exists h2 res1.ga
      (.vec ((diffColumns op X.ncols (p1 :: ps')).map Prod.snd)) _ hg2
    have hn2 := write_next _ _ _ _ hw2
    have hn3 := write_next _ _ _ _ hw3
    refine ⟨⟨res1.va, res1.ga, true⟩, h3, ?_, (diffColumns op X.ncols (p1 :: ps')).map Prod.fst,
      (diffColumns op X.ncols (p1 :: ps')).map Prod.snd, ?_, ?_,
      by simp [diffColumns], by simp [diffColumns], ?_, rfl, hne, hlov, hlog,
      by dsimp only; omega, by dsimp only; omega, by omega, ?_⟩
    · simp only [diffTreeH, hh1, dBind, hop, readInput_of h1 xa X hx1,
        dreads_mapM h1 o X dir _ _ _ hreads, diffWrite, hw2, hw3, dPure]
    · rw [Heap.read_write_other _ _ _ _ _ hw3 hne, Heap.read_write_same _ _ _ _ hw2]
    · exact Heap.read_write_same _ _ _ _ hw3
    · intro j hj
      have hms := dreads_scalar h1 o X dir j hj _ _ _ hreads
      simp only [diffScalar, hms, hop, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      simp only [diffColumns, List.map_map, bang_eq_getD]
      rw [getD_map_range _ _ _ _ hj, getD_map_range _ _ _ _ hj]
      rfl
    · intro p hp
      rw [Heap.read_write_other _ _ res1.ga p _ hw3 (Nat.ne_of_lt (show p < res1.ga by omega)),
        Heap.read_write_other _ _ res1.va p _ hw2 (Nat.ne_of_lt (show p < res1.va by omega)),
        hk1 p hp]

private theorem mapM_some_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- For every well-formed tree, operator enum, direction and input matrix
object `X` (Array, view or transpose: a view shares `X`'s object),
`eval_diff_tree_array` returns its value and derivative vectors as two distinct
arrays allocated during the call, holding exactly the pure mirror's results
(the chain rule of deriv-chain-rule at every sample) with the flag
`is_valid_array(x) && is_valid_array(dx)` of those arrays. Neither aliases `X`, a
view of `X`, a constant, or any array that existed before the call, and the
call leaves every pre-existing object, including `X`, unchanged, even though
fused kernels overwrite child vectors in place. -/
def diffOutputsFresh : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (dir : Nat) (t : Tree JF) (D : Nat) (h : Heap Obj) (xa : Nat),
    t.WF D o.nops X.nrows → h.read xa = .ok (.input X) →
    ∃ res h' vals ders, diffTreeH o xa dir t h = .ok (res, h') ∧
      eval_diff_tree_array o X dir t =
        some (vals.zip ders, Eval.isValidArray vals.toArray && Eval.isValidArray ders.toArray) ∧
      h'.read res.va = .ok (.vec vals) ∧ h'.read res.ga = .ok (.vec ders) ∧
      res.complete = true ∧ res.va ≠ res.ga ∧ h.next ≤ res.va ∧ h.next ≤ res.ga ∧
      ∀ p, p < h.next → h'.read p = h.read p

theorem diffOutputsFresh_proof : diffOutputsFresh := by
  intro o X dir t D h xa hwf hx
  obtain ⟨res, h', hh, vals, ders, hv, hd, hl1, hl2, hj, hc, hne, hlv, hld, _, _, _, hk⟩ :=
    diffTreeH_agree o X xa dir D t h hwf hx
  refine ⟨res, h', vals, ders, hh, ?_, hv, hd, hc, hne, hlv, hld, hk⟩
  have hz : (List.range X.ncols).map (fun j => (vals[j]!, ders[j]!)) = vals.zip ders := by
    apply List.ext_getElem
    · simp [hl1, hl2]
    · intro n h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp [List.getElem!_eq_getElem?_getD, hl1, hl2, h1]
  unfold eval_diff_tree_array
  change Option.map _ ((List.range X.ncols).mapM fun j => diffScalar o (diffSample X j) dir t) = _
  rw [mapM_some_of _ (fun j => (vals[j]!, ders[j]!)) (List.range X.ncols)
    (fun j hjm => hj j (List.mem_range.1 hjm)), hz]
  simp [List.map_fst_zip, List.map_snd_zip, hl1, hl2]

end DynExpr.Deriv
