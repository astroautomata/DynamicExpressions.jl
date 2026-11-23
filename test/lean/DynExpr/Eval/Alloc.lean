import DynExpr.Eval.Lemmas

/-!
Buffer allocation, loop and canonical-output lemmas for the evaluator proofs.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- The buffer can serve `k` more slot requests of arrays of length `n`. -/
def Good (n k : Nat) : Buf T → Prop
  | .none => True
  | .mat A i => n ≤ A.ncols ∧ i + k ≤ A.nrows
  | .vec _ _ => True

theorem Good.mono {n k k' : Nat} {b : Buf T} (h : Good n k b) (hk : k' ≤ k) : Good n k' b := by
  cases b with
  | none => trivial
  | mat A i => exact ⟨h.1, by have := h.2; omega⟩
  | vec _ _ => trivial

theorem getArray_good {n k : Nat} {b : Buf T} (h : Good n (k + 1) b) :
    ∃ a b', getArray b n = .ok (a, b') ∧ a.size = n ∧ Good n k b' := by
  cases b with
  | none => exact ⟨_, .none, rfl, by simp [JVec.fill], trivial⟩
  | mat A i =>
    obtain ⟨hc, hr⟩ := h
    obtain ⟨r, hrow, hs⟩ := A.row_exists (i + 1) (by omega) (by omega)
    exact ⟨r.extract 0 n, .mat A (i + 1), by simp [getArray, hrow, hc],
      by simp [hs]; omega, hc, by omega⟩
  | vec arrs i =>
    simp only [getArray]
    split
    · split
      · exact ⟨_, _, rfl, by assumption, trivial⟩
      · exact ⟨_, _, rfl, by simp [JVec.fill], trivial⟩
    · exact ⟨_, _, rfl, by simp [JVec.fill], trivial⟩

theorem getFilled_good {n k : Nat} {b : Buf T} (v : T) (h : Good n (k + 1) b) :
    ∃ b', getFilled b v n = .ok (JVec.fill n v, b') ∧ Good n k b' := by
  cases b with
  | none => exact ⟨.none, rfl, trivial⟩
  | mat A i =>
    obtain ⟨a, b', ha, hs, hg⟩ := getArray_good (b := .mat A i) (n := n) (k := k) h
    refine ⟨b', ?_, hg⟩
    simp [getFilled, ha, hs]
  | vec arrs i =>
    obtain ⟨a, b', ha, hs, hg⟩ := getArray_good (b := .vec arrs i) (n := n) (k := k) trivial
    refine ⟨b', ?_, hg⟩
    simp [getFilled, ha, hs]

theorem rowInb_size (X : JMat T) (f : Nat) (r : JVec T) (h : rowInb X f = .ok r) :
    r.size = X.ncols := by
  unfold rowInb at h
  split at h
  · exact X.row_length f r h
  · cases h

theorem getFeature_good {k : Nat} {b : Buf T} (X : JMat T) (f : Nat) (r : JVec T)
    (hr : rowInb X f = .ok r) (h : Good X.ncols (k + 1) b) :
    ∃ b', getFeature b X f = .ok (r, b') ∧ Good X.ncols k b' := by
  have hs := rowInb_size X f r hr
  cases b with
  | none => exact ⟨.none, by simp [getFeature, hr], trivial⟩
  | mat A i =>
    obtain ⟨a, b', ha, _, hg⟩ := getArray_good (b := .mat A i) (n := X.ncols) (k := k) h
    exact ⟨b', by simp [getFeature, ha, hr], hg⟩
  | vec arrs i =>
    obtain ⟨a, b', ha, _, hg⟩ := getArray_good (b := .vec arrs i) (n := X.ncols) (k := k) trivial
    exact ⟨b', by simp [getFeature, ha, hr], hg⟩

/-- `checkbounds` passes for an in-range feature. -/
@[simp] theorem chk_ok (X : JMat T) (f : Nat) (h1 : 1 ≤ f) (h2 : f ≤ X.nrows) :
    chk X f = .ok () := by
  simp [chk, h1, h2]

/-- Value of `t` at zero-based sample `j`. -/
abbrev cv (o : OpEnum T) (X : JMat T) (t : Tree T) (j : Nat) : T := vx o (col X (j + 1)) t

theorem canon_eq (o : OpEnum T) (X : JMat T) (t : Tree T) :
    canon o X t = ((List.range X.ncols).map (cv o X t)).toArray := rfl

theorem canon_size (o : OpEnum T) (X : JMat T) (t : Tree T) : (canon o X t).size = X.ncols := by
  simp [canon]

theorem canon_getD (o : OpEnum T) (X : JMat T) (t : Tree T) (j : Nat) (hj : j < X.ncols) :
    (canon o X t).getD j JlScalar.undef = cv o X t j := by
  simp [canon, Array.getD, hj]

/-- Outputs built from per-sample values agree when the values agree. -/
theorem range_map_congr {β : Type} (n : Nat) (g h : Nat → β) (hgh : ∀ j, j < n → g j = h j) :
    ((List.range n).map g).toArray = ((List.range n).map h).toArray := by
  congr 1
  apply List.map_congr_left
  intro j hj
  exact hgh j (by simpa using hj)

/-- A feature read at a valid sample gives the feature leaf's value. -/
theorem featureAt_cv (o : OpEnum T) (X : JMat T) (f j : Nat) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows)
    (hj : j < X.ncols) : featureAt X f (j + 1) = .ok (cv o X (.feature f) j) := by
  rw [featureAt_eq X f (j + 1) hf1 hf2 (by omega) (by omega),
    JMat.get?_eq X f (j + 1) hf1 hf2 (by omega) (by omega)]
  simp [vx, col, Tree.denote, Except.toOption,
    JMat.get?_eq X f (j + 1) hf1 hf2 (by omega) (by omega)]

/-- The canonical output of a feature leaf is its row. -/
theorem rowInb_canon (o : OpEnum T) (X : JMat T) (f : Nat) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows) :
    rowInb X f = .ok (canon o X (.feature f)) := by
  rw [rowInb_eq X f hf1 hf2]
  congr 1
  apply Array.ext
  · simp [canon]
  · intro j h1 h2
    simp only [Array.getElem_ofFn]
    have hj : j < X.ncols := by simpa using h1
    simp only [canon, List.getElem_toArray, List.getElem_map, List.getElem_range]
    simp [vx, col, Tree.denote, Except.toOption,
      JMat.get?_eq X f (j + 1) hf1 hf2 (by omega) (by omega)]

/-- The canonical output of a sample-independent tree is a filled array. -/
theorem canon_fill (o : OpEnum T) (X : JMat T) (t : Tree T) (v : T)
    (h : ∀ j, j < X.ncols → cv o X t j = v) : canon o X t = JVec.fill X.ncols v := by
  rw [canon_eq, range_map_congr X.ncols (cv o X t) (fun _ => v) h]
  simp [JVec.fill, List.map_const']

omit [JlScalar T] in
theorem simdWrite_eq (cum : JVec T) (n : Nat) (F : Nat → Jl T) (g : Nat → T)
    (hs : cum.size = n) (hF : ∀ j, j < n → F (j + 1) = .ok (g j)) :
    simdWrite cum n F = .ok ((List.range n).map g).toArray := by
  have hm := mapM_jl_eq (fun j => F (j + 1)) g (List.range n)
    (fun j hj => hF j (by simpa using hj))
  unfold simdWrite
  simp only [show n ≤ cum.size by omega, ↓reduceIte]
  rw [hm]
  simp [hs]

theorem inplaceMap_eq (cum : JVec T) (G : Nat → T → Jl T) (g : Nat → T)
    (hG : ∀ j, j < cum.size → G (j + 1) (cum.getD j JlScalar.undef) = .ok (g j)) :
    inplaceMap cum G = .ok ((List.range cum.size).map g).toArray := by
  have hm := mapM_jl_eq (fun j => G (j + 1) (cum.getD j JlScalar.undef)) g (List.range cum.size)
    (fun j hj => hG j (by simpa using hj))
  unfold inplaceMap
  rw [hm]
  rfl

/-- `degn_eval` on canonical children computes the operator per sample. -/
theorem degnEval_canon (o : OpEnum T) (X : JMat T) (f : List T → T) (cs : List (Tree T))
    (hne : cs ≠ []) :
    degnEval f (cs.map (canon o X)) =
      .ok ((List.range X.ncols).map (fun j => f (cs.map (fun c => cv o X c j)))).toArray := by
  obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c cs' => exact ⟨c, cs', rfl⟩
  have hinner : ∀ j, j < X.ncols →
      ((c :: cs').map (canon o X)).mapM (fun a => getInb a j) =
        .ok ((c :: cs').map (fun c => cv o X c j)) := by
    intro j hj
    have := mapM_jl_eq (fun a => getInb a j) (fun a => a.getD j JlScalar.undef)
      ((c :: cs').map (canon o X)) (by
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨c', _, rfl⟩ := ha
        have hsz : j < (canon o X c').size := by rw [canon_size]; exact hj
        simp [getInb, hsz, Array.getD])
    rw [this, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c' _
    exact canon_getD o X c' j hj
  have hm := mapM_jl_eq
    (fun j => do
      let args ← ((c :: cs').map (canon o X)).mapM (fun a => getInb a j)
      pure (f args))
    (fun j => f ((c :: cs').map (fun c => cv o X c j))) (List.range X.ncols) (by
      intro j hj
      have hj' : j < X.ncols := by simpa using hj
      show (((c :: cs').map (canon o X)).mapM (fun a => getInb a j) >>= fun args =>
        pure (f args)) = _
      rw [hinner j hj']
      rfl)
  simp only [List.map_cons, degnEval, canon_size]
  simp only [List.map_cons] at hm
  rw [hm]
  rfl

/-- The canonical output of a branch whose children are valid at every sample. -/
theorem canon_branch (o : OpEnum T) (X : JMat T) (op : Nat) (cs : List (Tree T))
    (g : List T → T) (hg : o.lookup cs.length op = some g)
    (hv : ∀ j, j < X.ncols → ∀ c ∈ cs, AllValid o (col X (j + 1)) c) :
    canon o X (.branch op cs) =
      ((List.range X.ncols).map (fun j => g (cs.map (fun c => cv o X c j)))).toArray := by
  rw [canon_eq]
  apply range_map_congr
  intro j hj
  exact vx_branch o _ op cs g hg (fun c hc => AllValid.some o _ c (hv j hj c hc))

/-- Canonical outputs of trees valid at every sample pass `is_valid_array`. -/
theorem canon_isValid (o : OpEnum T) (X : JMat T) (t : Tree T) (hA : ArrayValidSound T)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t) :
    isValidArray (canon o X t) = true := by
  apply hA
  intro x hx
  simp only [canon, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact AllValid.valid o _ t (hv j hj)

end DynExpr.Eval
