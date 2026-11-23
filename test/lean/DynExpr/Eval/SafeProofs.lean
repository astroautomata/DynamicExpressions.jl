import DynExpr.Eval.Top

/-!
The typed evaluator never performs an out-of-range unchecked access: feature
indices beyond the rows of `X` and matrix buffers with too few rows raise
`BoundsError` (or another defined error) through `checkbounds` and the
checked slot view, never `JlError.undefinedBehavior`.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- An error other than undefined behaviour. -/
private abbrev NotUB (e : JlError) : Prop := ∀ s, e ≠ .undefinedBehavior s

/-- A call either succeeds with a value satisfying `P` or raises a defined error. -/
private def SafeM {α : Type} (P : α → Prop) : Jl α → Prop
  | .ok a => P a
  | .error e => NotUB e

private abbrev NoUB {α : Type} (m : Jl α) : Prop := SafeM (fun _ => True) m

private theorem safe_bind {α β : Type} {P : α → Prop} {Q : β → Prop} {m : Jl α}
    {f : α → Jl β} (hm : SafeM P m) (hf : ∀ a, P a → SafeM Q (f a)) : SafeM Q (m >>= f) := by
  cases m with
  | ok a => exact hf a hm
  | error e => exact hm

private theorem safe_pure {α : Type} {P : α → Prop} {a : α} (h : P a) :
    SafeM P (pure a : Jl α) := h

private theorem safe_ok {α : Type} {P : α → Prop} {a : α} (h : P a) :
    SafeM P (.ok a : Jl α) := h

private theorem safe_err {α : Type} {P : α → Prop} {e : JlError} (h : NotUB e) :
    SafeM P (.error e : Jl α) := h

private theorem notUB_bounds : NotUB .boundsError := by
  intro s h; cases h

private theorem notUB_exc (m : String) : NotUB (.errorException m) := by
  intro s h; cases h

private theorem noUB_ne {α : Type} {m : Jl α} (h : NoUB m) (s : String) :
    m ≠ .error (.undefinedBehavior s) := by
  intro he
  rw [he] at h
  have h' : NotUB (JlError.undefinedBehavior s) := h
  exact h' s rfl

omit [JlScalar T] in
private theorem chk_safe (X : JMat T) (f : Nat) :
    SafeM (fun _ => 1 ≤ f ∧ f ≤ X.nrows) (chk X f) := by
  unfold chk
  split
  · exact safe_ok ‹_›
  · exact safe_err notUB_bounds

omit [JlScalar T] in
private theorem nifOp_safe (ops : List (List T → T)) (op : Nat) : NoUB (nifOp ops op) := by
  unfold nifOp
  split
  · exact safe_err (notUB_exc _)
  · exact safe_ok trivial

omit [JlScalar T] in
private theorem idxOp_safe (ops : List (List T → T)) (op : Nat) : NoUB (idxOp ops op) := by
  unfold idxOp
  split
  · exact safe_err notUB_bounds
  · split
    · exact safe_ok trivial
    · exact safe_err notUB_bounds

private theorem mapM_safe {α β : Type} (f : α → Jl β) :
    ∀ xs : List α, (∀ x ∈ xs, NoUB (f x)) →
      SafeM (fun ys : List β => ys.length = xs.length) (xs.mapM f)
  | [], _ => by
    rw [List.mapM_nil]
    exact safe_pure rfl
  | x :: xs, h => by
    rw [List.mapM_cons]
    refine safe_bind (h x (by simp)) fun y _ => ?_
    refine safe_bind (mapM_safe f xs fun z hz => h z (by simp [hz])) fun ys hl => ?_
    exact safe_pure (by simp [hl])

omit [JlScalar T] in
private theorem featureAt_safe (X : JMat T) (f j : Nat) (h1 : 1 ≤ f) (h2 : f ≤ X.nrows)
    (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) : NoUB (featureAt X f j) := by
  rw [featureAt_eq X f j h1 h2 hj1 hj2, JMat.get?_eq X f j h1 h2 hj1 hj2]
  exact safe_ok trivial

omit [JlScalar T] in
/-- A feature read after a passing `checkbounds`, followed by a continuation. -/
private theorem read_safe {β : Type} {Q : β → Prop} (X : JMat T) {f j : Nat} {g : T → Jl β}
    (hf : 1 ≤ f ∧ f ≤ X.nrows) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols)
    (hg : ∀ v, SafeM Q (g v)) : SafeM Q (featureAt X f j >>= g) :=
  safe_bind (featureAt_safe X f j hf.1 hf.2 hj1 hj2) fun v _ => hg v

omit [JlScalar T] in
private theorem simdWrite_safe (cum : JVec T) (n : Nat) (F : Nat → Jl T) (hs : cum.size = n)
    (hF : ∀ j, 1 ≤ j → j ≤ n → NoUB (F j)) :
    SafeM (fun a : JVec T => a.size = n) (simdWrite cum n F) := by
  unfold simdWrite
  simp only [show n ≤ cum.size by omega, ↓reduceIte]
  refine safe_bind (mapM_safe (fun j => F (j + 1)) (List.range n) ?_) fun vs hl => ?_
  · intro j hj
    have := List.mem_range.mp hj
    exact hF (j + 1) (by omega) (by omega)
  · exact safe_pure (by simp [hl, hs])

private theorem inplaceMap_safe (cum : JVec T) (G : Nat → T → Jl T)
    (hG : ∀ j, 1 ≤ j → j ≤ cum.size → ∀ x, NoUB (G j x)) :
    SafeM (fun a : JVec T => a.size = cum.size) (inplaceMap cum G) := by
  unfold inplaceMap
  refine safe_bind (mapM_safe _ (List.range cum.size) ?_) fun vs hl => ?_
  · intro j hj
    have := List.mem_range.mp hj
    exact hG (j + 1) (by omega) (by omega) _
  · exact safe_pure (by simp [hl])

omit [JlScalar T] in
private theorem degn_safe (n : Nat) (f : List T → T) (xs : List (JVec T))
    (hs : ∀ x ∈ xs, x.size = n) : SafeM (fun a : JVec T => a.size = n) (degnEval f xs) := by
  cases xs with
  | nil =>
    unfold degnEval
    exact safe_err (notUB_exc _)
  | cons c cs =>
    have hc := hs c (by simp)
    unfold degnEval
    refine safe_bind (mapM_safe _ (List.range c.size) ?_) fun vs hl => ?_
    · intro j hj
      have hj' := List.mem_range.mp hj
      refine safe_bind (mapM_safe _ (c :: cs) ?_) fun _ _ => safe_pure trivial
      intro a ha
      have := hs a ha
      unfold getInb
      simp only [show j < a.size by omega, ↓reduceDIte]
      exact safe_ok trivial
    · exact safe_pure (by simp [hl, hc])

/-- Buffers whose slots are wide enough for `n` samples; the row count is free. -/
private def BufSafe (n : Nat) : Buf T → Prop
  | .none => True
  | .mat A _ => n ≤ A.ncols
  | .vec _ _ => True

omit [JlScalar T] in
private theorem bufSafe_mat {n : Nat} {A : JMat T} {i : Nat} :
    BufSafe n (Buf.mat A i) ↔ n ≤ A.ncols := Iff.rfl

/-- An array of length `n` with a safe buffer. -/
private abbrev ArrP (n : Nat) (p : JVec T × Buf T) : Prop := p.1.size = n ∧ BufSafe n p.2

/-- A result with one value per sample and a safe buffer. -/
private abbrev RP (X : JMat T) (p : ResultOk T × Buf T) : Prop :=
  p.1.x.size = X.ncols ∧ BufSafe X.ncols p.2

private abbrev Safe (X : JMat T) (m : Jl (ResultOk T × Buf T)) : Prop := SafeM (RP X) m

omit [JlScalar T] in
private theorem arr_bind {β : Type} {Q : β → Prop} {n : Nat} {m : Jl (JVec T × Buf T)}
    {k : JVec T × Buf T → Jl β} (hm : SafeM (ArrP n) m)
    (hk : ∀ a c, a.size = n → BufSafe n c → SafeM Q (k (a, c))) : SafeM Q (m >>= k) :=
  safe_bind hm fun p hp => hk p.1 p.2 hp.1 hp.2

omit [JlScalar T] in
private theorem res_bind {β : Type} {Q : β → Prop} {X : JMat T} {m : Jl (ResultOk T × Buf T)}
    {k : ResultOk T × Buf T → Jl β} (hm : Safe X m)
    (hk : ∀ r c, r.x.size = X.ncols → BufSafe X.ncols c → SafeM Q (k (r, c))) :
    SafeM Q (m >>= k) :=
  safe_bind hm fun p hp => hk p.1 p.2 hp.1 hp.2

omit [JlScalar T] in
private theorem row_safe (A : JMat T) (i : Nat) :
    SafeM (fun r : JVec T => r.size = A.ncols) (A.row i) := by
  unfold JMat.row
  split
  · exact safe_ok (by simp)
  · exact safe_err notUB_bounds

private theorem getArray_safe {n : Nat} {b : Buf T} (hb : BufSafe n b) :
    SafeM (ArrP n) (getArray b n) := by
  cases b with
  | none => exact safe_ok ⟨by simp [JVec.fill], trivial⟩
  | mat A i =>
    have hb' : n ≤ A.ncols := hb
    unfold getArray
    refine safe_bind (row_safe A (i + 1)) fun r hr => ?_
    simp only [hb', ↓reduceIte]
    refine safe_pure ⟨?_, hb'⟩
    show (r.extract 0 n).size = n
    have hr' : r.size = A.ncols := hr
    simp only [Array.size_extract, hr']
    omega
  | vec arrs i =>
    simp only [getArray]
    split
    · split
      · exact safe_ok ⟨by assumption, trivial⟩
      · exact safe_ok ⟨by simp [JVec.fill], trivial⟩
    · exact safe_ok ⟨by simp [JVec.fill], trivial⟩

private theorem getFilled_safe {n : Nat} {b : Buf T} (v : T) (hb : BufSafe n b) :
    SafeM (ArrP n) (getFilled b v n) := by
  cases b with
  | none => exact safe_ok ⟨by simp [JVec.fill], trivial⟩
  | mat A i =>
    unfold getFilled
    refine arr_bind (getArray_safe hb) ?_
    intro a c hs hc
    exact safe_pure ⟨by simp [JVec.fill, hs], hc⟩
  | vec arrs i =>
    unfold getFilled
    refine arr_bind (getArray_safe hb) ?_
    intro a c hs hc
    exact safe_pure ⟨by simp [JVec.fill, hs], hc⟩

omit [JlScalar T] in
private theorem rowInb_safe (X : JMat T) (f : Nat) (hf : 1 ≤ f ∧ f ≤ X.nrows) :
    SafeM (fun r : JVec T => r.size = X.ncols) (rowInb X f) := by
  unfold rowInb
  simp only [hf, and_self, ↓reduceIte]
  exact row_safe X f

private theorem getFeature_safe (X : JMat T) (f : Nat) {b : Buf T} (hf : 1 ≤ f ∧ f ≤ X.nrows)
    (hb : BufSafe X.ncols b) : SafeM (ArrP X.ncols) (getFeature b X f) := by
  cases b with
  | none =>
    unfold getFeature
    exact safe_bind (rowInb_safe X f hf) fun r hr => safe_pure ⟨hr, trivial⟩
  | mat A i =>
    unfold getFeature
    refine arr_bind (getArray_safe hb) ?_
    intro _ c _ hc
    exact safe_bind (rowInb_safe X f hf) fun r hr => safe_pure ⟨hr, hc⟩
  | vec arrs i =>
    unfold getFeature
    refine arr_bind (getArray_safe hb) ?_
    intro _ c _ hc
    exact safe_bind (rowInb_safe X f hf) fun r hr => safe_pure ⟨hr, hc⟩

private theorem retV_safe (cx : Ctx) (X : JMat T) (v : T) (k : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) (hb : BufSafe X.ncols b) (hk : Safe X (k b)) : Safe X (retV cx X v k b) := by
  unfold retV
  split
  · refine arr_bind (getArray_safe hb) ?_
    intro a c hs hc
    exact safe_pure ⟨hs, hc⟩
  · exact hk

private theorem retVIf_safe (cx : Ctx) (X : JMat T) (c : Bool) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (hb : BufSafe X.ncols b)
    (hk : Safe X (k b)) : Safe X (retVIf cx X c v k b) := by
  unfold retVIf
  split
  · exact retV_safe cx X v k b hb hk
  · exact hk

private theorem filled_safe (X : JMat T) (v : T) (b : Buf T) (hb : BufSafe X.ncols b) :
    Safe X (filled X v b) := by
  unfold filled
  refine arr_bind (getFilled_safe v hb) ?_
  intro a c hs hc
  exact safe_pure ⟨hs, hc⟩

private theorem deg1L2_safe (cx : Ctx) (X : JMat T) (f fl : List T → T) (ll lr : Tree T)
    (b : Buf T) (hb : BufSafe X.ncols b) : Safe X (deg1L2 cx X f fl ll lr b) := by
  unfold deg1L2
  dsimp only
  split
  · apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    exact filled_safe _ _ _ hb
  · split
    · apply retV_safe _ _ _ _ _ hb
      refine safe_bind (chk_safe X _) ?_
      intro _ hf
      refine arr_bind (getArray_safe hb) ?_
      intro cum c hs hc
      refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
        read_safe X hf hj1 hj2 fun _ => safe_pure trivial) fun out ho => ?_
      exact safe_pure ⟨ho, hc⟩
    · split
      · refine safe_bind (chk_safe X _) ?_
        intro _ hf
        apply retV_safe _ _ _ _ _ hb
        refine arr_bind (getArray_safe hb) ?_
        intro cum c hs hc
        refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
          read_safe X hf hj1 hj2 fun _ => safe_pure trivial) fun out ho => ?_
        exact safe_pure ⟨ho, hc⟩
      · refine safe_bind (chk_safe X _) ?_
        intro _ hf
        refine safe_bind (chk_safe X _) ?_
        intro _ hg
        refine arr_bind (getArray_safe hb) ?_
        intro cum c hs hc
        refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
          read_safe X hf hj1 hj2 fun _ => read_safe X hg hj1 hj2 fun _ =>
            safe_pure trivial) fun out ho => ?_
        exact safe_pure ⟨ho, hc⟩

private theorem deg1L1_safe (cx : Ctx) (X : JMat T) (f fl : List T → T) (ll : Tree T)
    (b : Buf T) (hb : BufSafe X.ncols b) : Safe X (deg1L1 cx X f fl ll b) := by
  unfold deg1L1
  dsimp only
  split
  · apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    exact filled_safe _ _ _ hb
  · refine safe_bind (chk_safe X _) ?_
    intro _ hf
    refine arr_bind (getArray_safe hb) ?_
    intro cum c hs hc
    refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
      read_safe X hf hj1 hj2 fun _ => safe_pure trivial) fun out ho => ?_
    exact safe_pure ⟨ho, hc⟩

private theorem deg2L0R0_safe (cx : Ctx) (X : JMat T) (f : List T → T) (l r : Tree T)
    (b : Buf T) (hb : BufSafe X.ncols b) : Safe X (deg2L0R0 cx X f l r b) := by
  unfold deg2L0R0
  dsimp only
  split
  · apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    apply retV_safe _ _ _ _ _ hb
    exact filled_safe _ _ _ hb
  · split
    · refine arr_bind (getArray_safe hb) ?_
      intro cum c hs hc
      apply retV_safe _ _ _ _ _ hc
      refine safe_bind (chk_safe X _) ?_
      intro _ hf
      refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
        read_safe X hf hj1 hj2 fun _ => safe_pure trivial) fun out ho => ?_
      exact safe_pure ⟨ho, hc⟩
    · split
      · refine arr_bind (getArray_safe hb) ?_
        intro cum c hs hc
        refine safe_bind (chk_safe X _) ?_
        intro _ hf
        apply retV_safe _ _ _ _ _ hc
        refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
          read_safe X hf hj1 hj2 fun _ => safe_pure trivial) fun out ho => ?_
        exact safe_pure ⟨ho, hc⟩
      · refine arr_bind (getArray_safe hb) ?_
        intro cum c hs hc
        refine safe_bind (chk_safe X _) ?_
        intro _ hf
        refine safe_bind (chk_safe X _) ?_
        intro _ hg
        refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
          read_safe X hf hj1 hj2 fun _ => read_safe X hg hj1 hj2 fun _ =>
            safe_pure trivial) fun out ho => ?_
        exact safe_pure ⟨ho, hc⟩

private theorem deg2L0_safe (cx : Ctx) (X : JMat T) (f : List T → T) (l : Tree T)
    (cum : JVec T) (cid : Ident) (b : Buf T) (hs : cum.size = X.ncols)
    (hb : BufSafe X.ncols b) : Safe X (deg2L0 cx X f l cum cid b) := by
  unfold deg2L0
  dsimp only
  split
  · apply retV_safe _ _ _ _ _ hb
    refine safe_bind (inplaceMap_safe cum _ fun _ _ _ _ => safe_pure trivial) fun out ho => ?_
    exact safe_pure ⟨Eq.trans ho hs, hb⟩
  · refine safe_bind (chk_safe X _) ?_
    intro _ hf
    refine safe_bind (inplaceMap_safe cum _ fun j hj1 hj2 _ =>
      read_safe X hf hj1 (by omega) fun _ => safe_pure trivial) fun out ho => ?_
    exact safe_pure ⟨Eq.trans ho hs, hb⟩

private theorem deg2R0_safe (cx : Ctx) (X : JMat T) (f : List T → T) (r : Tree T)
    (cum : JVec T) (cid : Ident) (b : Buf T) (hs : cum.size = X.ncols)
    (hb : BufSafe X.ncols b) : Safe X (deg2R0 cx X f r cum cid b) := by
  unfold deg2R0
  dsimp only
  split
  · apply retV_safe _ _ _ _ _ hb
    refine safe_bind (inplaceMap_safe cum _ fun _ _ _ _ => safe_pure trivial) fun out ho => ?_
    exact safe_pure ⟨Eq.trans ho hs, hb⟩
  · refine safe_bind (chk_safe X _) ?_
    intro _ hf
    refine safe_bind (inplaceMap_safe cum _ fun j hj1 hj2 _ =>
      read_safe X hf hj1 (by omega) fun _ => safe_pure trivial) fun out ho => ?_
    exact safe_pure ⟨Eq.trans ho hs, hb⟩

private theorem branch0_safe (cx : Ctx) (X : JMat T) (f g : List T → T) (s : Side)
    (l1 l2 l3 : Tree T) (b : Buf T) (hb : BufSafe X.ncols b) :
    Safe X (branch0 cx X f g s l1 l2 l3 b) := by
  unfold branch0
  refine arr_bind (getArray_safe hb) ?_
  intro cum c hs hc
  dsimp only
  split
  · exact safe_pure ⟨hs, hc⟩
  · refine safe_bind (chk_safe X _) ?_
    intro _ h1
    refine safe_bind (chk_safe X _) ?_
    intro _ h2
    refine safe_bind (chk_safe X _) ?_
    intro _ h3
    cases s <;>
    · apply retVIf_safe _ _ _ _ _ _ hc
      refine safe_bind (simdWrite_safe cum _ _ hs fun j hj1 hj2 =>
        safe_bind (read_safe (Q := fun _ => True) X h1 hj1 hj2 fun _ => safe_pure trivial)
          fun _ _ =>
        safe_bind (read_safe (Q := fun _ => True) X h2 hj1 hj2 fun _ => safe_pure trivial)
          fun _ _ =>
        safe_bind (read_safe (Q := fun _ => True) X h3 hj1 hj2 fun _ => safe_pure trivial)
          fun _ _ =>
          safe_pure trivial) fun out ho => ?_
      exact safe_pure ⟨ho, hc⟩

private theorem checked_safe (cx : Ctx) (X : JMat T) (ev : Buf T → Jl (ResultOk T × Buf T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (he : Safe X (ev b))
    (hk : ∀ a id c, a.size = X.ncols → BufSafe X.ncols c → Safe X (k a id c)) :
    Safe X (checked cx ev k b) := by
  unfold checked
  refine res_bind he ?_
  intro r c hs hc
  try dsimp only
  split
  · exact safe_pure ⟨hs, hc⟩
  · split
    · exact safe_pure ⟨hs, hc⟩
    · exact hk _ _ _ hs hc

private theorem unfused1_safe (cx : Ctx) (X : JMat T) (fop : Jl (List T → T))
    (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (hop : NoUB fop)
    (he : Safe X (ev b)) : Safe X (unfused1 cx fop ev b) := by
  unfold unfused1
  refine checked_safe cx X ev _ b he ?_
  intro a id c hs hc
  refine safe_bind hop fun f _ => ?_
  refine safe_bind (degn_safe X.ncols f [a] ?_) fun out ho => safe_pure ⟨ho, hc⟩
  intro x hx
  rw [List.mem_singleton.mp hx]
  exact hs

private theorem unfused2_safe (cx : Ctx) (X : JMat T) (fop : Jl (List T → T))
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (hop : NoUB fop)
    (hl : ∀ b, BufSafe X.ncols b → Safe X (evL b))
    (hr : ∀ b, BufSafe X.ncols b → Safe X (evR b)) (hb : BufSafe X.ncols b) :
    Safe X (unfused2 cx fop evL evR b) := by
  unfold unfused2
  refine checked_safe cx X evL _ b (hl b hb) ?_
  intro a id c hs hc
  refine checked_safe cx X evR _ c (hr c hc) ?_
  intro a' id' c' hs' hc'
  refine safe_bind hop fun f _ => ?_
  refine safe_bind (degn_safe X.ncols f [a, a'] ?_) fun out ho => safe_pure ⟨ho, hc'⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact hs
  · exact hs'

private theorem deg1Dispatch_safe (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat)
    (c : Tree T) (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (hev : ∀ b, BufSafe X.ncols b → Safe X (ev b)) (hb : BufSafe X.ncols b) :
    Safe X (deg1Dispatch cx o X op c ev b) := by
  unfold deg1Dispatch
  dsimp only
  split
  · exact unfused1_safe cx X _ ev b (idxOp_safe _ _) (hev b hb)
  · refine safe_bind (nifOp_safe _ _) ?_
    intro f _
    split <;> (try split) <;> first
      | exact unfused1_safe cx X _ ev b (safe_pure trivial) (hev b hb)
      | exact safe_bind (nifOp_safe _ _) fun fl _ => deg1L2_safe cx X f fl _ _ b hb
      | exact safe_bind (nifOp_safe _ _) fun fl _ => deg1L1_safe cx X f fl _ b hb

private theorem deg2Dispatch_safe (cx : Ctx) (o : OpEnum T) (X : JMat T) (op : Nat)
    (l r : Tree T) (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (hl : ∀ b, BufSafe X.ncols b → Safe X (evL b))
    (hr : ∀ b, BufSafe X.ncols b → Safe X (evR b)) (hb : BufSafe X.ncols b) :
    Safe X (deg2Dispatch cx o X op l r evL evR b) := by
  unfold deg2Dispatch
  dsimp only
  split
  · exact unfused2_safe cx X _ evL evR b (idxOp_safe _ _) hl hr hb
  · refine safe_bind (nifOp_safe _ _) ?_
    intro f _
    repeat' split
    all_goals first
      | exact unfused2_safe cx X _ evL evR b (safe_pure trivial) hl hr hb
      | exact deg2L0R0_safe cx X f _ _ b hb
      | exact safe_bind (nifOp_safe _ _) fun g _ => branch0_safe cx X f g _ _ _ _ b hb
      | exact checked_safe cx X evL _ b (hl b hb) fun a id c hs hc =>
          deg2R0_safe cx X f _ a id c hs hc
      | exact checked_safe cx X evR _ b (hr b hb) fun a id c hs hc =>
          deg2L0_safe cx X f _ a id c hs hc

private theorem constEvalL_safe (o : OpEnum T) (early : Bool) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, NoUB (constEval o c early)) : NoUB (constEvalL o cs early) := by
  induction cs with
  | nil =>
    unfold constEvalL
    exact safe_ok trivial
  | cons c cs hi =>
    unfold constEvalL
    refine safe_bind (ih c (by simp)) ?_
    intro p _
    obtain ⟨v, ok⟩ := p
    try dsimp only
    split
    · exact safe_pure trivial
    · refine safe_bind (hi fun d hd => ih d (by simp [hd])) ?_
      intro q _
      cases q <;> exact safe_pure trivial

private theorem constEval_safe (o : OpEnum T) (early : Bool) (t : Tree T) :
    NoUB (constEval o t early) := by
  induction t using Tree.induction with
  | hc v =>
    unfold constEval
    exact safe_ok trivial
  | hf f =>
    unfold constEval
    exact safe_ok trivial
  | hb op cs ih =>
    unfold constEval
    refine safe_bind (constEvalL_safe o early cs ih) ?_
    intro q _
    cases q with
    | inl p => exact safe_pure trivial
    | inr vs =>
      try dsimp only
      split
      · exact safe_bind (idxOp_safe _ _) fun _ _ => safe_pure trivial
      · exact safe_bind (nifOp_safe _ _) fun _ _ => safe_pure trivial

private theorem constPath_safe (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (early : Bool) (hb : BufSafe X.ncols b) : Safe X (constPath o X t b early) := by
  have hc := constEval_safe o early t
  unfold constPath
  split
  · next e he =>
    rw [he] at hc
    exact safe_err hc
  · split
    · refine arr_bind (getArray_safe hb) ?_
      intro a c hs hc'
      exact safe_pure ⟨hs, hc'⟩
    · exact filled_safe X _ b hb

/-- Children loop results: an early return, or child arrays of one value per
sample. -/
private def ChildP (X : JMat T) :
    (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T) → Prop
  | .inl p => RP X p
  | .inr (xs, c) => (∀ q ∈ xs, q.1.size = X.ncols) ∧ BufSafe X.ncols c

omit [JlScalar T] in
private theorem childP_inl {X : JMat T} {p : ResultOk T × Buf T} :
    ChildP X (.inl p) ↔ RP X p := Iff.rfl

omit [JlScalar T] in
private theorem childP_inr {X : JMat T} {xs : List (JVec T × Ident)} {c : Buf T} :
    ChildP X (.inr (xs, c)) ↔ (∀ q ∈ xs, q.1.size = X.ncols) ∧ BufSafe X.ncols c := Iff.rfl

private theorem children_safe (cx : Ctx) (o : OpEnum T) (X : JMat T) (cs : List (Tree T))
    (ih : ∀ t ∈ cs, ∀ b, BufSafe X.ncols b → Safe X (evalT cx o X t b)) :
    ∀ b, BufSafe X.ncols b → SafeM (ChildP X) (evalChildren cx o X cs b) := by
  induction cs with
  | nil =>
    intro b hb
    unfold evalChildren
    exact safe_ok (childP_inr.2 ⟨by simp, hb⟩)
  | cons t ts hi =>
    intro b hb
    unfold evalChildren
    refine res_bind (ih t (by simp) b hb) ?_
    intro r c hs hc
    try dsimp only
    split
    · exact safe_pure (childP_inl.2 ⟨hs, hc⟩)
    · split
      · exact safe_pure (childP_inl.2 ⟨hs, hc⟩)
      · refine safe_bind (hi (fun u hu => ih u (by simp [hu])) c hc) ?_
        intro res hres
        cases res with
        | inl p => exact safe_pure hres
        | inr p =>
          obtain ⟨xs, d⟩ := p
          have h' := childP_inr.1 hres
          refine safe_pure (childP_inr.2 ⟨?_, h'.2⟩)
          intro q hq
          cases hq with
          | head => exact hs
          | tail _ hm => exact h'.1 q hm

omit [JlScalar T] in
private theorem degnFinish_safe (o : OpEnum T) (X : JMat T) (d op : Nat)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)) (h : ChildP X res) :
    Safe X (degnFinish o d op res) := by
  cases res with
  | inl p =>
    unfold degnFinish
    exact safe_pure (childP_inl.1 h)
  | inr p =>
    obtain ⟨xs, c⟩ := p
    have h' := childP_inr.1 h
    unfold degnFinish
    refine safe_bind (nifOp_safe _ _) fun f _ => ?_
    refine safe_bind (degn_safe X.ncols f (xs.map Prod.fst) ?_) fun out ho =>
      safe_pure ⟨ho, h'.2⟩
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    exact h'.1 q hq

/-- Every representable tree evaluates without undefined behaviour from any
buffer whose slots are wide enough, whatever its row count. -/
private theorem eval_safe (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) :
    t.Representable → ∀ b, BufSafe X.ncols b → Safe X (evalT cx o X t b) := by
  induction t using Tree.induction with
  | hc v =>
    intro _ b hb
    unfold evalT
    refine arr_bind (getFilled_safe v hb) ?_
    intro a c hs hc
    exact safe_pure ⟨hs, hc⟩
  | hf f =>
    intro _ b hb
    unfold evalT
    refine safe_bind (chk_safe X f) ?_
    intro _ hf
    refine arr_bind (getFeature_safe X f hf hb) ?_
    intro a c hs hc
    exact safe_pure ⟨hs, hc⟩
  | hb op cs ih =>
    intro hrep b hb
    simp only [Tree.Representable] at hrep
    have hch : ∀ c ∈ cs, ∀ b, BufSafe X.ncols b → Safe X (evalT cx o X c b) :=
      fun c hc => ih c hc (hrep.2 c hc)
    unfold evalT
    split
    · exact constPath_safe o X _ b cx.earlyExit hb
    · cases cs with
      | nil => simp at hrep
      | cons c cs =>
        cases cs with
        | nil => exact deg1Dispatch_safe cx o X op c _ b (hch c (by simp)) hb
        | cons d ds =>
          cases ds with
          | nil =>
            exact deg2Dispatch_safe cx o X op c d _ _ b (hch c (by simp)) (hch d (by simp)) hb
          | cons e es =>
            simp only
            split
            · exact deg2Dispatch_safe cx o X op c d _ _ b (hch c (by simp)) (hch d (by simp)) hb
            · refine safe_bind (children_safe cx o X _ hch b hb) ?_
              intro res hres
              exact degnFinish_safe o X _ op res hres

private theorem evalArr_safe (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (h : Safe X (evalT cx o X t b)) : NoUB (evalArr cx o X t b) := by
  unfold evalArr
  refine res_bind h ?_
  intro r c _ _
  exact safe_pure trivial

theorem evalFeatureOOB_proof : evalFeatureOOB := by
  intro T _ ext impl D early fused o X t _ hw m
  have h := evalArr_safe ⟨early, fused, D⟩ o X t .none
    (eval_safe ⟨early, fused, D⟩ o X t (Tree.WF.representable t hw) .none trivial)
  exact noUB_ne h m

theorem evalSmallBuffer_proof : evalSmallBuffer := by
  intro T _ ext impl D early fused o X t A i _ hw hc m
  have hb : BufSafe X.ncols (Buf.mat A i) := bufSafe_mat.2 (by omega)
  have h := evalArr_safe ⟨early, fused, D⟩ o X t (.mat A i)
    (eval_safe ⟨early, fused, D⟩ o X t (Tree.WF.representable t hw) _ hb)
  exact noUB_ne h m

/-- `evalFeatureOOB` hypotheses: one sample, and a feature index beyond the
single row of `X`. -/
example : 1 ≤ (⟨1, 1, #[.fin 1], rfl⟩ : JMat JF).ncols ∧
    (Tree.feature 2 : Tree JF).WF 2 (⟨[]⟩ : OpEnum JF).nops 65535 :=
  ⟨Nat.le_refl 1, by simp [Tree.WF]⟩

/-- `evalSmallBuffer` hypotheses: a buffer matrix with no rows at all. -/
example : 1 ≤ (⟨1, 1, #[.fin 1], rfl⟩ : JMat JF).ncols ∧
    (Tree.feature 1 : Tree JF).WF 2 (⟨[]⟩ : OpEnum JF).nops
      (⟨1, 1, #[.fin 1], rfl⟩ : JMat JF).nrows ∧
    (⟨0, 1, #[], rfl⟩ : JMat JF).ncols = (⟨1, 1, #[.fin 1], rfl⟩ : JMat JF).ncols :=
  ⟨Nat.le_refl 1, by simp [Tree.WF], rfl⟩

end DynExpr.Eval
