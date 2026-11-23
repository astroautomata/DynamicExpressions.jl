import DynExpr.Eval.AliasProofs
import DynExpr.Eval.Alloc

namespace DynExpr.Eval
variable {T : Type} [JlScalar T]

/-- Storage sufficient for every allocation of a tree. -/
def BufOK (X : JMat T) (t : Tree T) (b : Buf T) : Prop :=
  b = .none ∨ (∃ arrs i, b = .vec arrs i) ∨
    ∃ A i, b = .mat A i ∧ A.ncols = X.ncols ∧ i + t.size ≤ A.nrows

omit [JlScalar T] in
private theorem bufOK_good {X : JMat T} {t : Tree T} {b : Buf T}
    (h : BufOK X t b) : Good X.ncols t.size b := by
  rcases h with rfl | ⟨a, i, rfl⟩ | ⟨A, i, rfl, hc, hr⟩
  · trivial
  · trivial
  · exact ⟨by omega, hr⟩

private def Complete (X : JMat T) (k : Nat) (m : Jl (ResultOk T × Buf T)) : Prop :=
  ∃ r b, m = .ok (r, b) ∧ r.x.size = X.ncols ∧ Good X.ncols k b

private theorem filled_total (X : JMat T) (v : T) (b : Buf T) (k : Nat)
    (h : Good X.ncols (k + 1) b) : Complete X k (filled X v b) := by
  obtain ⟨c, hc, hg⟩ := getFilled_good v h
  refine ⟨⟨JVec.fill X.ncols v, true, nextId b⟩, c, ?_, by simp [JVec.fill], hg⟩
  simp [filled, hc]

private theorem retV_total (cx : Ctx) (X : JMat T) (v : T) (b : Buf T) (k : Nat)
    (f : Buf T → Jl (ResultOk T × Buf T)) (h : Good X.ncols (k + 1) b)
    (hf : Complete X k (f b)) : Complete X k (retV cx X v f b) := by
  unfold retV
  split
  · obtain ⟨a, c, he, hs, hg⟩ := getArray_good h
    exact ⟨⟨a, false, nextId b⟩, c, by simp [he], hs, hg⟩
  · exact hf

private theorem mapM_total {A B : Type} (xs : List A) (f : A → Jl B)
    (hf : ∀ x ∈ xs, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys ∧ ys.length = xs.length := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := hf x (by simp)
    obtain ⟨ys, hys, hl⟩ := ih (fun z hz => hf z (by simp [hz]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys], by simp [hl]⟩

omit [JlScalar T] in
private theorem simd_total (X : JMat T) (cum : JVec T) (f : Nat → Jl T)
    (hs : cum.size = X.ncols)
    (hf : ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, f j = .ok v) :
    ∃ a, simdWrite cum X.ncols f = .ok a ∧ a.size = X.ncols := by
  obtain ⟨xs, hx, hl⟩ := mapM_total (List.range X.ncols) (fun j => f (j + 1))
    (fun j hj => hf (j + 1) (by omega) (by have hj' := List.mem_range.mp hj; omega))
  refine ⟨xs.toArray, ?_, by simpa using hl⟩
  simp [simdWrite, hs, hx]

private theorem inplace_total (X : JMat T) (cum : JVec T) (f : Nat → T → Jl T)
    (hs : cum.size = X.ncols)
    (hf : ∀ j, 1 ≤ j → j ≤ X.ncols → ∀ x, ∃ v, f j x = .ok v) :
    ∃ a, inplaceMap cum f = .ok a ∧ a.size = X.ncols := by
  obtain ⟨xs, hx, hl⟩ := mapM_total (List.range cum.size)
    (fun j => f (j + 1) (cum.getD j JlScalar.undef)) (by
      intro j hj
      exact hf (j + 1) (by omega) (by have hj' := List.mem_range.mp hj; omega) _)
  refine ⟨xs.toArray, ?_, by simp_all⟩
  unfold inplaceMap
  rw [hx]
  rfl

omit [JlScalar T] in
private theorem feature_total (X : JMat T) (f j : Nat)
    (h1 : 1 ≤ f) (h2 : f ≤ X.nrows) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    ∃ v, featureAt X f j = .ok v := by
  rw [featureAt_eq X f j h1 h2 hj1 hj2, JMat.get?_eq X f j h1 h2 hj1 hj2]
  exact ⟨_, rfl⟩

private def LeafOK (X : JMat T) : Tree T → Prop
  | .const _ => True
  | .feature f => 1 ≤ f ∧ f ≤ X.nrows
  | .branch .. => False

omit [JlScalar T] in
private theorem leafOK_of_WF (X : JMat T) (o : OpEnum T) (D : Nat) (t : Tree T)
    (h : t.WF D o.nops X.nrows) (hl : isLeaf t = true) : LeafOK X t := by
  cases t <;> simp_all [Tree.WF, isLeaf, LeafOK]

omit [JlScalar T] in
private theorem leaf_feature_total (X : JMat T) (t : Tree T) (h : LeafOK X t)
    (hc : isConstLeaf t = false) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    ∃ v, featureAt X (leafFeat t) j = .ok v := by
  cases t with
  | const v => simp [isConstLeaf] at hc
  | feature f => exact feature_total X f j h.1 h.2 hj1 hj2
  | branch op cs => exact False.elim h

private theorem chk_leaf (X : JMat T) (t : Tree T) (h : LeafOK X t)
    (hc : isConstLeaf t = false) : chk X (leafFeat t) = .ok () := by
  cases t with
  | const v => simp [isConstLeaf] at hc
  | feature f => exact chk_ok X f h.1 h.2
  | branch op cs => exact False.elim h

private theorem chk_pick (X : JMat T) (t : Tree T) (h : LeafOK X t) (hp : 1 ≤ X.nrows) :
    chk X (if isConstLeaf t = true then 1 else leafFeat t) = .ok () := by
  by_cases hc : isConstLeaf t = true
  · simp [hc, chk_ok X 1 (by omega) hp]
  · simp [hc, chk_leaf X t h (by simpa using hc)]

omit [JlScalar T] in
private theorem degn_total (X : JMat T) (f : List T → T) (xs : List (JVec T))
    (hne : xs ≠ []) (hs : ∀ x ∈ xs, x.size = X.ncols) :
    ∃ a, degnEval f xs = .ok a ∧ a.size = X.ncols := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    have hx := hs x (by simp)
    obtain ⟨vs, hv, hl⟩ := mapM_total (List.range x.size) (fun j => do
      let args ← (x :: xs).mapM (fun a => getInb a j)
      pure (f args)) (by
      intro j hj
      have hj' : j < X.ncols := by simpa [hx] using hj
      obtain ⟨args, ha, _⟩ := mapM_total (x :: xs) (fun a => getInb a j) (by
        intro a hm
        have hsize := hs a hm
        exact ⟨a[j]'(by omega), by simp [getInb, show j < a.size by omega]⟩)
      exact ⟨f args, by simp [ha]⟩)
    refine ⟨vs.toArray, ?_, by simp_all⟩
    simp only [degnEval]
    rw [hv]
    rfl

private theorem allocSimd_total (X : JMat T) (b : Buf T) (k : Nat)
    (f : Nat → Jl T) (h : Good X.ncols (k + 1) b)
    (hf : ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, f j = .ok v) :
    Complete X k (do
      let (cum, c) ← getArray b X.ncols
      let out ← simdWrite cum X.ncols f
      pure (⟨out, true, nextId b⟩, c)) := by
  obtain ⟨a, c, ha, hs, hg⟩ := getArray_good h
  obtain ⟨out, ho, hsize⟩ := simd_total X a f hs hf
  exact ⟨⟨out, true, nextId b⟩, c, by simp [ha, ho], hsize, hg⟩

private theorem deg1L1_total (cx : Ctx) (X : JMat T) (f g : List T → T)
    (l : Tree T) (b : Buf T) (k : Nat) (hl : LeafOK X l)
    (h : Good X.ncols (k + 1) b) : Complete X k (deg1L1 cx X f g l b) := by
  unfold deg1L1
  split
  · apply retV_total _ _ _ _ _ _ h
    apply retV_total _ _ _ _ _ _ h
    apply retV_total _ _ _ _ _ _ h
    exact filled_total _ _ _ _ h
  · rw [chk_leaf X l hl (by simp_all)]
    simp only [jl_ok_bind]
    apply allocSimd_total X b k _ h
    intro j hj1 hj2
    obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
    exact ⟨post cx.earlyExit f (g [v]), by simp [hv]⟩

private theorem deg1L2_total (cx : Ctx) (X : JMat T) (f g : List T → T)
    (l r : Tree T) (b : Buf T) (k : Nat) (hl : LeafOK X l) (hr : LeafOK X r)
    (h : Good X.ncols (k + 1) b) : Complete X k (deg1L2 cx X f g l r b) := by
  unfold deg1L2
  dsimp only
  split
  · apply retV_total _ _ _ _ _ _ h
    apply retV_total _ _ _ _ _ _ h
    apply retV_total _ _ _ _ _ _ h
    apply retV_total _ _ _ _ _ _ h
    exact filled_total _ _ _ _ h
  · split
    · apply retV_total _ _ _ _ _ _ h
      rw [chk_leaf X r hr (by simp_all)]
      simp only [jl_ok_bind]
      apply allocSimd_total X b k _ h
      intro j hj1 hj2
      obtain ⟨v, hv⟩ := leaf_feature_total X r hr (by simp_all) j hj1 hj2
      exact ⟨post cx.earlyExit f (g [leafVal l, v]), by simp [hv]⟩
    · split
      · rw [chk_leaf X l hl (by simp_all)]
        simp only [jl_ok_bind]
        apply retV_total _ _ _ _ _ _ h
        apply allocSimd_total X b k _ h
        intro j hj1 hj2
        obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
        exact ⟨post cx.earlyExit f (g [v, leafVal r]), by simp [hv]⟩
      · rw [chk_leaf X l hl (by simp_all), chk_leaf X r hr (by simp_all)]
        simp only [jl_ok_bind]
        apply allocSimd_total X b k _ h
        intro j hj1 hj2
        obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
        obtain ⟨w, hw⟩ := leaf_feature_total X r hr (by simp_all) j hj1 hj2
        exact ⟨post cx.earlyExit f (g [v, w]), by simp [hv, hw]⟩

private theorem leafWrite_total (cx : Ctx) (X : JMat T) (f : List T → T)
    (l : Tree T) (cum : JVec T) (id : Ident) (b : Buf T) (k : Nat)
    (hl : LeafOK X l) (hs : cum.size = X.ncols) (h : Good X.ncols (k + 1) b) :
    Complete X k (deg2L0 cx X f l cum id b) := by
  unfold deg2L0
  split
  · apply retV_total _ _ _ _ _ _ h
    obtain ⟨out, ho, hos⟩ := inplace_total X cum (fun _ x => pure (f [leafVal l, x])) hs
      (fun _ _ _ x => ⟨f [leafVal l, x], rfl⟩)
    exact ⟨⟨out, true, id⟩, b, by rw [ho]; rfl, hos, h.mono (by omega)⟩
  · rw [chk_leaf X l hl (by simp_all)]
    simp only [jl_ok_bind]
    obtain ⟨out, ho, hos⟩ := inplace_total X cum
      (fun j x => do let v ← featureAt X (leafFeat l) j; pure (f [v, x])) hs (by
      intro j hj1 hj2 x
      obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
      exact ⟨f [v, x], by simp [hv]⟩)
    exact ⟨⟨out, true, id⟩, b, by rw [ho]; rfl, hos, h.mono (by omega)⟩

private theorem leafWriteR_total (cx : Ctx) (X : JMat T) (f : List T → T)
    (r : Tree T) (cum : JVec T) (id : Ident) (b : Buf T) (k : Nat)
    (hr : LeafOK X r) (hs : cum.size = X.ncols) (h : Good X.ncols (k + 1) b) :
    Complete X k (deg2R0 cx X f r cum id b) := by
  unfold deg2R0
  split
  · apply retV_total _ _ _ _ _ _ h
    obtain ⟨out, ho, hos⟩ := inplace_total X cum (fun _ x => pure (f [x, leafVal r])) hs
      (fun _ _ _ x => ⟨f [x, leafVal r], rfl⟩)
    exact ⟨⟨out, true, id⟩, b, by rw [ho]; rfl, hos, h.mono (by omega)⟩
  · rw [chk_leaf X r hr (by simp_all)]
    simp only [jl_ok_bind]
    obtain ⟨out, ho, hos⟩ := inplace_total X cum
      (fun j x => do let v ← featureAt X (leafFeat r) j; pure (f [x, v])) hs (by
      intro j hj1 hj2 x
      obtain ⟨v, hv⟩ := leaf_feature_total X r hr (by simp_all) j hj1 hj2
      exact ⟨f [x, v], by simp [hv]⟩)
    exact ⟨⟨out, true, id⟩, b, by rw [ho]; rfl, hos, h.mono (by omega)⟩

private theorem deg2L0R0_total (cx : Ctx) (X : JMat T) (f : List T → T)
    (l r : Tree T) (b : Buf T) (k : Nat) (hl : LeafOK X l) (hr : LeafOK X r)
    (h : Good X.ncols (k + 2) b) : Complete X k (deg2L0R0 cx X f l r b) := by
  have h1 : Good X.ncols (k + 1) b := h.mono (by omega)
  unfold deg2L0R0
  dsimp only
  split
  · apply retV_total _ _ _ _ _ _ h1
    apply retV_total _ _ _ _ _ _ h1
    apply retV_total _ _ _ _ _ _ h1
    exact filled_total _ _ _ _ h1
  · split
    · obtain ⟨a, c, ha, hs, hg⟩ := getArray_good (k := k + 1) (by simpa [Nat.add_assoc] using h)
      simp only [ha, jl_ok_bind]
      apply retV_total _ _ _ _ _ _ hg
      rw [chk_leaf X r hr (by simp_all)]
      simp only [jl_ok_bind]
      obtain ⟨out, ho, hos⟩ := simd_total X a
        (fun j => do let v ← featureAt X (leafFeat r) j; pure (f [leafVal l, v])) hs (by
        intro j hj1 hj2
        obtain ⟨v, hv⟩ := leaf_feature_total X r hr (by simp_all) j hj1 hj2
        exact ⟨f [leafVal l, v], by simp [hv]⟩)
      exact ⟨⟨out, true, nextId b⟩, c, by rw [ho]; rfl, hos, hg.mono (by omega)⟩
    · split
      · obtain ⟨a, c, ha, hs, hg⟩ := getArray_good (k := k + 1) (by simpa [Nat.add_assoc] using h)
        simp only [ha, jl_ok_bind]
        rw [chk_leaf X l hl (by simp_all)]
        simp only [jl_ok_bind]
        apply retV_total _ _ _ _ _ _ hg
        obtain ⟨out, ho, hos⟩ := simd_total X a
          (fun j => do let v ← featureAt X (leafFeat l) j; pure (f [v, leafVal r])) hs (by
          intro j hj1 hj2
          obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
          exact ⟨f [v, leafVal r], by simp [hv]⟩)
        exact ⟨⟨out, true, nextId b⟩, c, by rw [ho]; rfl, hos, hg.mono (by omega)⟩
      · obtain ⟨a, c, ha, hs, hg⟩ := getArray_good h1
        simp only [ha, jl_ok_bind]
        rw [chk_leaf X l hl (by simp_all), chk_leaf X r hr (by simp_all)]
        simp only [jl_ok_bind]
        obtain ⟨out, ho, hos⟩ := simd_total X a
          (fun j => do
            let v1 ← featureAt X (leafFeat l) j
            let v2 ← featureAt X (leafFeat r) j
            pure (f [v1, v2])) hs (by
          intro j hj1 hj2
          obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
          obtain ⟨w, hw⟩ := leaf_feature_total X r hr (by simp_all) j hj1 hj2
          exact ⟨f [v, w], by simp [hv, hw]⟩)
        exact ⟨⟨out, true, nextId b⟩, c, by rw [ho]; rfl, hos, hg⟩

private theorem pick_total (X : JMat T) (l : Tree T) (hl : LeafOK X l)
    (hp : 1 ≤ X.nrows) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    ∃ v, (do
      let a ← featureAt X (if isConstLeaf l then 1 else leafFeat l) j
      pure (if isConstLeaf l then (if isConstLeaf l then leafVal l else JlScalar.zero) else a)) = .ok v := by
  by_cases hc : isConstLeaf l = true
  · obtain ⟨v, hv⟩ := feature_total X 1 j (by omega) hp hj1 hj2
    exact ⟨leafVal l, by simp [hc, hv]⟩
  · obtain ⟨v, hv⟩ := leaf_feature_total X l hl (by simp_all) j hj1 hj2
    exact ⟨v, by simp [hc, hv]⟩

private theorem branch0_total (cx : Ctx) (X : JMat T) (f g : List T → T) (s : Side)
    (l1 l2 l3 : Tree T) (b : Buf T) (k : Nat)
    (h1 : LeafOK X l1) (h2 : LeafOK X l2) (h3 : LeafOK X l3) (hp : 1 ≤ X.nrows)
    (h : Good X.ncols (k + 1 + 1) b) : Complete X k (branch0 cx X f g s l1 l2 l3 b) := by
  obtain ⟨cum, c, ha, hs, hg⟩ := getArray_good h
  simp only [branch0, ha, jl_ok_bind]
  split
  · exact ⟨⟨cum, false, nextId b⟩, c, rfl, hs, hg.mono (by omega)⟩
  · rw [chk_pick X l1 h1 hp, chk_pick X l2 h2 hp, chk_pick X l3 h3 hp]
    simp only [jl_ok_bind]
    let kernel : Nat → Jl T := fun j => do
          let x1 ← (do
            let a ← featureAt X (if isConstLeaf l1 = true then 1 else leafFeat l1) j
            pure (if isConstLeaf l1 = true then
              (if isConstLeaf l1 = true then leafVal l1 else JlScalar.zero) else a))
          let x2 ← (do
            let a ← featureAt X (if isConstLeaf l2 = true then 1 else leafFeat l2) j
            pure (if isConstLeaf l2 = true then
              (if isConstLeaf l2 = true then leafVal l2 else JlScalar.zero) else a))
          let x3 ← (do
            let a ← featureAt X (if isConstLeaf l3 = true then 1 else leafFeat l3) j
            pure (if isConstLeaf l3 = true then
              (if isConstLeaf l3 = true then leafVal l3 else JlScalar.zero) else a))
          pure (fused3 s cx.earlyExit f g x1 x2 x3)
    have hkernel : ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, kernel j = .ok v := by
      intro j hj1 hj2
      obtain ⟨v1, hv1⟩ := pick_total X l1 h1 hp j hj1 hj2
      obtain ⟨v2, hv2⟩ := pick_total X l2 h2 hp j hj1 hj2
      obtain ⟨v3, hv3⟩ := pick_total X l3 h3 hp j hj1 hj2
      exact ⟨fused3 s cx.earlyExit f g v1 v2 v3, by
        dsimp only [kernel]; rw [hv1]; simp only [jl_ok_bind]
        rw [hv2]; simp only [jl_ok_bind]; rw [hv3]; rfl⟩
    obtain ⟨out, ho, hout⟩ := simd_total X cum kernel hs hkernel
    have hbody : Complete X k (do
        let out ← simdWrite cum X.ncols kernel
        pure (⟨out, true, nextId b⟩, c)) :=
      ⟨⟨out, true, nextId b⟩, c, by simp [ho], hout, hg.mono (by omega)⟩
    cases s <;> simp only [retVIf] <;> split <;>
      (try apply retV_total _ _ _ _ _ _ hg) <;> exact hbody

private theorem checked_total (cx : Ctx) (X : JMat T) (b : Buf T) (k q : Nat)
    (ev : Buf T → Jl (ResultOk T × Buf T))
    (f : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T))
    (hkq : k ≤ q) (he : Complete X q (ev b))
    (hf : ∀ a id c, a.size = X.ncols → Good X.ncols q c → Complete X k (f a id c)) :
    Complete X k (checked cx ev f b) := by
  obtain ⟨r, c, hr, hs, hg⟩ := he
  simp only [checked, hr, jl_ok_bind]
  split
  · exact ⟨r, c, rfl, hs, hg.mono hkq⟩
  · split
    · exact ⟨⟨r.x, false, r.id⟩, c, rfl, hs, hg.mono hkq⟩
    · exact hf r.x r.id c hs hg

private theorem unfused1_total (cx : Ctx) (X : JMat T) (fop : Jl (List T → T))
    (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (k : Nat)
    (he : Complete X k (ev b)) (hop : ∃ f, fop = .ok f) :
    Complete X k (unfused1 cx fop ev b) := by
  obtain ⟨f, hf⟩ := hop
  unfold unfused1
  apply checked_total _ _ _ _ k _ _ (Nat.le_refl _) he
  intro a id c hs hg
  obtain ⟨out, ho, hos⟩ := degn_total X f [a] (by simp) (by simpa using hs)
  exact ⟨⟨out, true, id⟩, c, by simp only [hf, jl_ok_bind]; rw [ho]; rfl, hos, hg⟩

private theorem unfused2_total (cx : Ctx) (X : JMat T) (fop : Jl (List T → T))
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (k q : Nat)
    (hl : Complete X q (evL b)) (hkq : k ≤ q)
    (hr : ∀ c, Good X.ncols q c → Complete X k (evR c)) (hop : ∃ f, fop = .ok f) :
    Complete X k (unfused2 cx fop evL evR b) := by
  obtain ⟨f, hf⟩ := hop
  unfold unfused2
  apply checked_total _ _ _ _ q _ _ hkq hl
  intro a id c hs hg
  apply checked_total _ _ _ _ k _ _ (Nat.le_refl _) (hr c hg)
  intro a' id' c' hs' hg'
  obtain ⟨out, ho, hos⟩ := degn_total X f [a, a'] (by simp) (by simp_all)
  exact ⟨⟨out, true, id⟩, c', by simp only [hf, jl_ok_bind]; rw [ho]; rfl, hos, hg'⟩

private theorem constChildren_total (o : OpEnum T) (early : Bool) (cs : List (Tree T))
    (ih : ∀ t ∈ cs, ∃ r, constEval o t early = .ok r) : ∃ r, constEvalL o cs early = .ok r := by
  induction cs with
  | nil => exact ⟨.inr [], rfl⟩
  | cons t ts hi =>
    obtain ⟨⟨v, ok⟩, hv⟩ := ih t (by simp)
    simp only [constEvalL, hv, jl_ok_bind]
    split
    · exact ⟨.inl (v, ok), rfl⟩
    · obtain ⟨r, hr⟩ := hi (fun c hc => ih c (by simp [hc]))
      cases r <;> simp [hr]

private theorem constEval_total (o : OpEnum T) (early : Bool) (t : Tree T) (D nf : Nat)
    (hw : t.WF D o.nops nf) : ∃ r, constEval o t early = .ok r := by
  induction t using Tree.induction with
  | hc v => exact ⟨_, rfl⟩
  | hf f => exact ⟨_, rfl⟩
  | hb op cs ih =>
    simp only [Tree.WF] at hw
    obtain ⟨⟨hn, _, _⟩, ⟨hop, hnops, _⟩, hcs⟩ := hw
    obtain ⟨r, hr⟩ := constChildren_total o early cs (fun c hc => ih c hc (hcs c hc))
    obtain ⟨f, hlookup, hnif⟩ := nifOp_lookup o cs.length op hn hop hnops
    have hidx := idxOp_lookup o cs.length op f hn hlookup
    simp only [constEval, hr, jl_ok_bind]
    cases r with
    | inl r => exact ⟨r, rfl⟩
    | inr vs =>
      split <;> simp [hnif, hidx]

private theorem constPath_total (o : OpEnum T) (X : JMat T) (t : Tree T)
    (D : Nat) (b : Buf T) (k : Nat) (early : Bool) (hw : t.WF D o.nops X.nrows)
    (hg : Good X.ncols (k + 1) b) : Complete X k (constPath o X t b early) := by
  obtain ⟨⟨v, ok⟩, he⟩ := constEval_total o early t D X.nrows hw
  simp only [constPath, he]
  split
  · obtain ⟨a, c, ha, hs, hg'⟩ := getArray_good hg
    exact ⟨⟨a, false, nextId b⟩, c, by simp [ha], hs, hg'⟩
  · exact filled_total X v b k hg

private theorem deg1Dispatch_total (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (c : Tree T) (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (k : Nat)
    (hop : 1 ≤ op) (hops : op ≤ o.nops 1) (hwc : c.WF cx.D o.nops X.nrows)
    (hev : ∀ q a, Good X.ncols (q + c.size) a → Complete X q (ev a))
    (hg : Good X.ncols (k + 1 + c.size) b) :
    Complete X k (deg1Dispatch cx o X op c ev b) := by
  have hp := c.size_pos
  have h1 : Good X.ncols (k + 1) b := hg.mono (by omega)
  have he := hev k b (hg.mono (by omega))
  obtain ⟨f, hl, hf⟩ := nifOp_lookup o 1 op (by omega) hop hops
  have hi := idxOp_lookup o 1 op f (by omega) hl
  unfold deg1Dispatch
  dsimp only
  split
  · exact unfused1_total cx X _ ev b k he ⟨f, hi⟩
  · simp only [hf, jl_ok_bind]
    have hu := unfused1_total cx X (pure f) ev b k he ⟨f, rfl⟩
    cases c with
    | const v => exact hu
    | feature f => exact hu
    | branch lop cs =>
      simp only [Tree.WF] at hwc
      cases cs with
      | nil => exact hu
      | cons ll ls =>
        cases ls with
        | nil =>
          simp only
          split
          · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 1 lop (by omega) hwc.2.1.1 (by simpa using hwc.2.1.2.1)
            simp only [hgop, jl_ok_bind]
            apply deg1L1_total cx X f g ll b k _ h1
            exact leafOK_of_WF X o cx.D ll (hwc.2.2 ll (by simp)) (by simp_all only [Bool.and_eq_true])
          · exact hu
        | cons lr rs =>
          cases rs with
          | nil =>
            simp only
            split
            · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 lop (by omega) hwc.2.1.1 (by simpa using hwc.2.1.2.1)
              simp only [hgop, jl_ok_bind]
              apply deg1L2_total cx X f g ll lr b k _ _ h1
              · exact leafOK_of_WF X o cx.D ll (hwc.2.2 ll (by simp)) (by simp_all only [Bool.and_eq_true])
              · exact leafOK_of_WF X o cx.D lr (hwc.2.2 lr (by simp)) (by simp_all only [Bool.and_eq_true])
            · exact hu
          | cons z zs => exact hu

omit [JlScalar T] in
private theorem constList_iff (cs : List (Tree T)) :
    isConstantL cs = true ↔ ∀ c ∈ cs, isConstant c = true := by
  induction cs with
  | nil => simp [isConstantL]
  | cons c cs ih => simp [isConstantL, ih]

omit [JlScalar T] in
private theorem zeroRows_constant (o : OpEnum T) (D : Nat) (t : Tree T)
    (h : t.WF D o.nops 0) : isConstant t = true := by
  induction t using Tree.induction with
  | hc v => rfl
  | hf f => simp only [Tree.WF] at h; omega
  | hb op cs ih =>
    simp only [Tree.WF] at h
    simp only [isConstant]
    apply (constList_iff cs).2
    intro c hc
    exact ih c hc (h.2.2 c hc)

private theorem deg2Dispatch_total (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (l r : Tree T) (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (k : Nat)
    (hop : 1 ≤ op) (hops : op ≤ o.nops 2)
    (hwl : l.WF cx.D o.nops X.nrows) (hwr : r.WF cx.D o.nops X.nrows)
    (hp : 1 ≤ X.nrows)
    (hevL : ∀ q a, Good X.ncols (q + l.size) a → Complete X q (evL a))
    (hevR : ∀ q a, Good X.ncols (q + r.size) a → Complete X q (evR a))
    (hg : Good X.ncols (k + 1 + l.size + r.size) b) :
    Complete X k (deg2Dispatch cx o X op l r evL evR b) := by
  have hlpos := l.size_pos
  have hrpos := r.size_pos
  have h1 : Good X.ncols (k + 1) b := hg.mono (by omega)
  obtain ⟨f, hl, hf⟩ := nifOp_lookup o 2 op (by omega) hop hops
  have hi := idxOp_lookup o 2 op f (by omega) hl
  have hu (fop : Jl (List T → T)) (hfo : ∃ g, fop = .ok g) :
      Complete X k (unfused2 cx fop evL evR b) := by
    apply unfused2_total cx X fop evL evR b k (k + r.size)
    · exact hevL (k + r.size) b (hg.mono (by omega))
    · omega
    · exact hevR k
    · exact hfo
  unfold deg2Dispatch
  dsimp only
  split
  · exact hu _ ⟨f, hi⟩
  · simp only [hf, jl_ok_bind]
    have hr0 (hrleaf : isLeaf r = true) :
        Complete X k (checked cx evL (fun x id b => deg2R0 cx X f r x id b) b) := by
      apply checked_total cx X b k (k + 1) _ _ (by omega)
        (hevL (k + 1) b (hg.mono (by omega)))
      intro a id c hs hc
      exact leafWriteR_total cx X f r a id c k (leafOK_of_WF X o cx.D r hwr hrleaf) hs hc
    have hl0 (hlleaf : isLeaf l = true) :
        Complete X k (checked cx evR (fun x id b => deg2L0 cx X f l x id b) b) := by
      apply checked_total cx X b k (k + 1) _ _ (by omega)
        (hevR (k + 1) b (hg.mono (by omega)))
      intro a id c hs hc
      exact leafWrite_total cx X f l a id c k (leafOK_of_WF X o cx.D l hwl hlleaf) hs hc
    split
    · apply deg2L0R0_total cx X f l r b k
      · exact leafOK_of_WF X o cx.D l hwl (by simp_all only [Bool.and_eq_true])
      · exact leafOK_of_WF X o cx.D r hwr (by simp_all only [Bool.and_eq_true])
      · exact hg.mono (by omega)
    · split
      · have hrleaf : isLeaf r = true := by simp_all only [Bool.and_eq_true]
        cases l with
        | const v => exact hr0 hrleaf
        | feature q => exact hr0 hrleaf
        | branch lop cs =>
          simp only [Tree.WF] at hwl
          cases cs with
          | nil => exact hr0 hrleaf
          | cons ll ls =>
            cases ls with
            | nil => exact hr0 hrleaf
            | cons lr rs =>
              cases rs with
              | cons z zs => exact hr0 hrleaf
              | nil =>
                simp only
                split
                · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 lop (by omega) hwl.2.1.1 (by simpa using hwl.2.1.2.1)
                  simp only [hgop, jl_ok_bind]
                  apply branch0_total cx X f g .left ll lr r b k _ _ _ hp (hg.mono (by omega))
                  · exact leafOK_of_WF X o cx.D ll (hwl.2.2 ll (by simp)) (by simp_all only [Bool.and_eq_true])
                  · exact leafOK_of_WF X o cx.D lr (hwl.2.2 lr (by simp)) (by simp_all only [Bool.and_eq_true])
                  · exact leafOK_of_WF X o cx.D r hwr hrleaf
                · exact hr0 hrleaf
      · split
        · have hlleaf : isLeaf l = true := by simp_all only [Bool.and_eq_true]
          cases r with
          | const v => exact hl0 hlleaf
          | feature q => exact hl0 hlleaf
          | branch rop cs =>
            simp only [Tree.WF] at hwr
            cases cs with
            | nil => exact hl0 hlleaf
            | cons rl rs =>
              cases rs with
              | nil => exact hl0 hlleaf
              | cons rr rest =>
                cases rest with
                | cons z zs => exact hl0 hlleaf
                | nil =>
                  simp only
                  split
                  · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 rop (by omega) hwr.2.1.1 (by simpa using hwr.2.1.2.1)
                    simp only [hgop, jl_ok_bind]
                    apply branch0_total cx X f g .right l rl rr b k _ _ _ hp (hg.mono (by omega))
                    · exact leafOK_of_WF X o cx.D l hwl hlleaf
                    · exact leafOK_of_WF X o cx.D rl (hwr.2.2 rl (by simp)) (by simp_all only [Bool.and_eq_true])
                    · exact leafOK_of_WF X o cx.D rr (hwr.2.2 rr (by simp)) (by simp_all only [Bool.and_eq_true])
                  · exact hl0 hlleaf
        · exact hu _ ⟨f, rfl⟩

private def ChildrenGood (X : JMat T) (k : Nat) (cs : List (Tree T)) :
    ((ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)) → Prop
  | .inl (r, b) => r.x.size = X.ncols ∧ Good X.ncols k b
  | .inr (xs, b) => xs.length = cs.length ∧ (∀ p ∈ xs, p.1.size = X.ncols) ∧ Good X.ncols k b

private theorem children_total (cx : Ctx) (o : OpEnum T) (X : JMat T) (cs : List (Tree T))
    (ih : ∀ t ∈ cs, ∀ k b, Good X.ncols (k + t.size) b → Complete X k (evalT cx o X t b)) :
    ∀ k b, Good X.ncols (k + (cs.map Tree.size).sum) b →
      ∃ res, evalChildren cx o X cs b = .ok res ∧ ChildrenGood X k cs res := by
  induction cs with
  | nil => intro k b hg; exact ⟨.inr ([], b), rfl, rfl, by simp, hg⟩
  | cons t ts hi =>
    intro k b hg
    have hg' : Good X.ncols ((k + (ts.map Tree.size).sum) + t.size) b := by
      simpa [List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg
    obtain ⟨r, c, hr, hs, hc⟩ := ih t (by simp) (k + (ts.map Tree.size).sum) b hg'
    simp only [evalChildren, hr, jl_ok_bind]
    split
    · exact ⟨.inl (r, c), rfl, hs, hc.mono (by omega)⟩
    · split
      · exact ⟨.inl (⟨r.x, false, r.id⟩, c), rfl, hs, hc.mono (by omega)⟩
      · obtain ⟨res, he, ht⟩ := hi (fun t hm => ih t (by simp [hm])) k c hc
        simp only [he, jl_ok_bind]
        cases res with
        | inl p => exact ⟨.inl p, rfl, ht⟩
        | inr p =>
          rcases p with ⟨xs, d⟩
          refine ⟨.inr ((r.x, r.id) :: xs, d), rfl, ?_, ?_, ht.2.2⟩
          · simpa using congrArg Nat.succ ht.1
          · intro p hp
            cases hp with
            | head => exact hs
            | tail _ hm => exact ht.2.1 p hm

private theorem finish_total (o : OpEnum T) (X : JMat T) (cs : List (Tree T)) (op k : Nat)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T))
    (hcs : 1 ≤ cs.length) (hop : 1 ≤ op) (hops : op ≤ o.nops cs.length)
    (hg : ChildrenGood X k cs res) : Complete X k (degnFinish o cs.length op res) := by
  cases res with
  | inl p => rcases p with ⟨r, b⟩; exact ⟨r, b, rfl, hg⟩
  | inr p =>
    rcases p with ⟨xs, b⟩
    obtain ⟨f, _, hf⟩ := nifOp_lookup o cs.length op hcs hop hops
    have hne : xs.map Prod.fst ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_map, List.length_nil] at this
      have := hg.1
      omega
    obtain ⟨out, ho, hs⟩ := degn_total X f (xs.map Prod.fst) hne (by
      intro a hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact hg.2.1 p hp)
    exact ⟨⟨out, true, (xs.head?.map Prod.snd).getD .fresh⟩, b,
      by simp only [degnFinish, hf, jl_ok_bind]; rw [ho]; rfl, hs, hg.2.2⟩

private theorem eval_complete (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hw : t.WF cx.D o.nops X.nrows) :
    ∀ k b, Good X.ncols (k + t.size) b → Complete X k (evalT cx o X t b) := by
  induction t using Tree.induction with
  | hc v =>
    intro k b hg
    obtain ⟨c, hc, hgood⟩ := getFilled_good (k := k) v (by simpa only [Tree.size] using hg)
    exact ⟨⟨JVec.fill X.ncols v, !cx.earlyExit || valid v, nextId b⟩, c,
      by simp [evalT, hc], by simp [JVec.fill], hgood⟩
  | hf f =>
    intro k b hg
    simp only [Tree.WF] at hw
    simp only [Tree.size] at hg
    have hr := rowInb_canon o X f hw.1 hw.2.1
    obtain ⟨c, hc, hgood⟩ := getFeature_good X f (canon o X (.feature f)) hr hg
    exact ⟨⟨canon o X (.feature f), true, nextId b⟩, c,
      by simp [evalT, hc, chk_ok X f hw.1 hw.2.1], canon_size o X (.feature f), hgood⟩
  | hb op cs ih =>
    intro k b hg
    have hsize := (Tree.branch op cs).size_pos
    have h1 : Good X.ncols (k + 1) b := hg.mono (by omega)
    unfold evalT
    split
    · exact constPath_total o X (.branch op cs) cx.D b k cx.earlyExit hw h1
    · have hnon : isConstantL cs = false := by simp_all
      have hp : 1 ≤ X.nrows := by
        by_cases hzero : X.nrows = 0
        · have hconst := zeroRows_constant o cx.D (.branch op cs) (hzero ▸ hw)
          simp [isConstant, hnon] at hconst
        · omega
      simp only [Tree.WF] at hw
      have hchild : ∀ c ∈ cs, ∀ q a, Good X.ncols (q + c.size) a → Complete X q (evalT cx o X c a) :=
        fun c hc => ih c hc (hw.2.2 c hc)
      cases cs with
      | nil => simp at hw
      | cons c cs =>
        cases cs with
        | nil =>
          apply deg1Dispatch_total cx o X op c _ b k hw.2.1.1
            (by simpa using hw.2.1.2.1) (hw.2.2 c (by simp)) (hchild c (by simp))
          simpa [Tree.size, Nat.add_assoc] using hg
        | cons d ds =>
          cases ds with
          | nil =>
            apply deg2Dispatch_total cx o X op c d _ _ b k hw.2.1.1
              (by simpa using hw.2.1.2.1) (hw.2.2 c (by simp)) (hw.2.2 d (by simp)) hp
              (hchild c (by simp)) (hchild d (by simp))
            simpa [Tree.size, Nat.add_assoc] using hg
          | cons e es =>
            simp only
            have hd : cx.D ≠ 2 := by
              have := hw.1.2.1
              simp only [List.length_cons] at this
              omega
            simp only [hd, ↓reduceIte]
            obtain ⟨res, hr, hres⟩ := children_total cx o X (c :: d :: e :: es) hchild k b
              (hg.mono (by simp only [Tree.size]; omega))
            simp only [hr, jl_ok_bind]
            have hfinish := finish_total o X (c :: d :: e :: es) op k res
              (by simp) hw.2.1.1 hw.2.1.2.1 hres
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinish

theorem evalT_total (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (hw : t.WF cx.D o.nops X.nrows) (hb : BufOK X t b) :
    ∃ r b', evalT cx o X t b = .ok (r, b') := by
  obtain ⟨r, c, hr, _, _⟩ := eval_complete cx o X t hw 0 b (by simpa using bufOK_good hb)
  exact ⟨r, c, hr⟩

/-- Totality that leaves room for `k` more nodes in the buffer. -/
theorem evalT_total_room (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (k : Nat) (hw : t.WF cx.D o.nops X.nrows) (hb : Good X.ncols (k + t.size) b) :
    ∃ r b', evalT cx o X t b = .ok (r, b') ∧ Good X.ncols k b' := by
  obtain ⟨r, c, hr, _, hg⟩ := eval_complete cx o X t hw k b hb
  exact ⟨r, c, hr, hg⟩

/-- Totality with the output length: every successful call returns one value
per sample. -/
theorem evalT_total_size (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (hw : t.WF cx.D o.nops X.nrows) (hb : BufOK X t b) :
    ∃ r b', evalT cx o X t b = .ok (r, b') ∧ r.x.size = X.ncols := by
  obtain ⟨r, c, hr, hs, _⟩ := eval_complete cx o X t hw 0 b (by simpa using bufOK_good hb)
  exact ⟨r, c, hr, hs⟩

theorem evalTotal_proof : evalTotal := by
  intro T inst ext impl D early fused o X t _ _ hw
  obtain ⟨r, b, hr⟩ := evalT_total ⟨early, fused, D⟩ o X t .none hw (Or.inl rfl)
  exact ⟨(r.x, r.ok && (!early || isValidArray r.x)), by simp [evalTreeArray, plainCtx, evalArr, hr]⟩

theorem evalSmallBufferFits_proof : evalSmallBufferFits := by
  intro T inst ext impl D early fused o X t A i _ hw hc hi
  obtain ⟨r, b, hr⟩ := evalT_total ⟨early, fused, D⟩ o X t (.mat A i) hw
    (Or.inr (Or.inr ⟨A, i, rfl, hc, hi⟩))
  exact ⟨(r.x, r.ok && (!early || isValidArray r.x)), by simp [evalTreeArray, plainCtx, evalArr, hr]⟩

private instance : JlScalar Nat where
  valid := fun _ => true
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  isNumber := true
  isFloat := false
  floatLike := false
  undef := 0
  invalid? := none

private def smallInput : JMat Nat := ⟨1, 1, #[7], rfl⟩
private def noOps : OpEnum Nat := ⟨[]⟩
private def unusedExtensions : ExtImpl Nat := ⟨fun _ _ => .error .boundsError⟩

example : (Tree.const 7).WF 2 noOps.nops smallInput.nrows ∧
    BufOK smallInput (.const 7) .none ∧
    ∃ r b, evalT {} noOps smallInput (.const 7) .none = .ok (r, b) := by
  exact ⟨by simp [Tree.WF], Or.inl rfl,
    evalT_total {} noOps smallInput (.const 7) .none (by simp [Tree.WF]) (Or.inl rfl)⟩

example : 1 ≤ smallInput.ncols ∧ (Tree.const 7).WF 2 noOps.nops 65535 ∧
    (Tree.const 7).WF 2 noOps.nops smallInput.nrows ∧
    ∃ r, evalTreeArray {} unusedExtensions 2 (.const 7) smallInput noOps
      (plainCtx true true .none) = .ok r := by
  exact ⟨by decide, by simp [Tree.WF], by simp [Tree.WF],
    evalTotal_proof Nat {} unusedExtensions 2 true true noOps smallInput (.const 7)
      (by decide) (by simp [Tree.WF]) (by simp [Tree.WF])⟩

example : 1 ≤ smallInput.ncols ∧ (Tree.const 7).WF 2 noOps.nops smallInput.nrows ∧
    smallInput.ncols = smallInput.ncols ∧ 0 + (Tree.const 7).size ≤ smallInput.nrows ∧
    ∃ r, evalTreeArray {} unusedExtensions 2 (.const 7) smallInput noOps
      (plainCtx true true (.mat smallInput 0)) = .ok r := by
  exact ⟨by decide, by simp [Tree.WF], rfl, by simp [Tree.size, smallInput],
    evalSmallBufferFits_proof Nat {} unusedExtensions 2 true true noOps smallInput (.const 7)
      smallInput 0 (by decide) (by simp [Tree.WF]) rfl (by simp [Tree.size, smallInput])⟩

end DynExpr.Eval
