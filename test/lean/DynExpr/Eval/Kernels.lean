import DynExpr.Eval.Alloc

/-!
Correctness of the fused kernels, the unfused paths and the constant-tree
shortcut when every intermediate value is valid.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- A leaf whose feature index is in range. -/
def LeafOK (X : JMat T) : Tree T → Prop
  | .const _ => True
  | .feature f => 1 ≤ f ∧ f ≤ X.nrows
  | .branch .. => False

theorem LeafOK.of_wf {X : JMat T} {D : Nat} {nops : Nat → Nat} (ℓ : Tree T)
    (hl : isLeaf ℓ = true) (hw : ℓ.WF D nops X.nrows) : LeafOK X ℓ := by
  cases ℓ with
  | const _ => trivial
  | feature f => simp only [Tree.WF] at hw; exact ⟨hw.1, hw.2.1⟩
  | branch _ _ => simp [isLeaf] at hl

@[simp] theorem cv_const (o : OpEnum T) (X : JMat T) (a : T) (j : Nat) :
    cv o X (.const a) j = a := by
  simp [cv, vx, Tree.denote]

/-- The value a kernel reads for a non-constant leaf. -/
theorem leaf_read (o : OpEnum T) (X : JMat T) (ℓ : Tree T) (hl : LeafOK X ℓ)
    (hc : isConstLeaf ℓ = false) (j : Nat) (hj : j < X.ncols) :
    featureAt X (leafFeat ℓ) (j + 1) = .ok (cv o X ℓ j) := by
  cases ℓ with
  | const _ => simp [isConstLeaf] at hc
  | feature f => exact featureAt_cv o X f j hl.1 hl.2 hj
  | branch _ _ => exact hl.elim

theorem leaf_const (o : OpEnum T) (X : JMat T) (ℓ : Tree T) (hc : isConstLeaf ℓ = true) (j : Nat) :
    leafVal ℓ = cv o X ℓ j := by
  cases ℓ with
  | const a => simp [leafVal]
  | _ => simp [isConstLeaf] at hc

theorem retV_valid (cx : Ctx) (X : JMat T) (v : T) (k : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) (hv : valid v = true) : retV cx X v k b = k b := by
  simp [retV, hv]

theorem retVIf_pass (cx : Ctx) (X : JMat T) (c : Bool) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (hv : c = true → valid v = true) :
    retVIf cx X c v k b = k b := by
  cases c
  · rfl
  · simp [retVIf, retV, hv rfl]

/-- `checkbounds` passes for an in-range feature leaf. -/
theorem leaf_chk (X : JMat T) (ℓ : Tree T) (hl : LeafOK X ℓ) (hc : isConstLeaf ℓ = false) :
    chk X (leafFeat ℓ) = .ok () := by
  cases ℓ with
  | const _ => simp [isConstLeaf] at hc
  | feature f => exact chk_ok X f hl.1 hl.2
  | branch _ _ => exact hl.elim

/-- `checkbounds` in `deg2_branch0_eval`, where constant leaves use feature `1`. -/
theorem pick_chk (X : JMat T) (ℓ : Tree T) (hl : LeafOK X ℓ) (h1 : 1 ≤ X.nrows) :
    chk X (if isConstLeaf ℓ = true then 1 else leafFeat ℓ) = .ok () := by
  cases hc : isConstLeaf ℓ
  · simpa using leaf_chk X ℓ hl hc
  · simpa using chk_ok X 1 (Nat.le_refl 1) h1

omit [JlScalar T] in
theorem isConstant_leaf (ℓ : Tree T) (hl : isLeaf ℓ = true) : isConstant ℓ = isConstLeaf ℓ := by
  cases ℓ <;> simp_all [isLeaf, isConstant, isConstLeaf]

section kernels
variable (cx : Ctx) (o : OpEnum T) (X : JMat T)

/-- Leaves with at least one feature, valid at every sample. -/
structure Leaves2 (l r : Tree T) : Prop where
  okl : LeafOK X l
  okr : LeafOK X r
  nc : ¬ (isConstLeaf l = true ∧ isConstLeaf r = true)
  vl : ∀ j, j < X.ncols → valid (cv o X l j) = true
  vr : ∀ j, j < X.ncols → valid (cv o X r j) = true

theorem deg2L0R0_ok (f : List T → T) (l r : Tree T) (hL : Leaves2 o X l r) (hn : 1 ≤ X.ncols)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + 1) b) :
    ∃ id b', deg2L0R0 cx X f l r b =
        .ok (⟨((List.range X.ncols).map (fun j => f [cv o X l j, cv o X r j])).toArray, true, id⟩, b') ∧
      Good X.ncols k b' := by
  obtain ⟨cum, b1, hga, hsz, hgood⟩ := getArray_good hb
  refine ⟨nextId b, b1, ?_, hgood⟩
  unfold deg2L0R0
  cases hcl : isConstLeaf l <;> cases hcr : isConstLeaf r
  · -- feature, feature
    have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v1 ← featureAt X (leafFeat l) j
        let v2 ← featureAt X (leafFeat r) j
        pure (f [v1, v2]))
      (fun j => f [cv o X l j, cv o X r j]) hsz (by
        intro j hj
        simp [leaf_read o X l hL.okl hcl j hj, leaf_read o X r hL.okr hcr j hj])
    simp only [jl_pure] at hw
    simp [hga, hw, leaf_chk X l hL.okl hcl, leaf_chk X r hL.okr hcr]
  · -- feature, constant
    have hc := leaf_const o X r hcr 0
    have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v ← featureAt X (leafFeat l) j
        pure (f [v, leafVal r]))
      (fun j => f [cv o X l j, cv o X r j]) hsz (by
        intro j hj
        simp [leaf_read o X l hL.okl hcl j hj, leaf_const o X r hcr j])
    have hv : valid (leafVal r) = true := by rw [hc]; exact hL.vr 0 hn
    simp only [jl_pure] at hw
    simp [hga, retV, hv, hw, leaf_chk X l hL.okl hcl]
  · -- constant, feature
    have hc := leaf_const o X l hcl 0
    have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v ← featureAt X (leafFeat r) j
        pure (f [leafVal l, v]))
      (fun j => f [cv o X l j, cv o X r j]) hsz (by
        intro j hj
        simp [leaf_read o X r hL.okr hcr j hj, leaf_const o X l hcl j])
    have hv : valid (leafVal l) = true := by rw [hc]; exact hL.vl 0 hn
    simp only [jl_pure] at hw
    simp [hga, retV, hv, hw, leaf_chk X r hL.okr hcr]
  · exact absurd ⟨hcl, hcr⟩ hL.nc

theorem deg1L2_ok (f fl : List T → T) (ll lr : Tree T) (hL : Leaves2 o X ll lr)
    (hin : ∀ j, j < X.ncols → valid (fl [cv o X ll j, cv o X lr j]) = true) (hn : 1 ≤ X.ncols)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + 1) b) :
    ∃ id b', deg1L2 cx X f fl ll lr b =
        .ok (⟨((List.range X.ncols).map
          (fun j => f [fl [cv o X ll j, cv o X lr j]])).toArray, true, id⟩, b') ∧
      Good X.ncols k b' := by
  obtain ⟨cum, b1, hga, hsz, hgood⟩ := getArray_good hb
  refine ⟨nextId b, b1, ?_, hgood⟩
  unfold deg1L2
  cases hcl : isConstLeaf ll <;> cases hcr : isConstLeaf lr
  · have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v1 ← featureAt X (leafFeat ll) j
        let v2 ← featureAt X (leafFeat lr) j
        pure (post cx.earlyExit f (fl [v1, v2])))
      (fun j => f [fl [cv o X ll j, cv o X lr j]]) hsz (by
        intro j hj
        simp [leaf_read o X ll hL.okl hcl j hj, leaf_read o X lr hL.okr hcr j hj, post, hin j hj])
    simp only [jl_pure] at hw
    simp [hga, hw, leaf_chk X ll hL.okl hcl, leaf_chk X lr hL.okr hcr]
  · have hc := leaf_const o X lr hcr 0
    have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v ← featureAt X (leafFeat ll) j
        pure (post cx.earlyExit f (fl [v, leafVal lr])))
      (fun j => f [fl [cv o X ll j, cv o X lr j]]) hsz (by
        intro j hj
        have := hin j hj
        simp [leaf_read o X ll hL.okl hcl j hj, leaf_const o X lr hcr j, post, this])
    have hv : valid (leafVal lr) = true := by rw [hc]; exact hL.vr 0 hn
    simp only [jl_pure] at hw
    simp [hga, retV, hv, hw, leaf_chk X ll hL.okl hcl]
  · have hc := leaf_const o X ll hcl 0
    have hw := simdWrite_eq cum X.ncols
      (fun j => do
        let v ← featureAt X (leafFeat lr) j
        pure (post cx.earlyExit f (fl [leafVal ll, v])))
      (fun j => f [fl [cv o X ll j, cv o X lr j]]) hsz (by
        intro j hj
        have := hin j hj
        simp [leaf_read o X lr hL.okr hcr j hj, leaf_const o X ll hcl j, post, this])
    have hv : valid (leafVal ll) = true := by rw [hc]; exact hL.vl 0 hn
    simp only [jl_pure] at hw
    simp [hga, retV, hv, hw, leaf_chk X lr hL.okr hcr]
  · exact absurd ⟨hcl, hcr⟩ hL.nc

theorem deg1L1_ok (f fl : List T → T) (ll : Tree T) (hl : LeafOK X ll)
    (hc : isConstLeaf ll = false)
    (hin : ∀ j, j < X.ncols → valid (fl [cv o X ll j]) = true)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + 1) b) :
    ∃ id b', deg1L1 cx X f fl ll b =
        .ok (⟨((List.range X.ncols).map (fun j => f [fl [cv o X ll j]])).toArray, true, id⟩, b') ∧
      Good X.ncols k b' := by
  obtain ⟨cum, b1, hga, hsz, hgood⟩ := getArray_good hb
  refine ⟨nextId b, b1, ?_, hgood⟩
  have hw := simdWrite_eq cum X.ncols
    (fun j => do
      let v ← featureAt X (leafFeat ll) j
      pure (post cx.earlyExit f (fl [v])))
    (fun j => f [fl [cv o X ll j]]) hsz (by
      intro j hj
      simp [leaf_read o X ll hl hc j hj, post, hin j hj])
  unfold deg1L1
  simp only [jl_pure] at hw
  simp [hc, hga, hw, leaf_chk X ll hl hc]

/-- In-place `op(cumulator, leaf)` on a canonical cumulator. -/
theorem deg2R0_ok (f : List T → T) (c r : Tree T) (hr : LeafOK X r) (hn : 1 ≤ X.ncols)
    (hvr : ∀ j, j < X.ncols → valid (cv o X r j) = true) (cid : Ident) (b : Buf T) :
    deg2R0 cx X f r (canon o X c) cid b =
      .ok (⟨((List.range X.ncols).map (fun j => f [cv o X c j, cv o X r j])).toArray, true, cid⟩, b) := by
  unfold deg2R0
  cases hcr : isConstLeaf r
  · have hm := inplaceMap_eq (canon o X c)
      (fun j x => do
        let v ← featureAt X (leafFeat r) j
        pure (f [x, v]))
      (fun j => f [cv o X c j, cv o X r j]) (by
        intro j hj
        rw [canon_size] at hj
        simp [leaf_read o X r hr hcr j hj, canon_getD o X c j hj])
    rw [canon_size] at hm
    simp only [jl_pure] at hm
    simp [hm, leaf_chk X r hr hcr]
  · have hv : valid (leafVal r) = true := by rw [leaf_const o X r hcr 0]; exact hvr 0 hn
    have hm := inplaceMap_eq (canon o X c)
      (fun _ x => pure (f [x, leafVal r]))
      (fun j => f [cv o X c j, cv o X r j]) (by
        intro j hj
        rw [canon_size] at hj
        simp [leaf_const o X r hcr j, canon_getD o X c j hj])
    rw [canon_size] at hm
    simp only [jl_pure] at hm
    simp [retV, hv, hm]

/-- In-place `op(leaf, cumulator)` on a canonical cumulator. -/
theorem deg2L0_ok (f : List T → T) (l c : Tree T) (hl : LeafOK X l) (hn : 1 ≤ X.ncols)
    (hvl : ∀ j, j < X.ncols → valid (cv o X l j) = true) (cid : Ident) (b : Buf T) :
    deg2L0 cx X f l (canon o X c) cid b =
      .ok (⟨((List.range X.ncols).map (fun j => f [cv o X l j, cv o X c j])).toArray, true, cid⟩, b) := by
  unfold deg2L0
  cases hcl : isConstLeaf l
  · have hm := inplaceMap_eq (canon o X c)
      (fun j x => do
        let v ← featureAt X (leafFeat l) j
        pure (f [v, x]))
      (fun j => f [cv o X l j, cv o X c j]) (by
        intro j hj
        rw [canon_size] at hj
        simp [leaf_read o X l hl hcl j hj, canon_getD o X c j hj])
    rw [canon_size] at hm
    simp only [jl_pure] at hm
    simp [hm, leaf_chk X l hl hcl]
  · have hv : valid (leafVal l) = true := by rw [leaf_const o X l hcl 0]; exact hvl 0 hn
    have hm := inplaceMap_eq (canon o X c)
      (fun _ x => pure (f [leafVal l, x]))
      (fun j => f [cv o X l j, cv o X c j]) (by
        intro j hj
        rw [canon_size] at hj
        simp [leaf_const o X l hcl j, canon_getD o X c j hj])
    rw [canon_size] at hm
    simp only [jl_pure] at hm
    simp [retV, hv, hm]

/-- A leaf value used by `deg2_branch0_eval` (`ifelse` with feature `1` for constants). -/
theorem pick_ok (ℓ : Tree T) (hl : LeafOK X ℓ) (h1 : 1 ≤ X.nrows) (j : Nat) (hj : j < X.ncols) :
    (do
      let a ← featureAt X (if isConstLeaf ℓ = true then 1 else leafFeat ℓ) (j + 1)
      pure (if isConstLeaf ℓ = true then (if isConstLeaf ℓ = true then leafVal ℓ else JlScalar.zero)
        else a) : Jl T) = .ok (cv o X ℓ j) := by
  cases hc : isConstLeaf ℓ
  · simp [leaf_read o X ℓ hl hc j hj]
  · simp [featureAt_cv o X 1 j (Nat.le_refl 1) h1 hj, leaf_const o X ℓ hc j]

/-- Three leaves with at least one feature, valid at every sample. -/
structure Leaves3 (l1 l2 l3 : Tree T) : Prop where
  ok1 : LeafOK X l1
  ok2 : LeafOK X l2
  ok3 : LeafOK X l3
  nc : ¬ (isConstLeaf l1 = true ∧ isConstLeaf l2 = true ∧ isConstLeaf l3 = true)
  v1 : ∀ j, j < X.ncols → valid (cv o X l1 j) = true
  v2 : ∀ j, j < X.ncols → valid (cv o X l2 j) = true
  v3 : ∀ j, j < X.ncols → valid (cv o X l3 j) = true

theorem Leaves3.nrows {l1 l2 l3 : Tree T} (h : Leaves3 o X l1 l2 l3) : 1 ≤ X.nrows := by
  have key : ∀ ℓ : Tree T, LeafOK X ℓ → isConstLeaf ℓ = false → 1 ≤ X.nrows := by
    intro ℓ hl hc
    cases ℓ with
    | feature f => exact Nat.le_trans hl.1 hl.2
    | const _ => simp [isConstLeaf] at hc
    | branch _ _ => exact hl.elim
  cases h1 : isConstLeaf l1
  · exact key l1 h.ok1 h1
  cases h2 : isConstLeaf l2
  · exact key l2 h.ok2 h2
  cases h3 : isConstLeaf l3
  · exact key l3 h.ok3 h3
  exact absurd ⟨h1, h2, h3⟩ h.nc

theorem leafBad_false (ℓ : Tree T) (hn : 1 ≤ X.ncols)
    (hv : ∀ j, j < X.ncols → valid (cv o X ℓ j) = true) :
    (cx.earlyExit && isConstLeaf ℓ && !valid (leafVal ℓ)) = false := by
  cases hc : isConstLeaf ℓ
  · simp
  · rw [leaf_const o X ℓ hc 0, hv 0 hn]; simp

theorem branch0_left_ok (f g : List T → T) (ll lr r : Tree T) (hL : Leaves3 o X ll lr r)
    (hin : ∀ j, j < X.ncols → valid (g [cv o X ll j, cv o X lr j]) = true) (hn : 1 ≤ X.ncols)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + 1) b) :
    ∃ id b', branch0 cx X f g .left ll lr r b =
        .ok (⟨((List.range X.ncols).map
          (fun j => f [g [cv o X ll j, cv o X lr j], cv o X r j])).toArray, true, id⟩, b') ∧
      Good X.ncols k b' := by
  obtain ⟨cum, b1, hga, hsz, hgood⟩ := getArray_good hb
  refine ⟨nextId b, b1, ?_, hgood⟩
  have h1 := hL.nrows
  have hw := simdWrite_eq cum X.ncols
    (fun j => do
      let x1 ← (do
        let a ← featureAt X (if isConstLeaf ll = true then 1 else leafFeat ll) j
        pure (if isConstLeaf ll = true then
          (if isConstLeaf ll = true then leafVal ll else JlScalar.zero) else a))
      let x2 ← (do
        let a ← featureAt X (if isConstLeaf lr = true then 1 else leafFeat lr) j
        pure (if isConstLeaf lr = true then
          (if isConstLeaf lr = true then leafVal lr else JlScalar.zero) else a))
      let x3 ← (do
        let a ← featureAt X (if isConstLeaf r = true then 1 else leafFeat r) j
        pure (if isConstLeaf r = true then
          (if isConstLeaf r = true then leafVal r else JlScalar.zero) else a))
      pure (fused3 .left cx.earlyExit f g x1 x2 x3))
    (fun j => f [g [cv o X ll j, cv o X lr j], cv o X r j]) hsz (by
      intro j hj
      rw [pick_ok o X ll hL.ok1 h1 j hj]
      simp only [jl_ok_bind]
      rw [pick_ok o X lr hL.ok2 h1 j hj]
      simp only [jl_ok_bind]
      rw [pick_ok o X r hL.ok3 h1 j hj]
      simp [fused3, hin j hj, hL.v3 j hj])
  unfold branch0
  simp only [hga, jl_ok_bind, leafBad_false cx o X ll hn hL.v1, leafBad_false cx o X lr hn hL.v2,
    leafBad_false cx o X r hn hL.v3, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    pick_chk X ll hL.ok1 h1, pick_chk X lr hL.ok2 h1, pick_chk X r hL.ok3 h1, jl_ok_bind]
  rw [retVIf_pass cx X _ _ _ _ (fun hc => by
    simp only [Bool.and_eq_true] at hc
    simp only [hc.1, hc.2, ↓reduceIte]
    rw [leaf_const o X ll hc.1 0, leaf_const o X lr hc.2 0]
    exact hin 0 hn)]
  rw [hw]
  rfl

theorem branch0_right_ok (f g : List T → T) (l rl rr : Tree T) (hL : Leaves3 o X l rl rr)
    (hin : ∀ j, j < X.ncols → valid (g [cv o X rl j, cv o X rr j]) = true) (hn : 1 ≤ X.ncols)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + 1) b) :
    ∃ id b', branch0 cx X f g .right l rl rr b =
        .ok (⟨((List.range X.ncols).map
          (fun j => f [cv o X l j, g [cv o X rl j, cv o X rr j]])).toArray, true, id⟩, b') ∧
      Good X.ncols k b' := by
  obtain ⟨cum, b1, hga, hsz, hgood⟩ := getArray_good hb
  refine ⟨nextId b, b1, ?_, hgood⟩
  have h1 := hL.nrows
  have hw := simdWrite_eq cum X.ncols
    (fun j => do
      let x1 ← (do
        let a ← featureAt X (if isConstLeaf l = true then 1 else leafFeat l) j
        pure (if isConstLeaf l = true then
          (if isConstLeaf l = true then leafVal l else JlScalar.zero) else a))
      let x2 ← (do
        let a ← featureAt X (if isConstLeaf rl = true then 1 else leafFeat rl) j
        pure (if isConstLeaf rl = true then
          (if isConstLeaf rl = true then leafVal rl else JlScalar.zero) else a))
      let x3 ← (do
        let a ← featureAt X (if isConstLeaf rr = true then 1 else leafFeat rr) j
        pure (if isConstLeaf rr = true then
          (if isConstLeaf rr = true then leafVal rr else JlScalar.zero) else a))
      pure (fused3 .right cx.earlyExit f g x1 x2 x3))
    (fun j => f [cv o X l j, g [cv o X rl j, cv o X rr j]]) hsz (by
      intro j hj
      rw [pick_ok o X l hL.ok1 h1 j hj]
      simp only [jl_ok_bind]
      rw [pick_ok o X rl hL.ok2 h1 j hj]
      simp only [jl_ok_bind]
      rw [pick_ok o X rr hL.ok3 h1 j hj]
      simp [fused3, hin j hj, hL.v1 j hj])
  unfold branch0
  simp only [hga, jl_ok_bind, leafBad_false cx o X l hn hL.v1, leafBad_false cx o X rl hn hL.v2,
    leafBad_false cx o X rr hn hL.v3, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    pick_chk X l hL.ok1 h1, pick_chk X rl hL.ok2 h1, pick_chk X rr hL.ok3 h1, jl_ok_bind]
  rw [retVIf_pass cx X _ _ _ _ (fun hc => by
    simp only [Bool.and_eq_true] at hc
    simp only [hc.1, hc.2, ↓reduceIte]
    rw [leaf_const o X rl hc.1 0, leaf_const o X rr hc.2 0]
    exact hin 0 hn)]
  rw [hw]
  rfl

/-- A checked child evaluation that succeeds with a valid canonical output
continues with that output. -/
theorem checked_ok (ev : Buf T → Jl (ResultOk T × Buf T)) (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T))
    (b b1 : Buf T) (c : Tree T) (id : Ident) (hA : ArrayValidSound T)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) c)
    (hev : ev b = .ok (⟨canon o X c, true, id⟩, b1)) :
    checked cx ev k b = k (canon o X c) id b1 := by
  simp [checked, hev, canon_isValid o X c hA hv]

end kernels

mutual
/-- `is_constant` trees denote the same value under every feature assignment. -/
theorem const_indep (o : OpEnum T) (x y : Nat → Option T) :
    ∀ t : Tree T, isConstant t = true → t.denote o x = t.denote o y
  | .const _, _ => by simp [Tree.denote]
  | .feature _, h => by simp [isConstant] at h
  | .branch op cs, h => by
    have hl := const_indepL o x y cs (by simpa [isConstant] using h)
    simp [Tree.denote, hl]
theorem const_indepL (o : OpEnum T) (x y : Nat → Option T) :
    ∀ cs : List (Tree T), isConstantL cs = true →
      cs.mapM (Tree.denote o x) = cs.mapM (Tree.denote o y)
  | [], _ => rfl
  | c :: cs, h => by
    simp only [isConstantL, Bool.and_eq_true] at h
    simp [List.mapM_cons, const_indep o x y c h.1, const_indepL o x y cs h.2]
end

mutual
/-- `dispatch_constant_tree` computes the denotation with flag true when every
node is valid. -/
theorem constEval_valid (o : OpEnum T) (x : Nat → Option T) (early : Bool) {D nf : Nat} :
    ∀ t : Tree T, t.WF D o.nops nf → AllValid o x t → isConstant t = true →
      constEval o t early = .ok (vx o x t, true)
  | .const v, _, hv, _ => by
    have := AllValid.valid o x (.const v) hv
    simp [constEval, vx, Tree.denote] at this ⊢
    exact this
  | .feature _, _, _, h => by simp [isConstant] at h
  | .branch op cs, hw, hv, hc => by
    simp only [Tree.WF] at hw
    obtain ⟨⟨hl1, _, _⟩, ⟨ho1, ho2, _⟩, hcs⟩ := hw
    obtain ⟨g, hg, hnif⟩ := nifOp_lookup o cs.length op hl1 ho1 ho2
    have hch := AllValid.children o x op cs hv
    have hlist := constEvalL_valid o x early cs hcs hch (by simpa [isConstant] using hc)
    have hvx := vx_branch o x op cs g hg (fun c hc => AllValid.some o x c (hch c hc))
    have hval := AllValid.valid o x _ hv
    rw [hvx] at hval
    rw [constEval, hlist]
    by_cases hlim : operatorLimit < (opsOf o cs.length).length
    · simp [hlim, idxOp_lookup o cs.length op g hl1 hg, hvx, hval]
    · simp [hlim, hnif, hvx, hval]
theorem constEvalL_valid (o : OpEnum T) (x : Nat → Option T) (early : Bool) {D nf : Nat} :
    ∀ cs : List (Tree T), (∀ c ∈ cs, c.WF D o.nops nf) → (∀ c ∈ cs, AllValid o x c) →
      isConstantL cs = true → constEvalL o cs early = .ok (.inr (cs.map (vx o x)))
  | [], _, _, _ => rfl
  | c :: cs, hw, hv, hc => by
    simp only [isConstantL, Bool.and_eq_true] at hc
    have h1 := constEval_valid o x early c (hw c (by simp)) (hv c (by simp)) hc.1
    have h2 := constEvalL_valid o x early cs (fun c' h => hw c' (by simp [h]))
      (fun c' h => hv c' (by simp [h])) hc.2
    rw [constEvalL, h1]
    simp [h2]
end

end DynExpr.Eval
