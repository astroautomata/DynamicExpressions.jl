import DynExpr.Eval.Kernels

/-!
Main correctness theorem: with every intermediate valid, `_eval_tree_array`
returns the canonical output (the denotation at every sample) with flag
true, for every `early_exit`/`use_fused` setting and every buffer with enough
slots.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

section unfused
variable (cx : Ctx) (o : OpEnum T) (X : JMat T)

theorem unfused1_ok (fop : Jl (List T → T)) (g : List T → T) (evC : Buf T → Jl (ResultOk T × Buf T))
    (b b1 : Buf T) (c : Tree T) (id : Ident) (hA : ArrayValidSound T)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) c)
    (hev : evC b = .ok (⟨canon o X c, true, id⟩, b1)) (hf : fop = .ok g) :
    unfused1 cx fop evC b =
      .ok (⟨((List.range X.ncols).map (fun j => g [cv o X c j])).toArray, true, id⟩, b1) := by
  unfold unfused1
  rw [checked_ok cx o X evC _ b b1 c id hA hv hev]
  have hd := degnEval_canon o X g [c] (by simp)
  simp only [List.map_cons, List.map_nil] at hd
  simp [hf, hd]

theorem unfused2_ok (fop : Jl (List T → T)) (g : List T → T)
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b b1 b2 : Buf T) (l r : Tree T) (idl idr : Ident)
    (hA : ArrayValidSound T)
    (hvl : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) l)
    (hvr : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) r)
    (hevl : evL b = .ok (⟨canon o X l, true, idl⟩, b1))
    (hevr : evR b1 = .ok (⟨canon o X r, true, idr⟩, b2)) (hf : fop = .ok g) :
    unfused2 cx fop evL evR b =
      .ok (⟨((List.range X.ncols).map
        (fun j => g [cv o X l j, cv o X r j])).toArray, true, idl⟩, b2) := by
  unfold unfused2
  rw [checked_ok cx o X evL _ b b1 l idl hA hvl hevl]
  rw [checked_ok cx o X evR _ b1 b2 r idr hA hvr hevr]
  have hd := degnEval_canon o X g [l, r] (by simp)
  simp only [List.map_cons, List.map_nil] at hd
  simp [hf, hd]

end unfused

/-- Hypotheses available for a child in the main induction. -/
def ChildOK (cx : Ctx) (o : OpEnum T) (X : JMat T) (c : Tree T) : Prop :=
  c.WF cx.D o.nops X.nrows ∧ (∀ j, j < X.ncols → AllValid o (col X (j + 1)) c) ∧
    ∀ k (b : Buf T), Good X.ncols (k + c.size) b →
      ∃ id b', evalT cx o X c b = .ok (⟨canon o X c, true, id⟩, b') ∧ Good X.ncols k b'

theorem leaves2_of (o : OpEnum T) (X : JMat T) {D : Nat} (l r : Tree T)
    (hl : isLeaf l = true) (hr : isLeaf r = true)
    (hwl : l.WF D o.nops X.nrows) (hwr : r.WF D o.nops X.nrows)
    (hnc : (isConstant l && isConstant r) = false)
    (hvl : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) l)
    (hvr : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) r) : Leaves2 o X l r where
  okl := LeafOK.of_wf l hl hwl
  okr := LeafOK.of_wf r hr hwr
  nc := by
    rw [isConstant_leaf l hl, isConstant_leaf r hr] at hnc
    intro ⟨h1, h2⟩; simp [h1, h2] at hnc
  vl := fun j hj => AllValid.valid o _ l (hvl j hj)
  vr := fun j hj => AllValid.valid o _ r (hvr j hj)

theorem deg1_case (cx : Ctx) (o : OpEnum T) (X : JMat T) (hA : ArrayValidSound T)
    (hn : 1 ≤ X.ncols) (op : Nat) (c : Tree T)
    (hwf : (Tree.branch op [c]).WF cx.D o.nops X.nrows)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) (.branch op [c]))
    (hnc : isConstant c = false) (ih : ChildOK cx o X c)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + (Tree.branch op [c]).size) b) :
    ∃ id b', deg1Dispatch cx o X op c (evalT cx o X c) b =
        .ok (⟨canon o X (.branch op [c]), true, id⟩, b') ∧ Good X.ncols k b' := by
  obtain ⟨hcw, hcv, hce⟩ := ih
  have hwf' := hwf
  simp only [Tree.WF] at hwf'
  obtain ⟨⟨hl1, _, _⟩, ⟨ho1, ho2, _⟩, _⟩ := hwf'
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at ho2 hl1
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 1 op (Nat.le_refl 1) ho1 ho2
  have hch : ∀ j, j < X.ncols → ∀ c' ∈ [c], AllValid o (col X (j + 1)) c' := by
    intro j hj c' hc'; simp at hc'; subst hc'; exact hcv j hj
  have hcanon := canon_branch o X op [c] g hg hch
  simp only [List.map_cons, List.map_nil] at hcanon
  have hsize : (Tree.branch op [c]).size = 1 + c.size := by simp
  rw [hsize] at hb
  obtain ⟨id, b1, hev, hg1⟩ := hce k b (hb.mono (by omega))
  have hunf : unfused1 cx (pure g) (evalT cx o X c) b = .ok (⟨canon o X (.branch op [c]), true, id⟩, b1) := by
    rw [unfused1_ok cx o X (pure g) g _ b b1 c id hA hcv hev rfl, hcanon]
  have hb1 : Good X.ncols (k + 1) b := hb.mono (by omega)
  unfold deg1Dispatch
  by_cases hlim : operatorLimit < (opsOf o 1).length
  · simp only [hlim, ↓reduceIte]
    refine ⟨id, b1, ?_, hg1⟩
    rw [unfused1_ok cx o X _ g _ b b1 c id hA hcv hev (idxOp_lookup o 1 op g (Nat.le_refl 1) hg),
      hcanon]
  · simp only [hlim, ↓reduceIte, hnif, jl_ok_bind]
    rcases c with a | f | ⟨lop, cs'⟩
    · exact ⟨id, b1, hunf, hg1⟩
    · exact ⟨id, b1, hunf, hg1⟩
    · rcases cs' with _ | ⟨ll, _ | ⟨lr, _ | ⟨_, _⟩⟩⟩
      · exact ⟨id, b1, hunf, hg1⟩
      · -- op(op_l(x))
        simp only
        cases hfu : (cx.useFused && isLeaf ll)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨id, b1, hunf, hg1⟩
        · simp only [↓reduceIte]
          simp only [Bool.and_eq_true] at hfu
          simp only [Tree.WF] at hcw
          obtain ⟨⟨hl1', _, _⟩, ⟨hlo1, hlo2, _⟩, hcs'⟩ := hcw
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlo2 hl1'
          obtain ⟨fl, hfl, hnifl⟩ := nifOp_lookup o 1 lop (Nat.le_refl 1) hlo1 hlo2
          have hllw := hcs' ll (by simp)
          have hllv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) ll :=
            fun j hj => AllValid.children o _ lop [ll] (hcv j hj) ll (by simp)
          have hcvx : ∀ j, j < X.ncols → cv o X (.branch lop [ll]) j = fl [cv o X ll j] := by
            intro j hj
            have := vx_branch o (col X (j + 1)) lop [ll] fl hfl
              (fun c' hc' => AllValid.some o _ c' (by simp at hc'; subst hc'; exact hllv j hj))
            simpa using this
          have hcl : isConstLeaf ll = false := by
            rw [← isConstant_leaf ll hfu.2]; simpa [isConstant, isConstantL] using hnc
          obtain ⟨id', b', hk, hg'⟩ := deg1L1_ok cx o X g fl ll (LeafOK.of_wf ll hfu.2 hllw) hcl
            (fun j hj => by rw [← hcvx j hj]; exact AllValid.valid o _ _ (hcv j hj)) hb1
          refine ⟨id', b', ?_, hg'⟩
          simp only [hnifl, jl_ok_bind, hk, hcanon]
          congr 3
          exact range_map_congr _ _ _ (fun j hj => by rw [hcvx j hj])
      · -- op(op_l(x, y))
        simp only
        cases hfu : (cx.useFused && isLeaf ll && isLeaf lr)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨id, b1, hunf, hg1⟩
        · simp only [↓reduceIte]
          simp only [Bool.and_eq_true] at hfu
          simp only [Tree.WF] at hcw
          obtain ⟨⟨hl1', _, _⟩, ⟨hlo1, hlo2, _⟩, hcs'⟩ := hcw
          simp only [List.length_cons, List.length_nil] at hlo2 hl1'
          obtain ⟨fl, hfl, hnifl⟩ := nifOp_lookup o 2 lop (by omega) hlo1 hlo2
          have hllv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) ll :=
            fun j hj => AllValid.children o _ lop [ll, lr] (hcv j hj) ll (by simp)
          have hlrv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) lr :=
            fun j hj => AllValid.children o _ lop [ll, lr] (hcv j hj) lr (by simp)
          have hcvx : ∀ j, j < X.ncols →
              cv o X (.branch lop [ll, lr]) j = fl [cv o X ll j, cv o X lr j] := by
            intro j hj
            have := vx_branch o (col X (j + 1)) lop [ll, lr] fl hfl (fun c' hc' => by
              simp at hc'
              rcases hc' with rfl | rfl
              · exact AllValid.some o _ _ (hllv j hj)
              · exact AllValid.some o _ _ (hlrv j hj))
            simpa using this
          have hL := leaves2_of o X ll lr hfu.1.2 hfu.2 (hcs' ll (by simp)) (hcs' lr (by simp))
            (by simpa [isConstant, isConstantL] using hnc) hllv hlrv
          obtain ⟨id', b', hk, hg'⟩ := deg1L2_ok cx o X g fl ll lr hL
            (fun j hj => by rw [← hcvx j hj]; exact AllValid.valid o _ _ (hcv j hj)) hn hb1
          refine ⟨id', b', ?_, hg'⟩
          simp only [hnifl, jl_ok_bind, hk, hcanon]
          congr 3
          exact range_map_congr _ _ _ (fun j hj => by rw [hcvx j hj])
      · exact ⟨id, b1, hunf, hg1⟩

theorem cv_branch2 (o : OpEnum T) (X : JMat T) (op : Nat) (l r : Tree T) (g : List T → T)
    (hg : o.lookup 2 op = some g) (j : Nat)
    (hl : AllValid o (col X (j + 1)) l) (hr : AllValid o (col X (j + 1)) r) :
    cv o X (.branch op [l, r]) j = g [cv o X l j, cv o X r j] := by
  have := vx_branch o (col X (j + 1)) op [l, r] g hg (fun c' hc' => by
    simp at hc'
    rcases hc' with rfl | rfl
    · exact AllValid.some o _ _ hl
    · exact AllValid.some o _ _ hr)
  simpa using this

theorem deg2_case (cx : Ctx) (o : OpEnum T) (X : JMat T) (hA : ArrayValidSound T)
    (hn : 1 ≤ X.ncols) (op : Nat) (l r : Tree T)
    (hwf : (Tree.branch op [l, r]).WF cx.D o.nops X.nrows)
    (hnc : (isConstant l && isConstant r) = false) (ihl : ChildOK cx o X l) (ihr : ChildOK cx o X r)
    {k : Nat} {b : Buf T} (hb : Good X.ncols (k + (Tree.branch op [l, r]).size) b) :
    ∃ id b', deg2Dispatch cx o X op l r (evalT cx o X l) (evalT cx o X r) b =
        .ok (⟨canon o X (.branch op [l, r]), true, id⟩, b') ∧ Good X.ncols k b' := by
  obtain ⟨hlw, hlv, hle⟩ := ihl
  obtain ⟨hrw, hrv, hre⟩ := ihr
  have hwf' := hwf
  simp only [Tree.WF] at hwf'
  obtain ⟨⟨hl1, _, _⟩, ⟨ho1, ho2, _⟩, _⟩ := hwf'
  simp only [List.length_cons, List.length_nil] at ho2 hl1
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 2 op (by omega) ho1 ho2
  have hch : ∀ j, j < X.ncols → ∀ c' ∈ [l, r], AllValid o (col X (j + 1)) c' := by
    intro j hj c' hc'
    simp at hc'
    rcases hc' with rfl | rfl
    · exact hlv j hj
    · exact hrv j hj
  have hcanon := canon_branch o X op [l, r] g hg hch
  simp only [List.map_cons, List.map_nil] at hcanon
  have hsize : (Tree.branch op [l, r]).size = 1 + (l.size + r.size) := by
    simp only [Tree.size_branch, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  rw [hsize] at hb
  obtain ⟨idl, b1, hevl, hg1⟩ := hle (k + 1 + r.size) b (hb.mono (by omega))
  obtain ⟨idr, b2, hevr, hg2⟩ := hre (k + 1) b1 hg1
  have hunf : unfused2 cx (pure g) (evalT cx o X l) (evalT cx o X r) b =
      .ok (⟨canon o X (.branch op [l, r]), true, idl⟩, b2) := by
    rw [unfused2_ok cx o X (pure g) g _ _ b b1 b2 l r idl idr hA hlv hrv hevl hevr rfl, hcanon]
  have hb1 : Good X.ncols (k + 1) b := hb.mono (by omega)
  -- `op(left, leaf)` with the left child evaluated first
  have hr0 : isLeaf r = true →
      checked cx (evalT cx o X l) (fun xl cid b => deg2R0 cx X g r xl cid b) b =
        .ok (⟨canon o X (.branch op [l, r]), true, idl⟩, b1) := by
    intro hrl
    rw [checked_ok cx o X _ _ b b1 l idl hA hlv hevl,
      deg2R0_ok cx o X g l r (LeafOK.of_wf r hrl hrw) hn (fun j hj => AllValid.valid o _ r (hrv j hj)),
      hcanon]
  obtain ⟨idr', b1', hevr', hg1'⟩ := hre k b (hb.mono (by omega))
  have hl0 : isLeaf l = true →
      checked cx (evalT cx o X r) (fun xr cid b => deg2L0 cx X g l xr cid b) b =
        .ok (⟨canon o X (.branch op [l, r]), true, idr'⟩, b1') := by
    intro hll
    rw [checked_ok cx o X _ _ b b1' r idr' hA hrv hevr',
      deg2L0_ok cx o X g l r (LeafOK.of_wf l hll hlw) hn (fun j hj => AllValid.valid o _ l (hlv j hj)),
      hcanon]
  have hk1 : Good X.ncols k b1 := hg1.mono (by omega)
  have hk2 : Good X.ncols k b2 := hg2.mono (by omega)
  unfold deg2Dispatch
  by_cases hlim : operatorLimit < (opsOf o 2).length
  · simp only [hlim, ↓reduceIte]
    refine ⟨idl, b2, ?_, hk2⟩
    rw [unfused2_ok cx o X _ g _ _ b b1 b2 l r idl idr hA hlv hrv hevl hevr
      (idxOp_lookup o 2 op g (by omega) hg), hcanon]
  · simp only [hlim, ↓reduceIte, hnif, jl_ok_bind]
    cases hfu : cx.useFused
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨idl, b2, hunf, hk2⟩
    · simp only [Bool.true_and]
      cases hll : isLeaf l <;> cases hrl : isLeaf r
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ⟨idl, b2, hunf, hk2⟩
      · -- left inner node, right leaf
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        have h0 := hr0 hrl
        rcases l with a | f | ⟨lop, cs'⟩
        · simp [isLeaf] at hll
        · simp [isLeaf] at hll
        · rcases cs' with _ | ⟨ll, _ | ⟨lr, _ | ⟨_, _⟩⟩⟩
          · exact ⟨idl, b1, h0, hk1⟩
          · exact ⟨idl, b1, h0, hk1⟩
          · simp only
            cases hb0 : (isNum T && isLeaf ll && isLeaf lr)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨idl, b1, h0, hk1⟩
            · simp only [↓reduceIte]
              simp only [Bool.and_eq_true] at hb0
              have hlw' := hlw
              simp only [Tree.WF] at hlw'
              obtain ⟨⟨hll1, _, _⟩, ⟨hlo1, hlo2, _⟩, hcs'⟩ := hlw'
              simp only [List.length_cons, List.length_nil] at hlo2 hll1
              obtain ⟨g', hg', hnif'⟩ := nifOp_lookup o 2 lop (by omega) hlo1 hlo2
              have hllv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) ll :=
                fun j hj => AllValid.children o _ lop [ll, lr] (hlv j hj) ll (by simp)
              have hlrv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) lr :=
                fun j hj => AllValid.children o _ lop [ll, lr] (hlv j hj) lr (by simp)
              have hL : Leaves3 o X ll lr r := {
                ok1 := LeafOK.of_wf ll hb0.1.2 (hcs' ll (by simp))
                ok2 := LeafOK.of_wf lr hb0.2 (hcs' lr (by simp))
                ok3 := LeafOK.of_wf r hrl hrw
                nc := by
                  intro ⟨h1, h2, h3⟩
                  rw [← isConstant_leaf ll hb0.1.2] at h1
                  rw [← isConstant_leaf lr hb0.2] at h2
                  rw [← isConstant_leaf r hrl] at h3
                  simp [isConstant, isConstantL, h1, h2, h3] at hnc
                v1 := fun j hj => AllValid.valid o _ _ (hllv j hj)
                v2 := fun j hj => AllValid.valid o _ _ (hlrv j hj)
                v3 := fun j hj => AllValid.valid o _ _ (hrv j hj) }
              have hcvx := fun j hj => cv_branch2 o X lop ll lr g' hg' j (hllv j hj) (hlrv j hj)
              obtain ⟨id', b', hk, hg'k⟩ := branch0_left_ok cx o X g g' ll lr r hL
                (fun j hj => by rw [← hcvx j hj]; exact AllValid.valid o _ _ (hlv j hj)) hn hb1
              refine ⟨id', b', ?_, hg'k⟩
              simp only [hnif', jl_ok_bind, hk, hcanon]
              congr 3
              exact range_map_congr _ _ _ (fun j hj => by rw [hcvx j hj])
          · exact ⟨idl, b1, h0, hk1⟩
      · -- left leaf, right inner node
        simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        have h0 := hl0 hll
        rcases r with a | f | ⟨rop, cs'⟩
        · simp [isLeaf] at hrl
        · simp [isLeaf] at hrl
        · rcases cs' with _ | ⟨rl, _ | ⟨rr, _ | ⟨_, _⟩⟩⟩
          · exact ⟨idr', b1', h0, hg1'⟩
          · exact ⟨idr', b1', h0, hg1'⟩
          · simp only
            cases hb0 : (isNum T && isLeaf rl && isLeaf rr)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact ⟨idr', b1', h0, hg1'⟩
            · simp only [↓reduceIte]
              simp only [Bool.and_eq_true] at hb0
              have hrw' := hrw
              simp only [Tree.WF] at hrw'
              obtain ⟨⟨hrl1, _, _⟩, ⟨hro1, hro2, _⟩, hcs'⟩ := hrw'
              simp only [List.length_cons, List.length_nil] at hro2 hrl1
              obtain ⟨g', hg', hnif'⟩ := nifOp_lookup o 2 rop (by omega) hro1 hro2
              have hrlv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) rl :=
                fun j hj => AllValid.children o _ rop [rl, rr] (hrv j hj) rl (by simp)
              have hrrv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) rr :=
                fun j hj => AllValid.children o _ rop [rl, rr] (hrv j hj) rr (by simp)
              have hL : Leaves3 o X l rl rr := {
                ok1 := LeafOK.of_wf l hll hlw
                ok2 := LeafOK.of_wf rl hb0.1.2 (hcs' rl (by simp))
                ok3 := LeafOK.of_wf rr hb0.2 (hcs' rr (by simp))
                nc := by
                  intro ⟨h1, h2, h3⟩
                  rw [← isConstant_leaf l hll] at h1
                  rw [← isConstant_leaf rl hb0.1.2] at h2
                  rw [← isConstant_leaf rr hb0.2] at h3
                  simp [isConstant, isConstantL, h1, h2, h3] at hnc
                v1 := fun j hj => AllValid.valid o _ _ (hlv j hj)
                v2 := fun j hj => AllValid.valid o _ _ (hrlv j hj)
                v3 := fun j hj => AllValid.valid o _ _ (hrrv j hj) }
              have hcvx := fun j hj => cv_branch2 o X rop rl rr g' hg' j (hrlv j hj) (hrrv j hj)
              obtain ⟨id', b', hk, hg'k⟩ := branch0_right_ok cx o X g g' l rl rr hL
                (fun j hj => by rw [← hcvx j hj]; exact AllValid.valid o _ _ (hrv j hj)) hn hb1
              refine ⟨id', b', ?_, hg'k⟩
              simp only [hnif', jl_ok_bind, hk, hcanon]
              congr 3
              exact range_map_congr _ _ _ (fun j hj => by rw [hcvx j hj])
          · exact ⟨idr', b1', h0, hg1'⟩
      · -- both leaves
        simp only [Bool.and_self, ↓reduceIte]
        have hL := leaves2_of o X l r hll hrl hlw hrw hnc hlv hrv
        obtain ⟨id', b', hk, hg'k⟩ := deg2L0R0_ok cx o X g l r hL hn hb1
        exact ⟨id', b', by rw [hk, hcanon], hg'k⟩

end DynExpr.Eval
