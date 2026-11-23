import DynExpr.Eval.Top

/-!
Zero-sample flag agreement: `eval-zero-samples-leaf`, `eval-zero-samples-pair`
and `eval-zero-samples-clean`. With zero samples, `early_exit=true` and no
buffer, every array is empty and both the fused and the unfused evaluation
return the flag `zsFlag o t`, the conjunction of the validity of every
constant leaf, with constant subtrees contributing their constant-evaluation
flag.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- Flag of the constant-tree shortcut. -/
def zsConstOk (o : OpEnum T) (t : Tree T) : Bool :=
  match constEval o t with
  | .ok p => p.2
  | .error _ => false

mutual
/-- Completion flag of a zero-sample evaluation with early exit. -/
def zsFlag (o : OpEnum T) : Tree T → Bool
  | .const v => valid v
  | .feature _ => true
  | .branch op cs => if isConstantL cs then zsConstOk o (.branch op cs) else zsFlagL o cs
/-- List version of `zsFlag`. -/
def zsFlagL (o : OpEnum T) : List (Tree T) → Bool
  | [] => true
  | c :: cs => zsFlag o c && zsFlagL o cs
end

/-- Flag of a leaf. -/
private def lv : Tree T → Bool
  | .const v => valid v
  | _ => true

/-- Flag of the inner pair of leaves in `deg2_branch0_eval`. -/
private def pf (g : List T → T) (l1 l2 : Tree T) : Bool :=
  if isConstLeaf l1 && isConstLeaf l2 then lv l1 && lv l2 && valid (g [leafVal l1, leafVal l2])
  else lv l1 && lv l2

/-- The result of a zero-sample evaluation with flag `ok`. -/
private def E (ok : Bool) : Jl (ResultOk T × Buf T) := .ok (⟨#[], ok, .fresh⟩, .none)

private theorem zs_valid_nil : isValidArray (#[] : JVec T) = true := by
  unfold isValidArray
  split <;> simp

omit [JlScalar T] in
private theorem zs_simd0 (f : Nat → Jl T) : simdWrite (#[] : JVec T) 0 f = .ok #[] := by
  simp [simdWrite]

private theorem zs_inplace0 (g : Nat → T → Jl T) : inplaceMap (#[] : JVec T) g = .ok #[] := by
  simp [inplaceMap]

omit [JlScalar T] in
private theorem zs_degn0 (f : List T → T) (cs : List (JVec T)) :
    degnEval f ((#[] : JVec T) :: cs) = .ok #[] := by
  simp [degnEval]

omit [JlScalar T] in
private theorem zs_fill0 (v : T) : JVec.fill 0 v = (#[] : JVec T) := by
  simp [JVec.fill]

private theorem zs_zf_leaf (o : OpEnum T) (X : JMat T) (ℓ : Tree T) (h : LeafOK X ℓ) :
    zsFlag o ℓ = lv ℓ := by
  cases ℓ with
  | const v => simp [zsFlag, lv]
  | feature f => simp [zsFlag, lv]
  | branch _ _ => exact h.elim

private theorem zs_checked (cx : Ctx) (he : cx.earlyExit = true)
    (ev : Buf T → Jl (ResultOk T × Buf T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T)) (a : Bool) (hev : ev .none = E a) :
    checked cx ev k .none = if a then k #[] .fresh .none else E false := by
  cases a <;> simp [checked, hev, E, he, zs_valid_nil]

private theorem zs_unfused1 (cx : Ctx) (he : cx.earlyExit = true) (fop : Jl (List T → T))
    (f : List T → T) (hf : fop = .ok f) (ev : Buf T → Jl (ResultOk T × Buf T)) (a : Bool)
    (hev : ev .none = E a) : unfused1 cx fop ev .none = E a := by
  unfold unfused1
  rw [zs_checked cx he ev _ a hev]
  cases a <;> simp [hf, zs_degn0, E]

private theorem zs_unfused2 (cx : Ctx) (he : cx.earlyExit = true) (fop : Jl (List T → T))
    (f : List T → T) (hf : fop = .ok f) (evL evR : Buf T → Jl (ResultOk T × Buf T)) (a c : Bool)
    (hl : evL .none = E a) (hr : evR .none = E c) :
    unfused2 cx fop evL evR .none = E (a && c) := by
  unfold unfused2
  rw [zs_checked cx he evL _ a hl]
  cases a
  · simp
  · simp only [↓reduceIte, Bool.true_and]
    rw [zs_checked cx he evR _ c hr]
    cases c <;> simp [hf, zs_degn0, E]

private theorem zs_retV (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (v : T) (k : Buf T → Jl (ResultOk T × Buf T)) :
    retV cx X v k .none = if valid v then k .none else E false := by
  cases h : valid v <;> simp [retV, h, he, hn, getArray, zs_fill0, nextId, E]

private theorem zs_deg1L1 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (f fl : List T → T)
    (ll : Tree T) (hl : LeafOK X ll) (hc : isConstLeaf ll = false) :
    deg1L1 cx X f fl ll .none = E true := by
  cases ll with
  | const a => simp [isConstLeaf] at hc
  | branch _ _ => exact hl.elim
  | feature q =>
    simp only [LeafOK] at hl
    simp [deg1L1, isConstLeaf, leafFeat, chk_ok X q hl.1 hl.2, hn, getArray, zs_fill0,
      zs_simd0, nextId, E]

private theorem zs_deg1L2 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (f fl : List T → T) (ll lr : Tree T) (hl : LeafOK X ll) (hr : LeafOK X lr)
    (hc : (isConstLeaf ll && isConstLeaf lr) = false) :
    deg1L2 cx X f fl ll lr .none = E (lv ll && lv lr) := by
  cases ll with
  | branch _ _ => exact hl.elim
  | const a =>
    cases lr with
    | branch _ _ => exact hr.elim
    | const c => simp [isConstLeaf] at hc
    | feature q =>
      simp only [LeafOK] at hr
      cases ha : valid a <;>
        simp [deg1L2, isConstLeaf, leafVal, leafFeat, lv, zs_retV cx X hn he, ha,
          chk_ok X q hr.1 hr.2, hn, getArray, zs_fill0, zs_simd0, nextId, E]
  | feature p =>
    simp only [LeafOK] at hl
    cases lr with
    | branch _ _ => exact hr.elim
    | const c =>
      cases hcv : valid c <;>
        simp [deg1L2, isConstLeaf, leafVal, leafFeat, lv, zs_retV cx X hn he, hcv,
          chk_ok X p hl.1 hl.2, hn, getArray, zs_fill0, zs_simd0, nextId, E]
    | feature q =>
      simp only [LeafOK] at hr
      simp [deg1L2, isConstLeaf, leafFeat, lv, chk_ok X p hl.1 hl.2, chk_ok X q hr.1 hr.2,
        hn, getArray, zs_fill0, zs_simd0, nextId, E]

private theorem zs_deg2L0R0 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (f : List T → T) (l r : Tree T) (hl : LeafOK X l) (hr : LeafOK X r)
    (hc : (isConstLeaf l && isConstLeaf r) = false) :
    deg2L0R0 cx X f l r .none = E (lv l && lv r) := by
  cases l with
  | branch _ _ => exact hl.elim
  | const a =>
    cases r with
    | branch _ _ => exact hr.elim
    | const c => simp [isConstLeaf] at hc
    | feature q =>
      simp only [LeafOK] at hr
      cases ha : valid a <;>
        simp [deg2L0R0, isConstLeaf, leafVal, leafFeat, lv, zs_retV cx X hn he, ha,
          chk_ok X q hr.1 hr.2, hn, getArray, zs_fill0, zs_simd0, nextId, E]
  | feature p =>
    simp only [LeafOK] at hl
    cases r with
    | branch _ _ => exact hr.elim
    | const c =>
      cases hcv : valid c <;>
        simp [deg2L0R0, isConstLeaf, leafVal, leafFeat, lv, zs_retV cx X hn he, hcv,
          chk_ok X p hl.1 hl.2, hn, getArray, zs_fill0, zs_simd0, nextId, E]
    | feature q =>
      simp only [LeafOK] at hr
      simp [deg2L0R0, isConstLeaf, leafFeat, lv, chk_ok X p hl.1 hl.2, chk_ok X q hr.1 hr.2,
        hn, getArray, zs_fill0, zs_simd0, nextId, E]

private theorem zs_deg2L0 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (f : List T → T) (l : Tree T) (hl : LeafOK X l) :
    deg2L0 cx X f l #[] .fresh .none = E (lv l) := by
  cases l with
  | branch _ _ => exact hl.elim
  | const a =>
    cases ha : valid a <;>
      simp [deg2L0, isConstLeaf, leafVal, lv, zs_retV cx X hn he, ha, zs_inplace0, E]
  | feature p =>
    simp only [LeafOK] at hl
    simp [deg2L0, isConstLeaf, leafFeat, lv, chk_ok X p hl.1 hl.2, zs_inplace0, E]

private theorem zs_deg2R0 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (f : List T → T) (r : Tree T) (hr : LeafOK X r) :
    deg2R0 cx X f r #[] .fresh .none = E (lv r) := by
  cases r with
  | branch _ _ => exact hr.elim
  | const a =>
    cases ha : valid a <;>
      simp [deg2R0, isConstLeaf, leafVal, lv, zs_retV cx X hn he, ha, zs_inplace0, E]
  | feature p =>
    simp only [LeafOK] at hr
    simp [deg2R0, isConstLeaf, leafFeat, lv, chk_ok X p hr.1 hr.2, zs_inplace0, E]

/-- `bad ℓ` of `deg2_branch0_eval` under early exit. -/
private theorem zs_bad (X : JMat T) (ℓ : Tree T) (h : LeafOK X ℓ) :
    (isConstLeaf ℓ && !valid (leafVal ℓ)) = !lv ℓ := by
  cases ℓ with
  | const v => simp [isConstLeaf, leafVal, lv]
  | feature f => simp [isConstLeaf, lv]
  | branch _ _ => exact h.elim

private theorem zs_branch0 (cx : Ctx) (X : JMat T) (hn : X.ncols = 0) (he : cx.earlyExit = true)
    (hp : 1 ≤ X.nrows) (f g : List T → T) (s : Side) (l1 l2 l3 : Tree T)
    (h1 : LeafOK X l1) (h2 : LeafOK X l2) (h3 : LeafOK X l3) :
    branch0 cx X f g s l1 l2 l3 .none =
      E (match s with
        | .left => pf g l1 l2 && lv l3
        | .right => lv l1 && pf g l2 l3) := by
  cases s
  all_goals
    unfold branch0
    simp only [getArray, jl_ok_bind, he, Bool.true_and, zs_bad X l1 h1, zs_bad X l2 h2, zs_bad X l3 h3]
  all_goals
    split
    · rename_i hb
      have hz : lv l1 = false ∨ lv l2 = false ∨ lv l3 = false := by
        cases h1' : lv l1 <;> cases h2' : lv l2 <;> cases h3' : lv l3 <;> simp_all
      rcases hz with hz | hz | hz <;> simp [hn, zs_fill0, nextId, pf, hz, E]
    · rename_i hb
      have hv1 : lv l1 = true := by cases h : lv l1 <;> simp_all
      have hv2 : lv l2 = true := by cases h : lv l2 <;> simp_all
      have hv3 : lv l3 = true := by cases h : lv l3 <;> simp_all
      simp only [pick_chk X l1 h1 hp, pick_chk X l2 h2 hp, pick_chk X l3 h3 hp, jl_ok_bind]
      simp only [retVIf]
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        rw [zs_retV cx X hn he]
        simp [hc.1, hc.2, hn, zs_fill0, zs_simd0, nextId, E, pf, hv1, hv2, hv3]
          <;> split <;> simp_all
      · rename_i hc
        simp only [Bool.not_eq_true] at hc
        simp [hc, hn, zs_fill0, zs_simd0, nextId, E, pf, hv1, hv2, hv3]

private theorem zs_zf_pair (o : OpEnum T) (X : JMat T) (lop : Nat) (g : List T → T)
    (hg : nifOp (opsOf o 2) lop = .ok g) (hlim : ¬ operatorLimit < (opsOf o 2).length)
    (l1 l2 : Tree T) (h1 : LeafOK X l1) (h2 : LeafOK X l2) :
    zsFlag o (.branch lop [l1, l2]) = pf g l1 l2 := by
  cases l1 with
  | branch _ _ => exact h1.elim
  | feature p =>
    cases l2 with
    | branch _ _ => exact h2.elim
    | const c => simp [zsFlag, zsFlagL, isConstantL, isConstant, pf, lv, isConstLeaf]
    | feature q => simp [zsFlag, zsFlagL, isConstantL, isConstant, pf, lv, isConstLeaf]
  | const a =>
    cases l2 with
    | branch _ _ => exact h2.elim
    | feature q => simp [zsFlag, zsFlagL, isConstantL, isConstant, pf, lv, isConstLeaf]
    | const c =>
      cases ha : valid a <;> cases hc : valid c <;>
        simp [zsFlag, isConstantL, isConstant, zsConstOk, constEval, constEvalL, pf, lv,
          isConstLeaf, leafVal, ha, hc, hg, hlim]

omit [JlScalar T] in
private theorem zs_leaf_const (t : Tree T) (h : isLeaf t = true) :
    isConstant t = isConstLeaf t := by cases t <;> simp_all [isLeaf, isConstant, isConstLeaf]

private theorem zs_deg1 (cx : Ctx) (o : OpEnum T) (X : JMat T) (hn : X.ncols = 0)
    (he : cx.earlyExit = true) (op : Nat) (c : Tree T) (ev : Buf T → Jl (ResultOk T × Buf T))
    (hop : 1 ≤ op) (hops : op ≤ o.nops 1) (hwc : c.WF cx.D o.nops X.nrows)
    (hnc : isConstant c = false) (hev : ev .none = E (zsFlag o c)) :
    deg1Dispatch cx o X op c ev .none = E (zsFlag o c) := by
  obtain ⟨f, hl, hf⟩ := nifOp_lookup o 1 op (by omega) hop hops
  have hi := idxOp_lookup o 1 op f (by omega) hl
  unfold deg1Dispatch
  dsimp only
  split
  · exact zs_unfused1 cx he _ f hi ev _ hev
  · simp only [hf, jl_ok_bind]
    have hu := zs_unfused1 cx he (pure f) f rfl ev _ hev
    cases c with
    | const v => exact hu
    | feature q => exact hu
    | branch lop cs =>
      simp only [Tree.WF] at hwc
      cases cs with
      | nil => exact hu
      | cons ll ls =>
        cases ls with
        | nil =>
          simp only
          split
          · rename_i hcond
            obtain ⟨g, _, hgop⟩ := nifOp_lookup o 1 lop (by omega) hwc.2.1.1
              (by simpa using hwc.2.1.2.1)
            simp only [hgop, jl_ok_bind]
            have hleaf : isLeaf ll = true := by simp_all only [Bool.and_eq_true]
            have hcl : isConstLeaf ll = false := by
              simpa [isConstant, isConstantL, zs_leaf_const ll hleaf] using hnc
            rw [zs_deg1L1 cx X hn f g ll (LeafOK.of_wf ll hleaf (hwc.2.2 ll (by simp))) hcl]
            have hs : zsFlag o ll = true := by
              rw [zs_zf_leaf o X ll (LeafOK.of_wf ll hleaf (hwc.2.2 ll (by simp)))]
              cases ll <;> simp_all [isConstLeaf, lv, isLeaf]
            simp [zsFlag, zsFlagL, isConstantL, hs]
            simp_all [isConstant, isConstantL]
          · exact hu
        | cons lr rs =>
          cases rs with
          | cons z zs => exact hu
          | nil =>
            simp only
            split
            · rename_i hcond
              obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 lop (by omega) hwc.2.1.1
                (by simpa using hwc.2.1.2.1)
              simp only [hgop, jl_ok_bind]
              have hll : isLeaf ll = true := by simp_all only [Bool.and_eq_true]
              have hlr : isLeaf lr = true := by simp_all only [Bool.and_eq_true]
              have okl := LeafOK.of_wf ll hll (hwc.2.2 ll (by simp))
              have okr := LeafOK.of_wf lr hlr (hwc.2.2 lr (by simp))
              have hnc' : isConstantL [ll, lr] = false := by simpa [isConstant] using hnc
              have hcl : (isConstLeaf ll && isConstLeaf lr) = false := by
                simpa [isConstantL, zs_leaf_const ll hll, zs_leaf_const lr hlr] using hnc'
              rw [zs_deg1L2 cx X hn he f g ll lr okl okr hcl]
              simp [zsFlag, zsFlagL, hnc', zs_zf_leaf o X ll okl, zs_zf_leaf o X lr okr]
            · exact hu

private theorem zs_deg2 (cx : Ctx) (o : OpEnum T) (X : JMat T) (hn : X.ncols = 0)
    (he : cx.earlyExit = true) (op : Nat) (l r : Tree T)
    (evL evR : Buf T → Jl (ResultOk T × Buf T))
    (hop : 1 ≤ op) (hops : op ≤ o.nops 2)
    (hwl : l.WF cx.D o.nops X.nrows) (hwr : r.WF cx.D o.nops X.nrows) (hp : 1 ≤ X.nrows)
    (hnc : isConstantL [l, r] = false)
    (hevL : evL .none = E (zsFlag o l)) (hevR : evR .none = E (zsFlag o r)) :
    deg2Dispatch cx o X op l r evL evR .none = E (zsFlag o l && zsFlag o r) := by
  obtain ⟨f, hl, hf⟩ := nifOp_lookup o 2 op (by omega) hop hops
  have hi := idxOp_lookup o 2 op f (by omega) hl
  have hr0 (hrleaf : isLeaf r = true) :
      checked cx evL (fun x id b => deg2R0 cx X f r x id b) .none =
        E (zsFlag o l && zsFlag o r) := by
    have okr := LeafOK.of_wf r hrleaf hwr
    rw [zs_checked cx he evL _ _ hevL, zs_zf_leaf o X r okr]
    cases zsFlag o l <;> simp [zs_deg2R0 cx X hn he f r okr]
  have hl0 (hlleaf : isLeaf l = true) :
      checked cx evR (fun x id b => deg2L0 cx X f l x id b) .none =
        E (zsFlag o l && zsFlag o r) := by
    have okl := LeafOK.of_wf l hlleaf hwl
    rw [zs_checked cx he evR _ _ hevR, zs_zf_leaf o X l okl]
    cases zsFlag o r <;> simp [zs_deg2L0 cx X hn he f l okl, E]
  unfold deg2Dispatch
  dsimp only
  split
  · exact zs_unfused2 cx he _ f hi evL evR _ _ hevL hevR
  · rename_i hlim
    simp only [hf, jl_ok_bind]
    split
    · have hll : isLeaf l = true := by simp_all only [Bool.and_eq_true]
      have hlr : isLeaf r = true := by simp_all only [Bool.and_eq_true]
      have okl := LeafOK.of_wf l hll hwl
      have okr := LeafOK.of_wf r hlr hwr
      have hcl : (isConstLeaf l && isConstLeaf r) = false := by
        simpa [isConstantL, zs_leaf_const l hll, zs_leaf_const r hlr] using hnc
      rw [zs_deg2L0R0 cx X hn he f l r okl okr hcl, zs_zf_leaf o X l okl, zs_zf_leaf o X r okr]
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
                · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 lop (by omega) hwl.2.1.1
                    (by simpa using hwl.2.1.2.1)
                  simp only [hgop, jl_ok_bind]
                  have hll : isLeaf ll = true := by simp_all only [Bool.and_eq_true]
                  have hlr : isLeaf lr = true := by simp_all only [Bool.and_eq_true]
                  have ok1 := LeafOK.of_wf ll hll (hwl.2.2 ll (by simp))
                  have ok2 := LeafOK.of_wf lr hlr (hwl.2.2 lr (by simp))
                  have okr := LeafOK.of_wf r hrleaf hwr
                  rw [zs_branch0 cx X hn he hp f g .left ll lr r ok1 ok2 okr,
                    zs_zf_pair o X lop g hgop hlim ll lr ok1 ok2, zs_zf_leaf o X r okr]
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
                  · obtain ⟨g, _, hgop⟩ := nifOp_lookup o 2 rop (by omega) hwr.2.1.1
                      (by simpa using hwr.2.1.2.1)
                    simp only [hgop, jl_ok_bind]
                    have hrl : isLeaf rl = true := by simp_all only [Bool.and_eq_true]
                    have hrr : isLeaf rr = true := by simp_all only [Bool.and_eq_true]
                    have ok2 := LeafOK.of_wf rl hrl (hwr.2.2 rl (by simp))
                    have ok3 := LeafOK.of_wf rr hrr (hwr.2.2 rr (by simp))
                    have okl := LeafOK.of_wf l hlleaf hwl
                    rw [zs_branch0 cx X hn he hp f g .right l rl rr okl ok2 ok3,
                      zs_zf_pair o X rop g hgop hlim rl rr ok2 ok3, zs_zf_leaf o X l okl]
                  · exact hl0 hlleaf
        · exact zs_unfused2 cx he _ f rfl evL evR _ _ hevL hevR

private theorem zs_children (cx : Ctx) (o : OpEnum T) (X : JMat T) (he : cx.earlyExit = true)
    (cs : List (Tree T)) (ih : ∀ c ∈ cs, evalT cx o X c .none = E (zsFlag o c)) :
    evalChildren cx o X cs .none =
      .ok (if zsFlagL o cs then .inr (cs.map (fun _ => ((#[] : JVec T), Ident.fresh)), .none)
        else .inl (⟨#[], false, .fresh⟩, .none)) := by
  induction cs with
  | nil => simp [evalChildren, zsFlagL]
  | cons c cs hi =>
    have hc := ih c (by simp)
    have hcs := hi (fun t ht => ih t (by simp [ht]))
    cases h : zsFlag o c
    · simp [evalChildren, hc, h, zsFlagL, E]
    · cases h' : zsFlagL o cs
      · simp [evalChildren, hc, h, zsFlagL, E, he, zs_valid_nil, hcs, h']
      · simp [evalChildren, hc, h, zsFlagL, E, he, zs_valid_nil, hcs, h']

private theorem zs_finish (o : OpEnum T) (n op : Nat) (cs : List (Tree T)) (hne : cs ≠ [])
    (hn : 1 ≤ n) (hop : 1 ≤ op) (hops : op ≤ o.nops n) (a : Bool) :
    degnFinish o n op (if a then .inr (cs.map (fun _ => ((#[] : JVec T), Ident.fresh)), .none)
      else .inl (⟨#[], false, .fresh⟩, .none)) = E a := by
  obtain ⟨f, _, hf⟩ := nifOp_lookup o n op hn hop hops
  cases a
  · simp [degnFinish, E]
  · cases cs with
    | nil => exact absurd rfl hne
    | cons c cs => simp [degnFinish, hf, zs_degn0, E]

omit [JlScalar T] in
private theorem zs_constList_iff (cs : List (Tree T)) :
    isConstantL cs = true ↔ ∀ c ∈ cs, isConstant c = true := by
  induction cs with
  | nil => simp [isConstantL]
  | cons c cs ih => simp [isConstantL, ih]

omit [JlScalar T] in
private theorem zs_zeroRows_constant (o : OpEnum T) (D : Nat) (t : Tree T)
    (h : t.WF D o.nops 0) : isConstant t = true := by
  induction t using Tree.induction with
  | hc v => rfl
  | hf f => simp only [Tree.WF] at h; omega
  | hb op cs ih =>
    simp only [Tree.WF] at h
    simp only [isConstant]
    apply (zs_constList_iff cs).2
    intro c hc
    exact ih c hc (h.2.2 c hc)

private theorem zs_constChildren (o : OpEnum T) (cs : List (Tree T))
    (ih : ∀ t ∈ cs, ∃ r, constEval o t = .ok r) : ∃ r, constEvalL o cs = .ok r := by
  induction cs with
  | nil => exact ⟨.inr [], rfl⟩
  | cons t ts hi =>
    obtain ⟨⟨v, ok⟩, hv⟩ := ih t (by simp)
    simp only [constEvalL, hv, jl_ok_bind]
    split
    · exact ⟨.inl (v, ok), rfl⟩
    · obtain ⟨r, hr⟩ := hi (fun c hc => ih c (by simp [hc]))
      cases r <;> simp [hr]

private theorem zs_constEval (o : OpEnum T) (t : Tree T) (D nf : Nat)
    (hw : t.WF D o.nops nf) : ∃ r, constEval o t = .ok r := by
  induction t using Tree.induction with
  | hc v => exact ⟨_, rfl⟩
  | hf f => exact ⟨_, rfl⟩
  | hb op cs ih =>
    simp only [Tree.WF] at hw
    obtain ⟨⟨hn, _, _⟩, ⟨hop, hnops, _⟩, hcs⟩ := hw
    obtain ⟨r, hr⟩ := zs_constChildren o cs (fun c hc => ih c hc (hcs c hc))
    obtain ⟨f, hlookup, hnif⟩ := nifOp_lookup o cs.length op hn hop hnops
    have hidx := idxOp_lookup o cs.length op f hn hlookup
    simp only [constEval, hr, jl_ok_bind]
    cases r with
    | inl r => exact ⟨r, rfl⟩
    | inr vs =>
      split <;> simp [hnif, hidx]

private theorem zs_constPath (o : OpEnum T) (X : JMat T) (hn : X.ncols = 0) (t : Tree T)
    (D : Nat) (hw : t.WF D o.nops X.nrows) : constPath o X t .none = E (zsConstOk o t) := by
  obtain ⟨⟨v, ok⟩, he⟩ := zs_constEval o t D X.nrows hw
  cases ok <;> simp [constPath, he, zsConstOk, filled, getFilled, getArray, hn, zs_fill0,
    nextId, E]

/-- Zero-sample evaluation with early exit, fused or not, returns `zsFlag`. -/
private theorem zs_eval (cx : Ctx) (o : OpEnum T) (X : JMat T) (hn : X.ncols = 0)
    (he : cx.earlyExit = true) (t : Tree T) (hw : t.WF cx.D o.nops X.nrows) :
    evalT cx o X t .none = E (zsFlag o t) := by
  induction t using Tree.induction with
  | hc v => simp [evalT, getFilled, hn, zs_fill0, nextId, he, zsFlag, E]
  | hf f =>
    simp only [Tree.WF] at hw
    have hr := rowInb_canon o X f hw.1 hw.2.1
    have hc : canon o X (.feature f) = #[] := by simp [canon, hn]
    simp [evalT, chk_ok X f hw.1 hw.2.1, getFeature, hr, hc, nextId, zsFlag, E]
  | hb op cs ih =>
    unfold evalT
    split
    · rename_i hc
      rw [he, zs_constPath o X hn (.branch op cs) cx.D hw]
      simp [zsFlag, hc]
    · have hnon : isConstantL cs = false := by simp_all
      have hp : 1 ≤ X.nrows := by
        by_cases hzero : X.nrows = 0
        · have hconst := zs_zeroRows_constant o cx.D (.branch op cs) (hzero ▸ hw)
          simp [isConstant, hnon] at hconst
        · omega
      have hz : zsFlag o (.branch op cs) = zsFlagL o cs := by simp [zsFlag, hnon]
      rw [hz]
      simp only [Tree.WF] at hw
      have hchild : ∀ c ∈ cs, evalT cx o X c .none = E (zsFlag o c) :=
        fun c hc => ih c hc (hw.2.2 c hc)
      cases cs with
      | nil => simp at hw
      | cons c cs =>
        cases cs with
        | nil =>
          simp only [zsFlagL, Bool.and_true]
          exact zs_deg1 cx o X hn he op c _ hw.2.1.1 (by simpa using hw.2.1.2.1)
            (hw.2.2 c (by simp)) (by simpa [isConstantL] using hnon) (hchild c (by simp))
        | cons d ds =>
          cases ds with
          | nil =>
            simp only [zsFlagL, Bool.and_true]
            exact zs_deg2 cx o X hn he op c d _ _ hw.2.1.1 (by simpa using hw.2.1.2.1)
              (hw.2.2 c (by simp)) (hw.2.2 d (by simp)) hp hnon
              (hchild c (by simp)) (hchild d (by simp))
          | cons e es =>
            simp only
            have hd : cx.D ≠ 2 := by
              have h := hw.1.2.1; simp only [List.length_cons] at h; omega
            simp only [hd, ↓reduceIte, zs_children cx o X he (c :: d :: e :: es) hchild,
              jl_ok_bind]
            have hfinish := zs_finish o (c :: d :: e :: es).length op (c :: d :: e :: es)
              (by simp) (by simp) hw.2.1.1 hw.2.1.2.1 (zsFlagL o (c :: d :: e :: es))
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using hfinish

/-- The completion flag of a zero-sample evaluation with early exit. -/
private theorem zs_top (ext : Ext) (impl : ExtImpl T) (D : Nat) (o : OpEnum T) (X : JMat T)
    (t : Tree T) (hn : X.ncols = 0) (hw : t.WF D o.nops X.nrows) (fused : Bool) :
    (evalTreeArray ext impl D t X o (plainCtx true fused .none)).map Prod.snd =
      .ok (zsFlag o t) := by
  have h := zs_eval (⟨true, fused, D⟩ : Ctx) o X hn rfl t hw
  simp only [evalTreeArray, plainCtx, Bool.false_and, Bool.false_eq_true, ↓reduceIte, evalArr,
    h, E, jl_ok_bind, jl_pure, zs_valid_nil]
  simp [Except.map]

theorem evalZeroSamplesLeaf_proof : evalZeroSamplesLeaf := by
  intro T _ ext impl D o X t _ hn hw _
  rw [zs_top ext impl D o X t hn hw true, zs_top ext impl D o X t hn hw false]

theorem evalZeroSamplesPair_proof : evalZeroSamplesPair := by
  intro T _ ext impl D o X t _ hn hw _
  rw [zs_top ext impl D o X t hn hw true, zs_top ext impl D o X t hn hw false]

theorem evalZeroSamplesClean_proof : evalZeroSamplesClean := by
  intro T _ ext impl D o X t _ hn hw _ _
  rw [zs_top ext impl D o X t hn hw true, zs_top ext impl D o X t hn hw false]

private theorem zs_jf_exact : ArrayValidExact JF := by
  intro a
  rw [jf_isValidArray, Array.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hx)
    exact h i hi
  · intro h i hi
    exact h _ (by simp)

/-- Hypotheses of eval-zero-samples-leaf: `x1` on a one-feature, zero-sample input. -/
example : ArrayValidExact JF ∧ (⟨1, 0, #[], rfl⟩ : JMat JF).ncols = 0 ∧
    (Tree.feature 1 : Tree JF).WF 2 (OpEnum.nops (⟨[]⟩ : OpEnum JF)) 1 ∧
    noConstBranch (Tree.feature 1 : Tree JF) = true :=
  ⟨zs_jf_exact, rfl, by simp [Tree.WF], rfl⟩

/-- Hypotheses of eval-zero-samples-pair: the finite constant `1.0`. -/
example : ArrayValidExact JF ∧ (⟨1, 0, #[], rfl⟩ : JMat JF).ncols = 0 ∧
    (Tree.const (.fin 1) : Tree JF).WF 2 (OpEnum.nops (⟨[]⟩ : OpEnum JF)) 1 ∧
    ConstsFinite (Tree.const (.fin 1) : Tree JF) :=
  ⟨zs_jf_exact, rfl, by simp [Tree.WF], rfl⟩

private instance : JlScalar Nat where
  valid := fun _ => true
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  isNumber := false
  isFloat := false
  floatLike := false
  undef := 0
  invalid? := none

/-- Hypotheses of eval-zero-samples-clean: the constant `7` over `Nat`. -/
example : ArrayValidExact Nat ∧ (⟨1, 0, #[], rfl⟩ : JMat Nat).ncols = 0 ∧
    (Tree.const 7 : Tree Nat).WF 2 (OpEnum.nops (⟨[]⟩ : OpEnum Nat)) 1 ∧
    noConstBranch (Tree.const 7 : Tree Nat) = true ∧ ConstsFinite (Tree.const 7 : Tree Nat) := by
  simp [ArrayValidExact, isValidArray, valid, JlScalar.floatLike, JlValue.valid, Tree.WF,
    noConstBranch, ConstsFinite, constsOK]

end DynExpr.Eval
