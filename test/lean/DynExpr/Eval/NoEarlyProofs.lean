import DynExpr.Eval.Top

namespace DynExpr.Eval

variable {T : Type} [s : JlScalar T]

/-- Changing only validity lets the all-valid theorem apply after transporting each kernel. -/
private abbrev totalScalar (s : JlScalar T) : JlScalar T :=
  @JlScalar.mk T ⟨fun _ => true⟩ s.zero s.one s.add s.mul s.isNumber s.isFloat s.floatLike
    s.undef s.invalid?

private theorem total_valid (x : T) : @valid T (totalScalar s) x = true := rfl

omit s in
/-- Without early exit the fused unary kernels always apply the outer operator. -/
private theorem post_noEarly [JlScalar T] (f : List T → T) (x : T) : post false f x = f [x] := rfl

omit s in
private theorem bind_value {A : Type} (a : Jl (T × Bool)) (k : T → Jl A) :
    (a >>= fun p => k p.1) = ((a.map Prod.fst) >>= k) := by
  cases a <;> rfl

mutual
private theorem constEval_transport (o : OpEnum T) (t : Tree T) :
    (constEval o t false).map Prod.fst =
      (@constEval T (totalScalar s) o t false).map Prod.fst := by
  cases t with
  | const v => rfl
  | feature f => rfl
  | branch op cs =>
    simp only [constEval, constEvalL_transport o cs]
    cases @constEvalL T (totalScalar s) o cs false with
    | error e => rfl
    | ok r =>
      cases r with
      | inl r => rfl
      | inr vs =>
        simp only [jl_ok_bind]
        by_cases hl : operatorLimit < (opsOf o cs.length).length
        · simp only [hl, ↓reduceIte]
          cases idxOp (opsOf o cs.length) op <;> rfl
        · simp only [hl, ↓reduceIte]
          cases nifOp (opsOf o cs.length) op <;> rfl

private theorem constEvalL_transport (o : OpEnum T) (cs : List (Tree T)) :
    constEvalL o cs false = @constEvalL T (totalScalar s) o cs false := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [constEvalL, constEvalL_transport o cs]
    let k : T → Jl ((T × Bool) ⊕ List T) := fun v => do
      match ← @constEvalL T (totalScalar s) o cs false with
      | .inl r => pure (.inl r)
      | .inr vs => pure (.inr (v :: vs))
    change (@constEval T s o c false >>= fun p => k p.1) =
      (@constEval T (totalScalar s) o c false >>= fun p => k p.1)
    calc
      _ = ((@constEval T s o c false).map Prod.fst >>= k) := bind_value _ k
      _ = ((@constEval T (totalScalar s) o c false).map Prod.fst >>= k) :=
        congrArg (fun a => a >>= k) (constEval_transport o c)
      _ = _ := (bind_value _ k).symm
end

private theorem constPath_transport (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T) :
    constPath o X t b false = @constPath T (totalScalar s) o X t b false := by
  have aux (a : Jl (T × Bool)) (k : T → Jl (ResultOk T × Buf T)) :
      (match a with | .error e => .error e | .ok (v, _) => k v) =
        (a.map Prod.fst >>= k) := by cases a <;> rfl
  unfold constPath
  change (match @constEval T s o t false with
    | .error e => Except.error e | .ok (v, _) => filled X v b) =
    (match @constEval T (totalScalar s) o t false with
    | .error e => .error e | .ok (v, _) => @filled T (totalScalar s) X v b)
  rw [aux, aux, constEval_transport o t]
  rfl

private theorem total_allValid (o : OpEnum T) (X : JMat T) (j : Nat)
    (hj : 1 ≤ j ∧ j ≤ X.ncols) (t : Tree T) (hw : t.WF D o.nops X.nrows) :
    @AllValid T (totalScalar s) o (col X j) t := by
  induction t using Tree.induction with
  | hc v => simp only [AllValid]; rfl
  | hf i =>
    simp only [AllValid]
    obtain ⟨v, hv⟩ := Tree.denoteRow_some o X j hj (.feature i) hw
    exact ⟨v, by simpa [Tree.denoteRow, Tree.denote, col] using hv, rfl⟩
  | hb op cs ih =>
    simp only [AllValid]
    have hw' := hw
    simp only [Tree.WF] at hw'
    refine ⟨fun c hc => ih c hc (hw'.2.2 c hc), ?_⟩
    obtain ⟨v, hv⟩ := Tree.denoteRow_some o X j hj (.branch op cs) hw
    exact ⟨v, hv, rfl⟩

private theorem total_arraySound : @ArrayValidSound T (totalScalar s) := by
  intro a _
  unfold isValidArray
  simp only [total_valid]
  split <;> simp

private theorem deg1L2_transport (cx : Ctx) (X : JMat T) (f fl : List T → T)
    (ll lr : Tree T) (b : Buf T) (he : cx.earlyExit = false) :
    deg1L2 cx X f fl ll lr b = @deg1L2 T (totalScalar s) cx X f fl ll lr b := by
  simp only [deg1L2, retV, he, Bool.false_and, Bool.false_eq_true, ↓reduceIte, post_noEarly,
    @post_noEarly T (totalScalar s)]
  rfl

private theorem deg1L1_transport (cx : Ctx) (X : JMat T) (f fl : List T → T)
    (ll : Tree T) (b : Buf T) (he : cx.earlyExit = false) :
    deg1L1 cx X f fl ll b = @deg1L1 T (totalScalar s) cx X f fl ll b := by
  simp only [deg1L1, retV, he, Bool.false_and, Bool.false_eq_true, ↓reduceIte, post_noEarly,
    @post_noEarly T (totalScalar s)]
  rfl

private theorem deg2_transport (cx : Ctx) (X : JMat T) (f : List T → T)
    (l r : Tree T) (b : Buf T) (he : cx.earlyExit = false) :
    deg2L0R0 cx X f l r b = @deg2L0R0 T (totalScalar s) cx X f l r b := by
  simp [deg2L0R0, retV, he, getArray, leafVal, filled, getFilled]
  rfl

private theorem deg2L_transport (cx : Ctx) (X : JMat T) (f : List T → T)
    (l : Tree T) (v : JVec T) (id : Ident) (b : Buf T) (he : cx.earlyExit = false) :
    deg2L0 cx X f l v id b = @deg2L0 T (totalScalar s) cx X f l v id b := by
  simp [deg2L0, retV, he, leafVal, inplaceMap]
  rfl

private theorem deg2R_transport (cx : Ctx) (X : JMat T) (f : List T → T)
    (r : Tree T) (v : JVec T) (id : Ident) (b : Buf T) (he : cx.earlyExit = false) :
    deg2R0 cx X f r v id b = @deg2R0 T (totalScalar s) cx X f r v id b := by
  simp [deg2R0, retV, he, leafVal, inplaceMap]
  rfl

private theorem branch0_transport (cx : Ctx) (X : JMat T) (f g : List T → T)
    (side : Side) (l1 l2 l3 : Tree T) (b : Buf T) (he : cx.earlyExit = false) :
    branch0 cx X f g side l1 l2 l3 b =
      @branch0 T (totalScalar s) cx X f g side l1 l2 l3 b := by
  cases side <;> simp [branch0, fused3, he, leafVal, getArray, retVIf, retV] <;> rfl

private theorem unfused1_transport (cx : Ctx) (f : Jl (List T → T))
    (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (he : cx.earlyExit = false) :
    unfused1 cx f ev b = @unfused1 T (totalScalar s) cx f ev b := by
  simp [unfused1, checked, he]

private theorem unfused2_transport (cx : Ctx) (f : Jl (List T → T))
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) (he : cx.earlyExit = false) :
    unfused2 cx f evL evR b = @unfused2 T (totalScalar s) cx f evL evR b := by
  simp [unfused2, checked, he]

private theorem deg1Dispatch_transport (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (c : Tree T) (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (he : cx.earlyExit = false)
    (hw : (Tree.branch op [c]).WF cx.D o.nops X.nrows) :
    deg1Dispatch cx o X op c ev b =
      @deg1Dispatch T (totalScalar s) cx o X op c ev b := by
  unfold deg1Dispatch
  by_cases hlim : operatorLimit < (opsOf o 1).length
  · simp only [hlim, ↓reduceIte]
    exact unfused1_transport cx _ ev b he
  · have hw' := hw
    simp only [Tree.WF, List.length_cons, List.length_nil] at hw'
    obtain ⟨f, _, hnif⟩ := nifOp_lookup o 1 op (by omega) hw'.2.1.1 hw'.2.1.2.1
    simp only [hlim, ↓reduceIte, hnif, jl_ok_bind]
    cases c with
    | const v => exact unfused1_transport cx _ ev b he
    | feature i => exact unfused1_transport cx _ ev b he
    | branch lop cs =>
      rcases cs with _ | ⟨ll, _ | ⟨lr, _ | ⟨a, rest⟩⟩⟩
      · exact unfused1_transport cx _ ev b he
      · simp only
        split
        · cases hfl : nifOp (opsOf o 1) lop with
          | error e => rfl
          | ok fl =>
            simp only [jl_ok_bind]
            exact deg1L1_transport cx X f fl ll b he
        · exact unfused1_transport cx _ ev b he
      · simp only
        split
        · cases hfl : nifOp (opsOf o 2) lop with
          | error e => rfl
          | ok fl =>
            simp only [jl_ok_bind]
            exact deg1L2_transport cx X f fl ll lr b he
        · exact unfused1_transport cx _ ev b he
      · exact unfused1_transport cx _ ev b he

private theorem deg2Dispatch_transport (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (l r : Tree T) (evL evR : Buf T → Jl (ResultOk T × Buf T))
    (b : Buf T) (he : cx.earlyExit = false) :
    deg2Dispatch cx o X op l r evL evR b =
      @deg2Dispatch T (totalScalar s) cx o X op l r evL evR b := by
  unfold deg2Dispatch
  by_cases hlim : operatorLimit < (opsOf o 2).length
  · simp only [hlim, ↓reduceIte]
    exact unfused2_transport cx _ evL evR b he
  · simp only [hlim, ↓reduceIte]
    cases hnif : nifOp (opsOf o 2) op with
    | error e => rfl
    | ok f =>
      simp only [jl_ok_bind]
      have hL : checked cx evR (fun x id b => deg2L0 cx X f l x id b) b =
          @checked T (totalScalar s) cx evR
            (fun x id b => @deg2L0 T (totalScalar s) cx X f l x id b) b := by
        simp only [checked, he, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          deg2L_transport cx X f l _ _ _ he]
      have hR : checked cx evL (fun x id b => deg2R0 cx X f r x id b) b =
          @checked T (totalScalar s) cx evL
            (fun x id b => @deg2R0 T (totalScalar s) cx X f r x id b) b := by
        simp only [checked, he, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          deg2R_transport cx X f r _ _ _ he]
      have hnum : @isNum T (totalScalar s) = isNum T := rfl
      simp only [hnum]
      split
      · exact deg2_transport cx X f l r b he
      · split
        · cases l with
          | const v => exact hR
          | feature i => exact hR
          | branch lop cs =>
            rcases cs with _ | ⟨ll, _ | ⟨lr, _ | ⟨a, rest⟩⟩⟩
            · exact hR
            · exact hR
            · simp only
              split
              · cases hnf : nifOp (opsOf o 2) lop with
                | error e => rfl
                | ok g =>
                  simp only [jl_ok_bind]
                  exact branch0_transport cx X f g .left ll lr r b he
              · exact hR
            · exact hR
        · split
          · cases r with
            | const v => exact hL
            | feature i => exact hL
            | branch rop cs =>
              rcases cs with _ | ⟨rl, _ | ⟨rr, _ | ⟨a, rest⟩⟩⟩
              · exact hL
              · exact hL
              · simp only
                split
                · cases hnf : nifOp (opsOf o 2) rop with
                  | error e => rfl
                  | ok g =>
                    simp only [jl_ok_bind]
                    exact branch0_transport cx X f g .right l rl rr b he
                · exact hL
              · exact hL
          · exact unfused2_transport cx _ evL evR b he

private theorem children_transport (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (he : cx.earlyExit = false) (cs : List (Tree T))
    (hcs : ∀ c ∈ cs, evalT cx o X c = @evalT T (totalScalar s) cx o X c) :
    evalChildren cx o X cs = @evalChildren T (totalScalar s) cx o X cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have ht := ih (fun c hc => hcs c (by simp [hc]))
    funext b
    simp only [evalChildren, hc, ht, he, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

private theorem evalT_transport (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (he : cx.earlyExit = false)
    (t : Tree T) (hw : t.WF cx.D o.nops X.nrows) :
    evalT cx o X t = @evalT T (totalScalar s) cx o X t := by
  induction t using Tree.induction with
  | hc v =>
    funext b
    simp only [evalT, he, Bool.not_false, Bool.true_or]
    rfl
  | hf i => rfl
  | hb op cs ih =>
    by_cases hcon : isConstantL cs = true
    · funext b
      unfold evalT
      simp only [hcon, ↓reduceIte, he]
      exact constPath_transport o X (.branch op cs) b
    have hcon' : isConstantL cs = false := by simpa using hcon
    have hw' := hw
    simp only [Tree.WF] at hw'
    have hch : ∀ c ∈ cs, evalT cx o X c = @evalT T (totalScalar s) cx o X c :=
      fun c hc => ih c hc (hw'.2.2 c hc)
    funext b
    unfold evalT
    simp only [hcon', Bool.false_eq_true, ↓reduceIte]
    rcases cs with _ | ⟨c, _ | ⟨r, _ | ⟨a, rest⟩⟩⟩
    · rfl
    · simp only
      rw [hch c (by simp)]
      exact deg1Dispatch_transport cx o X op c _ b he hw
    · simp only
      rw [hch c (by simp), hch r (by simp)]
      exact deg2Dispatch_transport cx o X op c r _ _ b he
    · simp only
      rw [hch c (by simp), hch r (by simp)]
      split
      · exact deg2Dispatch_transport cx o X op c r _ _ b he
      · rw [children_transport cx o X he _ hch]

theorem evalT_noEarly (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (he : cx.earlyExit = false)
    (hn : 1 ≤ X.ncols) (t : Tree T) (hw : t.WF cx.D o.nops X.nrows)
    (k : Nat) (b : Buf T)
    (hb : Good X.ncols (k + t.size) b) :
    ∃ id b', evalT cx o X t b = .ok (⟨canon o X t, true, id⟩, b') ∧ Good X.ncols k b' := by
  rw [evalT_transport cx o X he t hw]
  obtain ⟨_, _, hv⟩ := @evalT_valid T (totalScalar s) cx o X total_arraySound hn t hw
    (fun j hj => total_allValid o X (j + 1) ⟨by omega, by omega⟩ t hw)
  exact hv k b hb

theorem evalArr_noEarly (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (he : cx.earlyExit = false)
    (hn : 1 ≤ X.ncols) (t : Tree T) (hw : t.WF cx.D o.nops X.nrows)
    (b : Buf T) (hb : Good X.ncols t.size b) :
    evalArr cx o X t b = .ok (canon o X t, true) := by
  obtain ⟨id, b', hev, _⟩ := evalT_noEarly cx o X he hn t hw 0 b (by simpa using hb)
  simp [evalArr, hev, he]

theorem denotes_canon_wf (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hw : t.WF D o.nops X.nrows) : Denotes o X t (canon o X t) := by
  refine ⟨canon_size o X t, fun j h1 h2 => ?_⟩
  have hj : j - 1 < X.ncols := by omega
  rw [canon_eq, range_map_get _ _ _ hj]
  obtain ⟨v, hv⟩ := Tree.denoteRow_some o X j ⟨h1, h2⟩ t hw
  simp only [cv, vx, show j - 1 + 1 = j by omega]
  change some ((t.denoteRow o X j).getD JlScalar.undef) = t.denoteRow o X j
  rw [hv]
  rfl

theorem evalNoEarlyDenote_proof : evalNoEarlyDenote := by
  intro T _ ext impl D o X t hn hw _
  refine ⟨canon o X t, ?_, denotes_canon_wf o X t hw⟩
  exact evalArr_noEarly ⟨false, false, D⟩ o X rfl hn t hw .none trivial

theorem evalNoEarlyNoConst_proof : evalNoEarlyNoConst := by
  intro T _ ext impl D o X t hn hw _
  refine ⟨canon o X t, ?_, denotes_canon_wf o X t hw⟩
  exact evalArr_noEarly ⟨false, false, D⟩ o X rfl hn t hw .none trivial

/-- eval-noearly-fused-agree: since PR #268 the fused unary kernels apply the
outer operator whenever early exit is off, so fused and unfused evaluation
agree (both give the denotation). -/
theorem evalNoEarlyFusedAgree_proof : evalNoEarlyFusedAgree := by
  intro T _ ext impl D o X t hn hw _
  change (evalArr ⟨false, true, D⟩ o X t .none).map (·.1.toList) =
    (evalArr ⟨false, false, D⟩ o X t .none).map (·.1.toList)
  rw [evalArr_noEarly ⟨false, true, D⟩ o X rfl hn t hw .none trivial,
    evalArr_noEarly ⟨false, false, D⟩ o X rfl hn t hw .none trivial]

theorem evalNoEarlyFusedKeep_proof : evalNoEarlyFusedKeep := by
  intro T _ ext impl D o X t hn hw hnc _
  exact evalNoEarlyFusedAgree_proof T ext impl D o X t hn hw hnc

private def keepFirst : List JF → JF := fun xs => xs.headD .nan
private def keepOps : OpEnum JF := ⟨[[keepFirst]]⟩
private def invalidSample : JMat JF := ⟨1, 1, #[.nan], rfl⟩
private def nestedUnary : Tree JF := .branch 1 [.branch 1 [.feature 1]]

private theorem keepOps_invalid : UnaryKeepsInvalid keepOps := by
  intro op f hf x _
  have hb := (keepOps.lookup_some_iff 1 op).1 ⟨f, hf⟩
  have hop : op = 1 := by simp [keepOps, OpEnum.nops] at hb; omega
  subst op
  have hfun : keepFirst = f := by simpa [keepOps, OpEnum.lookup] using hf
  rw [← hfun]
  rfl

example : 1 ≤ invalidSample.ncols ∧ nestedUnary.WF 2 keepOps.nops invalidSample.nrows ∧
    noConstBranch nestedUnary = true ∧
    ∃ out, evalArr ⟨false, false, 2⟩ keepOps invalidSample nestedUnary .none = .ok (out, true) ∧
      Denotes keepOps invalidSample nestedUnary out := by
  have hn : 1 ≤ invalidSample.ncols := by decide +kernel
  have hw : nestedUnary.WF 2 keepOps.nops invalidSample.nrows := by
    simp [nestedUnary, Tree.WF, keepOps, OpEnum.nops, invalidSample]
  have hc : noConstBranch nestedUnary = true := by
    simp [nestedUnary, noConstBranch, noConstBranchL, isConstant, isConstantL]
  refine ⟨hn, hw, hc, canon keepOps invalidSample nestedUnary, ?_,
    denotes_canon_wf keepOps invalidSample nestedUnary hw⟩
  exact evalArr_noEarly ⟨false, false, 2⟩ keepOps invalidSample rfl
    hn nestedUnary hw .none trivial

example : 1 ≤ invalidSample.ncols ∧ nestedUnary.WF 2 keepOps.nops invalidSample.nrows ∧
    noConstBranch nestedUnary = true ∧ UnaryKeepsInvalid keepOps ∧
    (evalArr ⟨false, true, 2⟩ keepOps invalidSample nestedUnary .none).map (·.1.toList) =
      (evalArr ⟨false, false, 2⟩ keepOps invalidSample nestedUnary .none).map (·.1.toList) := by
  have hn : 1 ≤ invalidSample.ncols := by decide +kernel
  have hw : nestedUnary.WF 2 keepOps.nops invalidSample.nrows := by
    simp [nestedUnary, Tree.WF, keepOps, OpEnum.nops, invalidSample]
  have hc : noConstBranch nestedUnary = true := by
    simp [nestedUnary, noConstBranch, noConstBranchL, isConstant, isConstantL]
  refine ⟨hn, hw, hc, keepOps_invalid, ?_⟩
  rw [evalArr_noEarly ⟨false, true, 2⟩ keepOps invalidSample rfl hn nestedUnary hw .none trivial,
    evalArr_noEarly ⟨false, false, 2⟩ keepOps invalidSample rfl hn nestedUnary hw .none trivial]

end DynExpr.Eval

