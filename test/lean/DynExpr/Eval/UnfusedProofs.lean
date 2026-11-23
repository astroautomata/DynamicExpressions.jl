import DynExpr.Eval.Top

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

private def ScalarStatus (o : OpEnum T) (t : Tree T) (r : T × Bool) : Prop :=
  valid r.1 = r.2 ∧ (r.2 = true → ∀ x, AllValid o x t ∧ r.1 = vx o x t)

private def ScalarListStatus (o : OpEnum T) (cs : List (Tree T)) :
    (T × Bool) ⊕ List T → Prop
  | .inl r => r.2 = false ∧ valid r.1 = false
  | .inr vs => ∀ x, (∀ c ∈ cs, AllValid o x c) ∧ vs = cs.map (vx o x)

private theorem constEvalL_total (o : OpEnum T) (cs : List (Tree T))
    (hc : ∀ c ∈ cs, ∃ r, constEval o c = .ok r ∧ ScalarStatus o c r) :
    ∃ r, constEvalL o cs = .ok r ∧ ScalarListStatus o cs r := by
  induction cs with
  | nil => exact ⟨.inr [], rfl, fun _ => ⟨by simp, rfl⟩⟩
  | cons c cs ih =>
    obtain ⟨⟨v, ok⟩, hv, hs⟩ := hc c (by simp)
    simp only [ScalarStatus] at hs
    cases ok with
    | false => exact ⟨.inl (v, false), by simp [constEvalL, hv], rfl, hs.1⟩
    | true =>
      obtain ⟨r, hr, hsr⟩ := ih (by intro c hm; exact hc c (by simp [hm]))
      cases r with
      | inl r => exact ⟨.inl r, by simp [constEvalL, hv, hr], hsr⟩
      | inr vs =>
        refine ⟨.inr (v :: vs), by simp [constEvalL, hv, hr], ?_⟩
        intro x
        obtain ⟨hvx, he⟩ := hs.2 rfl x
        obtain ⟨hcs, hvs⟩ := hsr x
        exact ⟨by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hvx; exact hcs a ha,
          by simp [he, hvs]⟩

private theorem constEval_total (o : OpEnum T) (D nf : Nat) (t : Tree T) :
    t.WF D o.nops nf → isConstant t = true →
    ∃ r, constEval o t = .ok r ∧ ScalarStatus o t r := by
  induction t using Tree.induction with
  | hc v =>
    intro hw hcon
    exact ⟨(v, valid v), rfl, rfl, by
      intro hv x; exact ⟨by simpa [AllValid] using hv, by simp [vx, Tree.denote]⟩⟩
  | hf f => intro hw hcon; simp [isConstant] at hcon
  | hb op cs ih =>
    intro hw hcon
    simp only [Tree.WF] at hw
    have hcs : ∀ c ∈ cs, isConstant c = true := by
      have hl : isConstantL cs = true := hcon
      clear hw ih hcon
      induction cs with
      | nil => simp
      | cons c cs ihl =>
        simp only [isConstantL, Bool.and_eq_true] at hl
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hl.1
        · exact ihl hl.2 a ha
    obtain ⟨r, hr, hs⟩ := constEvalL_total o cs (by
      intro c hc; exact ih c hc (hw.2.2 c hc) (hcs c hc))
    cases r with
    | inl r =>
      refine ⟨r, by simp [constEval, hr], ?_⟩
      simp only [ScalarListStatus] at hs
      exact ⟨hs.2.trans hs.1.symm, by intro ht; rw [hs.1] at ht; cases ht⟩
    | inr vs =>
      obtain ⟨g, hg, hnif⟩ := nifOp_lookup o cs.length op hw.1.1 hw.2.1.1 hw.2.1.2.1
      have hidx := idxOp_lookup o cs.length op g hw.1.1 hg
      refine ⟨(g vs, valid (g vs)), by simp [constEval, hr, hnif, hidx], rfl, ?_⟩
      intro hv x
      obtain ⟨hchildren, hvs⟩ := hs x
      have hvx := vx_branch o x op cs g hg (fun c hc => AllValid.some o x c (hchildren c hc))
      have hden : (Tree.branch op cs).denote o x = some (g vs) := by
        simp [Tree.denote, hg, mapM_opt_eq (Tree.denote o x) (vx o x) cs
          (fun c hc => AllValid.some o x c (hchildren c hc)), hvs]
      exact ⟨by simp only [AllValid]; exact ⟨hchildren, g vs, hden, hv⟩, by rw [hvx, hvs]⟩

private def RootChildren (o : OpEnum T) (X : JMat T) : Tree T → Prop
  | .const _ | .feature _ => True
  | .branch _ cs => ∀ j, j < X.ncols → ∀ c ∈ cs, AllValid o (col X (j + 1)) c

private theorem canon_valid (o : OpEnum T) (X : JMat T) (t : Tree T) (D : Nat)
    (hA : ArrayValidExact T) (hw : t.WF D o.nops X.nrows) (hc : RootChildren o X t)
    (hv : isValidArray (canon o X t) = true) :
    ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t := by
  intro j hj
  have hm : cv o X t j ∈ (canon o X t).toList := by
    simp only [canon, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  have hvalid := (hA _).1 hv _ hm
  obtain ⟨v, hden⟩ := Tree.denoteRow_some o X (j + 1) ⟨by omega, by omega⟩ t hw
  have hvx : vx o (col X (j + 1)) t = v := by
    change t.denote o (col X (j + 1)) = some v at hden
    simp [vx, hden]
  have hval : valid v = true := by simpa [cv, hvx] using hvalid
  cases t with
  | const a =>
    simp only [Tree.denoteRow, Tree.denote, Option.some.injEq] at hden
    simpa [AllValid, ← hden] using hval
  | feature f =>
    simp only [AllValid]
    exact ⟨v, by simpa [col, Tree.denoteRow, Tree.denote] using hden, hval⟩
  | branch op cs =>
    simp only [AllValid]
    exact ⟨hc j hj, v, hden, hval⟩

private def ArrayStatus (o : OpEnum T) (X : JMat T) (t : Tree T) (r : ResultOk T) : Prop :=
  r.ok = true → r.x = canon o X t ∧
    (isValidArray r.x = true → ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t)

private theorem canonical_status (o : OpEnum T) (X : JMat T) (t : Tree T) (D : Nat)
    (id : Ident) (hA : ArrayValidExact T) (hw : t.WF D o.nops X.nrows)
    (hc : RootChildren o X t) : ArrayStatus o X t ⟨canon o X t, true, id⟩ := by
  intro h
  exact ⟨rfl, canon_valid o X t D hA hw hc⟩

private theorem constPath_status (o : OpEnum T) (X : JMat T) (D : Nat) (t : Tree T)
    (hw : t.WF D o.nops X.nrows) (hcon : isConstant t = true) :
    ∃ r, constPath o X t .none = .ok (r, .none) ∧ ArrayStatus o X t r := by
  obtain ⟨⟨v, ok⟩, hr, hs⟩ := constEval_total o D X.nrows t hw hcon
  cases ok with
  | false => exact ⟨⟨JVec.fill X.ncols JlScalar.undef, false, .fresh⟩,
      by simp [constPath, hr, getArray, nextId], by simp [ArrayStatus]⟩
  | true =>
    have hv : ∀ j, j < X.ncols → cv o X t j = v := by
      intro j hj; exact (hs.2 rfl (col X (j + 1))).2.symm
    have hcanon := canon_fill o X t v hv
    refine ⟨⟨JVec.fill X.ncols v, true, .fresh⟩, by simp [constPath, hr, filled, getFilled, nextId], ?_⟩
    intro hok
    exact ⟨hcanon.symm, fun _ j hj => (hs.2 rfl (col X (j + 1))).1⟩

private def ChildrenStatus (o : OpEnum T) (X : JMat T) (cs : List (Tree T)) :
    (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T) → Prop
  | .inl (r, b) => r.ok = false ∧ b = .none
  | .inr (xs, b) => b = .none ∧ xs.map Prod.fst = cs.map (canon o X) ∧
      ∀ j, j < X.ncols → ∀ c ∈ cs, AllValid o (col X (j + 1)) c

private theorem evalChildren_status (D : Nat) (o : OpEnum T) (X : JMat T)
    (cs : List (Tree T))
    (hc : ∀ c ∈ cs, ∃ r, evalT ⟨true, false, D⟩ o X c .none = .ok (r, .none) ∧ ArrayStatus o X c r) :
    ∃ r, evalChildren ⟨true, false, D⟩ o X cs .none = .ok r ∧ ChildrenStatus o X cs r := by
  induction cs with
  | nil => exact ⟨.inr ([], .none), rfl, rfl, rfl, by simp⟩
  | cons c cs ih =>
    obtain ⟨r, hr, hs⟩ := hc c (by simp)
    cases hok : r.ok with
    | false => exact ⟨.inl (r, .none), by simp [evalChildren, hr, hok], hok, rfl⟩
    | true =>
      cases hval : isValidArray r.x with
      | false => exact ⟨.inl (⟨r.x, false, r.id⟩, .none),
          by simp [evalChildren, hr, hok, hval], rfl, rfl⟩
      | true =>
        obtain ⟨hcanon, hgood⟩ := hs hok
        obtain ⟨res, hres, hst⟩ := ih (by intro c hm; exact hc c (by simp [hm]))
        cases res with
        | inl a => exact ⟨.inl a, by simp [evalChildren, hr, hok, hval, hres], hst⟩
        | inr a =>
          rcases a with ⟨xs, b⟩
          obtain ⟨rfl, hxs, hvalid⟩ := hst
          refine ⟨.inr ((r.x, r.id) :: xs, .none),
            by simp [evalChildren, hr, hok, hval, hres], rfl, by simp [hcanon, hxs], ?_⟩
          intro j hj a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact hgood hval j hj
          · exact hvalid j hj a ha

private theorem degnFinish_status (D : Nat) (o : OpEnum T) (X : JMat T)
    (op : Nat) (cs : List (Tree T)) (hA : ArrayValidExact T)
    (hw : (Tree.branch op cs).WF D o.nops X.nrows)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T))
    (hs : ChildrenStatus o X cs res) :
    ∃ r, degnFinish o cs.length op res = .ok (r, .none) ∧ ArrayStatus o X (.branch op cs) r := by
  have hw' := hw
  simp only [Tree.WF] at hw'
  cases res with
  | inl a =>
    rcases a with ⟨r, b⟩
    obtain ⟨hok, rfl⟩ := hs
    exact ⟨r, rfl, by simp [ArrayStatus, hok]⟩
  | inr a =>
    rcases a with ⟨xs, b⟩
    obtain ⟨rfl, hxs, hvalid⟩ := hs
    obtain ⟨g, hg, hnif⟩ := nifOp_lookup o cs.length op hw'.1.1 hw'.2.1.1 hw'.2.1.2.1
    have hne : cs ≠ [] := by intro he; simp [he] at hw'
    have heval := degnEval_canon o X g cs hne
    have hcanon := canon_branch o X op cs g hg hvalid
    refine ⟨⟨canon o X (.branch op cs), true, (xs.head?.map Prod.snd).getD .fresh⟩, ?_, ?_⟩
    · simp only [degnFinish, hnif, jl_ok_bind, hxs, heval, ← hcanon, jl_pure]
    · exact canonical_status o X _ D _ hA hw hvalid


private theorem deg1_unfused (D : Nat) (o : OpEnum T) (X : JMat T) (op : Nat)
    (c : Tree T) (g : List T → T) (hg : o.lookup 1 op = some g)
    (hnif : nifOp (opsOf o 1) op = .ok g) (b : Buf T) :
    deg1Dispatch ⟨true, false, D⟩ o X op c (evalT ⟨true, false, D⟩ o X c) b =
      unfused1 ⟨true, false, D⟩ (.ok g) (evalT ⟨true, false, D⟩ o X c) b := by
  have hidx := idxOp_lookup o 1 op g (by omega) hg
  unfold deg1Dispatch
  split <;> simp [hidx, hnif]

private theorem deg2_unfused (D : Nat) (o : OpEnum T) (X : JMat T) (op : Nat)
    (l r : Tree T) (g : List T → T) (hg : o.lookup 2 op = some g)
    (hnif : nifOp (opsOf o 2) op = .ok g) (b : Buf T) :
    deg2Dispatch ⟨true, false, D⟩ o X op l r
      (evalT ⟨true, false, D⟩ o X l) (evalT ⟨true, false, D⟩ o X r) b =
      unfused2 ⟨true, false, D⟩ (.ok g)
        (evalT ⟨true, false, D⟩ o X l) (evalT ⟨true, false, D⟩ o X r) b := by
  have hidx := idxOp_lookup o 2 op g (by omega) hg
  simp [deg2Dispatch, hidx, hnif]

private theorem unfused1_children (D : Nat) (o : OpEnum T) (X : JMat T) (op : Nat)
    (c : Tree T) (g : List T → T) (hnif : nifOp (opsOf o 1) op = .ok g) (b : Buf T) :
    unfused1 ⟨true, false, D⟩ (.ok g) (evalT ⟨true, false, D⟩ o X c) b =
      (do let res ← evalChildren ⟨true, false, D⟩ o X [c] b
          degnFinish o 1 op res) := by
  cases he : evalT ⟨true, false, D⟩ o X c b with
  | error e => simp [unfused1, checked, evalChildren, he]
  | ok a =>
    rcases a with ⟨r, b1⟩
    cases hok : r.ok <;> cases hval : isValidArray r.x <;>
      simp [unfused1, checked, evalChildren, he, hok, hval, degnFinish, hnif]

private theorem unfused2_children (D : Nat) (o : OpEnum T) (X : JMat T) (op : Nat)
    (l r : Tree T) (g : List T → T) (hnif : nifOp (opsOf o 2) op = .ok g) (b : Buf T) :
    unfused2 ⟨true, false, D⟩ (.ok g)
      (evalT ⟨true, false, D⟩ o X l) (evalT ⟨true, false, D⟩ o X r) b =
      (do let res ← evalChildren ⟨true, false, D⟩ o X [l, r] b
          degnFinish o 2 op res) := by
  cases he : evalT ⟨true, false, D⟩ o X l b with
  | error e => simp [unfused2, checked, evalChildren, he]
  | ok a =>
    rcases a with ⟨rl, b1⟩
    cases hlok : rl.ok <;> cases hlval : isValidArray rl.x
    all_goals simp [unfused2, checked, evalChildren, he, hlok, hlval, degnFinish]
    cases hr : evalT ⟨true, false, D⟩ o X r b1 with
    | error e => simp
    | ok a =>
      rcases a with ⟨rr, b2⟩
      cases hrok : rr.ok <;> cases hrval : isValidArray rr.x <;>
        simp [hrok, hrval, hnif]

private theorem evalT_branch_unfused (D : Nat) (o : OpEnum T) (X : JMat T)
    (op : Nat) (cs : List (Tree T)) (hw : (Tree.branch op cs).WF D o.nops X.nrows)
    (hcon : isConstantL cs = false) :
    evalT ⟨true, false, D⟩ o X (.branch op cs) .none =
      (do let res ← evalChildren ⟨true, false, D⟩ o X cs .none
          degnFinish o cs.length op res) := by
  have hw' := hw
  simp only [Tree.WF] at hw'
  rcases cs with _ | ⟨c, _ | ⟨r, _ | ⟨s, rest⟩⟩⟩
  · simp at hw'
  · obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 1 op (by omega) hw'.2.1.1 (by simpa using hw'.2.1.2.1)
    simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte]
    rw [deg1_unfused D o X op c g hg hnif, unfused1_children D o X op c g hnif]
    rfl
  · obtain ⟨g, hg, hnif⟩ := nifOp_lookup o 2 op (by omega) hw'.2.1.1 (by simpa using hw'.2.1.2.1)
    simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte]
    rw [deg2_unfused D o X op c r g hg hnif, unfused2_children D o X op c r g hnif]
    rfl
  · have hD : D ≠ 2 := by have := hw'.1.2.1; simp only [List.length_cons] at this; omega
    simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte, hD]
    congr 1

private theorem evalT_status (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (t : Tree T) :
    t.WF D o.nops X.nrows →
    ∃ r, evalT ⟨true, false, D⟩ o X t .none = .ok (r, .none) ∧ ArrayStatus o X t r := by
  induction t using Tree.induction with
  | hc v =>
    intro hw
    have hcanon := canon_fill o X (.const v) v (fun j hj => cv_const o X v j)
    refine ⟨⟨canon o X (.const v), valid v, .fresh⟩, ?_, ?_⟩
    · simp [evalT, getFilled, nextId, hcanon]
    · intro h
      exact ⟨rfl, fun _ j _ => by simpa [AllValid] using h⟩
  | hf f =>
    intro hw
    have hw' := hw
    simp only [Tree.WF] at hw'
    have hr := rowInb_canon o X f hw'.1 hw'.2.1
    refine ⟨⟨canon o X (.feature f), true, .fresh⟩, ?_, canonical_status o X _ D _ hA hw trivial⟩
    simp [evalT, getFeature, hr, nextId, chk_ok X f hw'.1 hw'.2.1]
  | hb op cs ih =>
    intro hw
    cases hcon : isConstantL cs with
    | true =>
      obtain ⟨r, hr, hs⟩ := constPath_status o X D (.branch op cs) hw hcon
      refine ⟨r, ?_, hs⟩
      unfold evalT
      simp only [hcon, ↓reduceIte, hr]
    | false =>
      have hw' := hw
      simp only [Tree.WF] at hw'
      obtain ⟨res, hr, hs⟩ := evalChildren_status D o X cs (by
        intro c hc; exact ih c hc (hw'.2.2 c hc))
      obtain ⟨r, hfinish, hstatus⟩ := degnFinish_status D o X op cs hA hw res hs
      refine ⟨r, ?_, hstatus⟩
      rw [evalT_branch_unfused D o X op cs hw hcon, hr]
      simp only [jl_ok_bind, hfinish]

theorem evalUnfusedFlag_proof : evalUnfusedFlag := by
  intro T inst ext impl D o X t hA hn hw
  obtain ⟨r, hr, hs⟩ := evalT_status D o X hA t hw
  let ok := r.ok && isValidArray r.x
  have heval : evalArr ⟨true, false, D⟩ o X t .none = .ok (r.x, ok) := by
    simp [evalArr, hr, ok]
  have hsound : ok = true → ∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t := by
    intro hok
    have hp : r.ok = true ∧ isValidArray r.x = true := by simpa [ok] using hok
    obtain ⟨hok, hvalid⟩ := hp
    have hgood := (hs hok).2 hvalid
    intro j hj hjn
    simpa [show j - 1 + 1 = j by omega] using hgood (j - 1) (by omega)
  refine ⟨r.x, ok, heval, ⟨hsound, ?_⟩, ?_⟩
  · intro hv
    have hAs : ArrayValidSound T := fun a ha => (hA a).2 ha
    have hsuccess := evalArr_valid ⟨true, false, D⟩ o X t .none hAs hn hw (shift_valid o X t hv) trivial
    have he : (r.x, ok) = (canon o X t, true) := Except.ok.inj (heval.symm.trans hsuccess)
    exact congrArg Prod.snd he
  · intro hok
    have hv := shift_valid o X t (hsound hok)
    have hp : r.ok = true ∧ isValidArray r.x = true := by simpa [ok] using hok
    have hcanon := (hs hp.1).1
    rw [hcanon]
    exact denotes_canon o X t hv

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

example : ArrayValidExact Nat ∧ 1 ≤ (⟨1, 1, #[7], rfl⟩ : JMat Nat).ncols ∧
    (Tree.const 7).WF 2 (OpEnum.nops (⟨[]⟩ : OpEnum Nat)) 1 := by
  simp [ArrayValidExact, isValidArray, valid, JlScalar.floatLike, JlValue.valid, Tree.WF]


end DynExpr.Eval
