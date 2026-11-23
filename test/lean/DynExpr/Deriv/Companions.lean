import DynExpr.Deriv.GradProofs

/-! Shape, validity, bounds and empty-input properties of the gradient,
directional and pullback evaluators, with their companions. -/

namespace DynExpr.Deriv

@[simp] private theorem okBind' (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem okPure' (a : α) : (pure a : Jl α) = .ok a := rfl

/-- For every well-formed tree and matrix, when no gradients are requested
(`variable=true` with zero features, or `variable=false` with zero constants)
the gradient has shape 0-by-nsamples for a non-`Array` input (view/transpose)
as it does for `Array`: zero gradients take the `fill_similar` branch,
src/EvaluateDerivative.jl:380-384. -/
def genericZeroShape : Prop :=
  ∀ (m : Mode) (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    nGradients m X.nrows (scalarConstants t).length = 0 →
    ∃ r, eval_grad_tree_array .generic m o X t = .ok r ∧
      r.gradient.nrows = 0 ∧ r.gradient.ncols = X.ncols
theorem genericZeroShape_proof : genericZeroShape := by
  intro m o X t D hwf hcap hzero
  obtain ⟨r, hr, ⟨_, hnr, hnc, _, _⟩, _⟩ := gradientModes_proof .generic m o X t D hwf hcap
  exact ⟨r, hr, hnr.trans hzero, hnc⟩
example : (Tree.feature 1 : Tree JF).WF 2 arithmetic.nops twoSampleOnes.nrows ∧
    nGradients .constants twoSampleOnes.nrows (scalarConstants (Tree.feature 1 : Tree JF)).length = 0 := by
  simp [Tree.WF, twoSampleOnes, nGradients, scalarConstants]

/-- Every result of the gradient traversal reports completion exactly when its
primal and gradient values are all finite. -/
def Checked (r : GradResult) : Prop :=
  r.complete = (r.primal.all JF.valid && r.gradient.columns.all (fun col => col.all JF.valid))

private theorem checkResult_checked (r : GradResult) (h : r.complete = true) :
    Checked (checkResult r) := by
  simp [Checked, checkResult, h]

private theorem deg0_complete (s : Storage) (m : Mode) (nf ng : Nat) (vals : List JF) (c : Bool)
    (i : Nat) (r : GradResult) (h : grad_deg0_eval s m nf ng vals c i = .ok r) :
    r.complete = true := by
  unfold grad_deg0_eval at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

private theorem kernel_complete (op : DOp) (ns : Nat) (rs : List GradResult) (r : GradResult)
    (h : gradKernel op ns rs = .ok r) : r.complete = true := by
  unfold gradKernel at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

private theorem map_check_ok (x : Jl GradResult) (r : GradResult)
    (h : x.map checkResult = .ok r) : ∃ r0, x = .ok r0 ∧ r = checkResult r0 := by
  cases x with
  | error e => cases h
  | ok r0 => cases h; exact ⟨r0, rfl, rfl⟩

private theorem collect_mem (P : GradResult → Prop) :
    ∀ (xs : List (Jl GradResult)) (rs : List GradResult),
      (∀ x ∈ xs, ∀ r, x = .ok r → P r) → collectChildren xs = .ok rs → ∀ r ∈ rs, P r := by
  intro xs
  induction xs with
  | nil => intro rs _ h; cases h; simp
  | cons a as ih =>
    intro rs hall h
    cases ha : a with
    | error e => rw [ha] at h; cases h
    | ok r =>
      have hr := hall a (by simp) r ha
      rw [ha] at h
      simp only [collectChildren, okBind'] at h
      split at h
      · cases h; simpa using hr
      · cases hc : collectChildren as with
        | error e => rw [hc] at h; cases h
        | ok rs' =>
          rw [hc] at h
          simp only [okBind'] at h
          have hrs' := ih rs' (fun x hx => hall x (by simp [hx])) hc
          split at h
          · rename_i failed hf
            cases h
            intro r' hr'
            simp only [List.mem_singleton] at hr'
            subst hr'
            exact hrs' _ (List.mem_of_find?_eq_some hf)
          · cases h
            intro r' hr'
            rcases List.mem_cons.1 hr' with rfl | hr'
            · exact hr
            · exact hrs' r' hr'

private theorem gradTreeList_mem (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (ng : Nat) :
    ∀ (cs : List (Tree JF)) (st : Nat) (x : Jl GradResult), x ∈ gradTreeList s m o X ng st cs →
      ∃ c ∈ cs, ∃ st', x = gradTree s m o X ng st' c := by
  intro cs
  induction cs with
  | nil => intro st x hx; simp [gradTreeList] at hx
  | cons c cs ih =>
    intro st x hx
    simp only [gradTreeList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨c, by simp, st, rfl⟩
    · obtain ⟨c', hc', st', h⟩ := ih _ x hx
      exact ⟨c', by simp [hc'], st', h⟩

theorem gradTree_checked (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (ng : Nat) :
    ∀ (t : Tree JF) (start : Nat) (r : GradResult),
      gradTree s m o X ng start t = .ok r → Checked r := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro start r h
    rw [gradTree_const] at h
    obtain ⟨r0, h0, rfl⟩ := map_check_ok _ _ h
    exact checkResult_checked r0 (deg0_complete _ _ _ _ _ _ _ r0 h0)
  | hf k =>
    intro start r h
    rw [gradTree_feature] at h
    cases hrow : X.row k with
    | error e => rw [hrow] at h; cases h
    | ok vals =>
      rw [hrow] at h
      simp only [okBind'] at h
      obtain ⟨r0, h0, rfl⟩ := map_check_ok _ _ h
      exact checkResult_checked r0 (deg0_complete _ _ _ _ _ _ _ r0 h0)
  | hb idx cs ih =>
    intro start r h
    rw [gradTree_branch] at h
    cases hc : collectChildren (gradTreeList s m o X ng start cs) with
    | error e => rw [hc] at h; cases h
    | ok rs =>
      rw [hc] at h
      simp only [okBind'] at h
      have hall := collect_mem Checked _ rs (by
        intro x hx r' hr'
        obtain ⟨c, hcm, st', rfl⟩ := gradTreeList_mem s m o X ng cs start x hx
        exact ih c hcm st' r' hr') hc
      split at h
      · rename_i failed hf
        cases h
        exact hall _ (List.mem_of_find?_eq_some hf)
      · split at h
        · cases h
        · obtain ⟨r0, h0, rfl⟩ := map_check_ok _ _ h
          exact checkResult_checked r0 (kernel_complete _ _ _ r0 h0)

/-- For every well-formed tree, operator enum, matrix, storage and mode,
`eval_grad_tree_array` succeeds and reports completion exactly when every
returned primal and gradient value is finite: leaves and fused kernels are
checked, and an incomplete child is returned unchanged,
src/EvaluateDerivative.jl:242-246,305-313. -/
def gradientValidity : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    ∃ r, eval_grad_tree_array s m o X t = .ok r ∧
      r.complete = (r.primal.all JF.valid && r.gradient.columns.all (fun col => col.all JF.valid))
theorem gradientValidity_proof : gradientValidity := by
  intro s m o X t D hwf hcap
  obtain ⟨r, hr, _⟩ := gradientModes_proof s m o X t D hwf hcap
  exact ⟨r, hr, gradTree_checked s m o X _ t 1 r (by unfold eval_grad_tree_array at hr; exact hr)⟩

/-- For every branch whose first child's gradient call returns an incomplete
result, the branch returns that result unchanged without evaluating later
children, so a later child that would throw (for example an out-of-range
feature) is never reached, src/EvaluateDerivative.jl:302-315. The child's
success on well-formed inputs is proven by deriv-gradient-modes. -/
def earlyExit : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (ng start idx : Nat) (c : Tree JF)
    (cs : List (Tree JF)) (r : GradResult),
    gradTree s m o X ng start c = .ok r → r.complete = false →
    gradTree s m o X ng start (.branch idx (c :: cs)) = .ok r
theorem earlyExit_proof : earlyExit := by
  intro s m o X ng start idx c cs r h hc
  rw [gradTree_branch]
  simp only [gradTreeList, collectChildren, h, okBind', hc, Bool.not_false, ite_true]
  simp [firstIncomplete, hc]
example : ∃ r, gradTree .dense .features ⟨[]⟩ twoSampleOnes 1 1 (.const .nan) = .ok r ∧
    r.complete = false :=
  ⟨_, by rw [gradTree_const]; rfl, rfl⟩

/-- For every well-formed tree and every matrix with zero samples, the pullback
with an empty cotangent returns zero constant sensitivities (the primal rule
accepts zero samples): an empty `dY` takes the `fill_similar` branch instead of
`sum`, src/ChainRules.jl:57-81. Companion: deriv-pullback-end-to-end describes
every input with at least one sample. -/
def emptyPullback : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat) (dComplete : Bool),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 → X.ncols = 0 →
    ∃ res, (EvalPullback.mk t X o).call [] dComplete = .ok res ∧
      extract_gradient res.tree t = List.replicate (scalarConstants t).length zero
theorem emptyPullback_proof : emptyPullback := by
  intro o X t D dComplete hwf hcap hns
  obtain ⟨r, hr, ⟨_, hnr, hnc, _, _⟩, _⟩ := gradientModes_proof .dense .both o X t D hwf hcap
  have hpull : ∀ a : GradMatrix, a.nrows = X.nrows + (scalarConstants t).length → a.ncols = 0 →
      ∃ res, (do
        let constants ← constantPullback X.nrows a []
        let features ← featurePullback X.nrows a []
        pure (⟨⟨t, constants⟩, features, true, true⟩ : PullbackResult) : Jl PullbackResult) =
          .ok res ∧
        extract_gradient res.tree t = List.replicate (scalarConstants t).length zero := by
    intro a h1 h2
    exact ⟨⟨⟨t, List.replicate (a.nrows - X.nrows) zero⟩, ⟨X.nrows, a.ncols,
      a.columns.zipIdx.map fun (col, j) => (col.take X.nrows).map fun v => v * ([] : List JF)[j]!⟩,
      true, true⟩, by simp [constantPullback, featurePullback, h2],
      by simp [extract_gradient, h1]⟩
  unfold EvalPullback.call
  rw [hr]
  simp only [okBind']
  exact hpull _ (by split <;> simp [invalidateMatrix, hnr, nGradients])
    (by split <;> simp [invalidateMatrix, hnc, hns])
example : (Tree.const one : Tree JF).WF 2 (DEnum.nops ⟨[]⟩) (⟨1, 0, #[], by decide⟩ : JMat JF).nrows ∧
    (⟨1, 0, #[], by decide⟩ : JMat JF).nrows + (scalarConstants (Tree.const one : Tree JF)).length ≤ 65535 := by
  simp [Tree.WF, scalarConstants]

/-- In every mode and storage, the gradient evaluator never reaches an
out-of-range `@inbounds` access, src/EvaluateDerivative.jl:344-408. -/
def gradNoOutOfBounds : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat) (msg : String),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    eval_grad_tree_array s m o X t ≠ .error (.undefinedBehavior msg)
theorem gradNoOutOfBounds_proof : gradNoOutOfBounds := by
  intro s m o X t D msg hwf hcap
  obtain ⟨r, hr, _⟩ := gradientModes_proof s m o X t D hwf hcap
  rw [hr]
  intro h
  cases h
example : (Tree.const one : Tree JF).WF 2 (DEnum.nops ⟨[]⟩) oneSample.nrows ∧
    oneSample.nrows + (scalarConstants (Tree.const one : Tree JF)).length ≤ 65535 := by
  refine ⟨by simp [Tree.WF], by simp [scalarConstants, oneSample]⟩

private theorem map_check_error (x : Jl GradResult) (e : JlError)
    (h : x.map checkResult = .error e) : x = .error e := by
  cases x with
  | error e' => cases h; rfl
  | ok r => cases h

private theorem deg0_error (s : Storage) (m : Mode) (nf ng : Nat) (vals : List JF) (c : Bool)
    (i : Nat) (e : JlError) (h : grad_deg0_eval s m nf ng vals c i = .error e) :
    e = .boundsError := by
  unfold grad_deg0_eval at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

private theorem deg0_shape (s : Storage) (m : Mode) (nf ng : Nat) (vals : List JF) (c : Bool)
    (i : Nat) (r : GradResult) (h : grad_deg0_eval s m nf ng vals c i = .ok r) :
    r.gradient.nrows = ng ∧ r.gradient.ncols = vals.length := by
  unfold grad_deg0_eval at h
  dsimp only at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

private theorem collect_error : ∀ (xs : List (Jl GradResult)) (e : JlError),
    collectChildren xs = .error e → ∃ x ∈ xs, x = .error e := by
  intro xs
  induction xs with
  | nil => intro e h; cases h
  | cons a as ih =>
    intro e h
    cases ha : a with
    | error e' =>
      rw [ha] at h
      cases h
      exact ⟨_, by simp, rfl⟩
    | ok r =>
      rw [ha] at h
      simp only [collectChildren, okBind'] at h
      split at h
      · cases h
      · cases hc : collectChildren as with
        | error e' =>
          rw [hc] at h
          cases h
          obtain ⟨x, hx, hxe⟩ := ih _ hc
          exact ⟨x, by simp [hx], hxe⟩
        | ok rs' =>
          rw [hc] at h
          simp only [okBind'] at h
          split at h <;> cases h

private theorem collect_ne_nil (xs : List (Jl GradResult)) (rs : List GradResult)
    (hxs : xs ≠ []) (h : collectChildren xs = .ok rs) : rs ≠ [] := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hxs
  cases ha : a with
  | error e => rw [ha] at h; cases h
  | ok r =>
    rw [ha] at h
    simp only [collectChildren, okBind'] at h
    split at h
    · cases h; simp
    · cases hc : collectChildren as with
      | error e => rw [hc] at h; cases h
      | ok rs' =>
        rw [hc] at h
        simp only [okBind'] at h
        split at h <;> (cases h; simp)

private theorem kernel_bounds (op : DOp) (ns ng : Nat) (rs : List GradResult) (hne : rs ≠ [])
    (hs : ∀ r ∈ rs, r.gradient.nrows = ng ∧ r.gradient.ncols = ns) :
    ∃ r, gradKernel op ns rs = .ok r ∧ r.gradient.nrows = ng ∧ r.gradient.ncols = ns := by
  obtain ⟨r0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := hs r0 (by simp)
  have hany : ((r0 :: rest).any fun r => decide (r.gradient.ncols < ns) ||
      decide (r.gradient.nrows < ng)) = false := by
    rw [List.any_eq_false]
    intro r hr
    have := hs r hr
    simp [this.1, this.2]
  unfold gradKernel
  simp only [List.getElem!_cons_zero, h0.1, hany, Bool.false_eq_true, and_false, ite_false]
  exact ⟨_, rfl, rfl, h0.2⟩

/-- On a well-formed tree, whatever the number of constants, every error of the
gradient traversal is the `BoundsError` of the checked row view and every
result has an `ng`-by-nsamples gradient, so the fused kernels' `@inbounds`
accesses stay in range, src/EvaluateDerivative.jl:344-408. -/
theorem gradTree_bounds (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (ng D : Nat) :
    ∀ (t : Tree JF) (start : Nat), t.WF D o.nops X.nrows →
      (∀ e, gradTree s m o X ng start t = .error e → e = .boundsError) ∧
      (∀ r, gradTree s m o X ng start t = .ok r →
        r.gradient.nrows = ng ∧ r.gradient.ncols = X.ncols) := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro start _
    rw [gradTree_const]
    refine ⟨fun e h => deg0_error _ _ _ _ _ _ _ e (map_check_error _ e h), fun r h => ?_⟩
    obtain ⟨r0, h0, rfl⟩ := map_check_ok _ _ h
    rw [checkResult_gradient]
    simpa using deg0_shape _ _ _ _ _ _ _ r0 h0
  | hf k =>
    intro start hwf
    simp only [Tree.WF] at hwf
    obtain ⟨vals, hvals, hsize⟩ := X.row_exists k hwf.1 hwf.2.1
    rw [gradTree_feature, hvals]
    simp only [okBind']
    refine ⟨fun e h => deg0_error _ _ _ _ _ _ _ e (map_check_error _ e h), fun r h => ?_⟩
    obtain ⟨r0, h0, rfl⟩ := map_check_ok _ _ h
    rw [checkResult_gradient]
    have hs := deg0_shape _ _ _ _ _ _ _ r0 h0
    exact ⟨hs.1, by rw [hs.2]; simpa using hsize⟩
  | hb idx cs ih =>
    intro start hwf
    simp only [Tree.WF] at hwf
    rw [gradTree_branch]
    have hlist : ∀ x ∈ gradTreeList s m o X ng start cs,
        (∀ e, x = .error e → e = .boundsError) ∧
        (∀ r, x = .ok r → r.gradient.nrows = ng ∧ r.gradient.ncols = X.ncols) := by
      intro x hx
      obtain ⟨c, hc, st, rfl⟩ := gradTreeList_mem s m o X ng cs start x hx
      exact ih c hc st (hwf.2.2 c hc)
    have hl : gradTreeList s m o X ng start cs ≠ [] := by
      cases cs with
      | nil => simp at hwf
      | cons c cs => simp [gradTreeList]
    obtain ⟨op, hop⟩ := lookup_exists o cs.length idx hwf.1.1 hwf.2.1.1 hwf.2.1.2.1
    cases hc : collectChildren (gradTreeList s m o X ng start cs) with
    | error e =>
      refine ⟨fun e' h => ?_, fun r h => by cases h⟩
      cases h
      obtain ⟨x, hx, hxe⟩ := collect_error _ _ hc
      exact (hlist x hx).1 _ hxe
    | ok rs =>
      simp only [okBind']
      have hrs := collect_mem (fun r => r.gradient.nrows = ng ∧ r.gradient.ncols = X.ncols) _ rs
        (fun x hx => (hlist x hx).2) hc
      cases hf : firstIncomplete rs with
      | some r =>
        refine ⟨fun e h => (by cases h), fun r' h => ?_⟩
        cases h
        exact hrs r (List.mem_of_find?_eq_some hf)
      | none =>
        obtain ⟨r0, hk, hn, hn'⟩ := kernel_bounds op X.ncols ng rs (collect_ne_nil _ rs hl hc) hrs
        simp only [hop, hk]
        refine ⟨fun e h => (by cases h), fun r h => ?_⟩
        cases h
        rw [checkResult_gradient]
        exact ⟨hn, hn'⟩

/-- Constant-gradient mode (`variable=false`) on a non-`Array` matrix (a view
or transpose) never reaches an out-of-range `@inbounds` access. With zero
constants the leaf allocates a 0-by-nsamples gradient, so the fused kernel
writes no rows, src/EvaluateDerivative.jl:353-365,380-384. -/
def viewConstantGradSafe : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (t : Tree JF) (msg : String),
    t.WF 2 o.nops X.nrows →
    eval_grad_tree_array .generic .constants o X t ≠ .error (.undefinedBehavior msg)
theorem viewConstantGradSafe_proof : viewConstantGradSafe := by
  intro o X t msg hwf h
  unfold eval_grad_tree_array at h
  have := (gradTree_bounds .generic .constants o X _ 2 t 1 hwf).1 _ h
  cases this

private theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys → ∀ y ∈ ys, ∃ a ∈ xs, f a = some y := by
  intro xs
  induction xs with
  | nil => intro ys h y hy; simp at h; subst h; simp at hy
  | cons a as ih =>
    intro ys h y hy
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hs : as.mapM f with
      | none => simp [ha, hs] at h
      | some bs =>
        simp [ha, hs] at h
        subst h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, by simp, ha⟩
        · obtain ⟨a', ha', hfa⟩ := ih bs hs y hy
          exact ⟨a', by simp [ha'], hfa⟩

/-- The bound for column-major indexing. -/
theorem offset_bound (X : JMat JF) (i j : Nat)
    (h : (1 ≤ i ∧ i ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols)) :
    X.nrows * (j - 1) + (i - 1) < X.data.size := by
  rw [X.size_eq]
  have hir : i - 1 < X.nrows := by omega
  calc
    X.nrows * (j - 1) + (i - 1) < X.nrows * (j - 1) + X.nrows := Nat.add_lt_add_left hir _
    _ = X.nrows * j := by rw [← Nat.mul_succ]; congr 1; omega
    _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_left _ h.2.2

private theorem get?_finite (X : JMat JF) (hX : FiniteMatrix X) (i j : Nat) (v : JF)
    (h : X.get? i j = .ok v) : v.valid = true := by
  have hdef : X.get? i j = (if hb : (1 ≤ i ∧ i ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols) then
      Except.ok (X.data[X.nrows * (j - 1) + (i - 1)]'(offset_bound X i j hb))
    else Except.error .boundsError) := rfl
  rw [hdef] at h
  split at h
  · cases h
    exact hX _ (Array.getElem_mem _)
  · cases h

/-- Well-formed trees have a directional value and derivative whenever every
feature is bound. -/
theorem diffScalar_some (o : DEnum) (x : Nat → Option JF) (direction nf D : Nat)
    (hx : ∀ k, 1 ≤ k → k ≤ nf → ∃ v, x k = some v) :
    ∀ t : Tree JF, t.WF D o.nops nf → ∃ p, diffScalar o x direction t = some p := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; exact ⟨(v, zero), by simp [diffScalar]⟩
  | hf k =>
    intro hw
    simp only [Tree.WF] at hw
    obtain ⟨v, hv⟩ := hx k hw.1 hw.2.1
    exact ⟨(v, if k = direction then one else zero), by simp [diffScalar, hv]⟩
  | hb idx cs ih =>
    intro hw
    simp only [Tree.WF] at hw
    obtain ⟨ps, hps⟩ := Tree.mapM_some cs (fun c hc => ih c hc (hw.2.2 c hc))
    obtain ⟨op, hop⟩ := lookup_exists o cs.length idx hw.1.1 hw.2.1.1 hw.2.1.2.1
    exact ⟨diffKernel op ps, by simp [diffScalar, hps, hop]⟩

/-- For `JF`, `is_valid_array` of the values and of the derivatives holds
exactly when every returned pair is finite. -/
theorem diffFlag_eq (ys : List (JF × JF)) :
    (Eval.isValidArray (ys.map Prod.fst).toArray && Eval.isValidArray (ys.map Prod.snd).toArray) =
      ys.all fun (v, d) => JF.valid v && JF.valid d := by
  rw [Eval.jf_isValidArray, Eval.jf_isValidArray]
  simp only [List.all_toArray]
  induction ys with
  | nil => rfl
  | cons p ys ih =>
    obtain ⟨v, d⟩ := p
    show ((JF.valid v && (ys.map Prod.fst).all JF.valid) &&
        (JF.valid d && (ys.map Prod.snd).all JF.valid)) =
      ((JF.valid v && JF.valid d) && ys.all fun (v, d) => JF.valid v && JF.valid d)
    rw [← ih]
    cases JF.valid v <;> cases JF.valid d <;> cases (ys.map Prod.fst).all JF.valid <;>
      cases (ys.map Prod.snd).all JF.valid <;> rfl

/-- For every well-formed tree, operator enum, direction and matrix,
`eval_diff_tree_array` succeeds and reports completion exactly when every
returned value and derivative is finite, as its documentation states: the flag
is `result.ok && is_valid_array(result.x) && is_valid_array(result.dx)`,
src/EvaluateDerivative.jl:35-57. -/
def directionalValidity : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (direction : Nat) (t : Tree JF) (D : Nat),
    t.WF D o.nops X.nrows →
    ∃ ys complete, eval_diff_tree_array o X direction t = some (ys, complete) ∧
      complete = (ys.all fun (v, d) => JF.valid v && JF.valid d)
theorem directionalValidity_proof : directionalValidity := by
  intro o X direction t D hwf
  obtain ⟨ys, hys⟩ := Tree.mapM_some
      (f := fun j => diffScalar o (fun k => (X.get? k (j + 1)).toOption) direction t)
      (List.range X.ncols) (by
    intro j hj
    rw [List.mem_range] at hj
    exact diffScalar_some o _ direction X.nrows D (by
      intro k h1 h2
      obtain ⟨w, hw⟩ := X.get?_exists k (j + 1) h1 h2 (by omega) (by omega)
      exact ⟨w, by rw [hw]; rfl⟩) t hwf)
  refine ⟨ys, _, ?_, diffFlag_eq ys⟩
  unfold eval_diff_tree_array
  rw [hys]
  rfl
example : (Tree.const JF.posInf : Tree JF).WF 2 (DEnum.nops ⟨[]⟩) 1 := by simp [Tree.WF]

/-- Companion of deriv-directional-validity: for finite inputs, finite constants
and operators whose values and partials are finite on finite arguments,
directional evaluation succeeds, every value and derivative is finite, and the
completion flag is true, so it agrees with the finiteness check,
src/EvaluateDerivative.jl:40-120. -/
def directionalValidityFinite : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (direction : Nat) (t : Tree JF) (D : Nat),
    t.WF D o.nops X.nrows → FiniteMatrix X → FiniteConstants t → FiniteOps o →
    ∃ ys, eval_diff_tree_array o X direction t = some (ys, true) ∧
      (ys.all fun (v, d) => JF.valid v && JF.valid d) = true
theorem directionalValidityFinite_proof : directionalValidityFinite := by
  intro o X direction t D hwf hX hct hops
  have hsample : ∀ j ∈ List.range X.ncols, ∃ v d, diffScalar o
      (fun k => (X.get? k (j + 1)).toOption) direction t = some (v, d) ∧
      v.valid = true ∧ d.valid = true := by
    intro j hj
    rw [List.mem_range] at hj
    have hx : ∀ k, 1 ≤ k → k ≤ X.nrows →
        ∃ w, (X.get? k (j + 1)).toOption = some w ∧ w.valid = true := by
      intro k h1 h2
      obtain ⟨w, hw⟩ := X.get?_exists k (j + 1) h1 h2 (by omega) (by omega)
      exact ⟨w, by rw [hw]; rfl, get?_finite X hX k (j + 1) w hw⟩
    obtain ⟨v, d, h1, _, hv, hd⟩ := seed_valid o _ (fun i => if i = direction then one else zero)
      (fun _ => zero) _ D hx (by intro i; split <;> rfl) (fun _ => rfl) hops t 1 hwf hct
    rw [denoteSeed_deriv] at h1
    exact ⟨v, d, by rw [directionalChainRule_proof]; exact h1, hv, hd⟩
  obtain ⟨ys, hys⟩ := Tree.mapM_some (List.range X.ncols) (by
    intro j hj
    obtain ⟨v, d, h, _⟩ := hsample j hj
    exact ⟨_, h⟩)
  have hall : (ys.all fun (v, d) => JF.valid v && JF.valid d) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨j, hj, hjp⟩ := mapM_mem _ _ ys hys p hp
    obtain ⟨v, d, h, hv, hd⟩ := hsample j hj
    rw [h] at hjp
    cases hjp
    simp [hv, hd]
  refine ⟨ys, ?_, hall⟩
  unfold eval_diff_tree_array
  rw [hys]
  simp only [Option.map_some]
  rw [diffFlag_eq, hall]

end DynExpr.Deriv
