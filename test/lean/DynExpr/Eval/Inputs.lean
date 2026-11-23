import DynExpr.Eval.Top
import DynExpr.Eval.GenericProofs

/-!
Input-level preconditions imply that every intermediate value is valid; proofs
of the registered properties stated with input-level preconditions.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

theorem constsOKL_mem (p : T → Bool) :
    ∀ cs : List (Tree T), constsOKL p cs = true → ∀ c ∈ cs, constsOK p c = true
  | [], _, c, hc => by simp at hc
  | c' :: cs, h, c, hc => by
    simp only [constsOKL, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.1
    · exact constsOKL_mem p cs h.2 c hc

theorem isConstantL_mem :
    ∀ cs : List (Tree T), isConstantL cs = true → ∀ c ∈ cs, isConstant c = true
  | [], _, c, hc => by simp at hc
  | c' :: cs, h, c, hc => by
    simp only [isConstantL, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h.1
    · exact isConstantL_mem cs h.2 c hc

/-- Finite feature values, finite constants and finite-preserving operators
make every intermediate value valid. -/
theorem allValid_of (o : OpEnum T) (ho : OpsFinite o) (x : Nat → Option T) (D nf : Nat)
    (hx : ∀ i, 1 ≤ i → i ≤ nf → ∃ v, x i = some v ∧ valid v = true) :
    ∀ t : Tree T, t.WF D o.nops nf → ConstsFinite t → AllValid o x t := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro _ hc
    simpa [AllValid, ConstsFinite, constsOK] using hc
  | hf i =>
    intro hw _
    simp only [Tree.WF] at hw
    simpa [AllValid] using hx i hw.1 hw.2.1
  | hb op cs ih =>
    intro hw hc
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, _, _⟩, ⟨ho1, ho2, _⟩, hcs⟩ := hw'
    have hcc : ∀ c ∈ cs, ConstsFinite c := fun c hm =>
      constsOKL_mem valid cs (by simpa [ConstsFinite, constsOK] using hc) c hm
    have hch : ∀ c ∈ cs, AllValid o x c := fun c hm => ih c hm (hcs c hm) (hcc c hm)
    obtain ⟨g, hg, _⟩ := nifOp_lookup o cs.length op hl1 ho1 ho2
    have hm := mapM_opt_eq (Tree.denote o x) (vx o x) cs
      (fun c hm => AllValid.some o x c (hch c hm))
    simp only [AllValid]
    refine ⟨hch, g (cs.map (vx o x)), by simp [Tree.denote, hg, hm], ?_⟩
    apply ho cs.length op g hg
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨c, hc', rfl⟩ := ha
    exact AllValid.valid o x c (hch c hc')

/-- Matrix entries at a valid coordinate are finite under `XFinite`. -/
theorem col_finite (X : JMat T) (hX : XFinite X) (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    ∀ i, 1 ≤ i → i ≤ X.nrows → ∃ v, col X j i = some v ∧ valid v = true := by
  intro i h1 h2
  rw [col, JMat.get?_eq X i j h1 h2 hj1 hj2]
  exact ⟨_, rfl, hX _ (by simp)⟩

theorem allValid_inputs (o : OpEnum T) (X : JMat T) (t : Tree T) (D : Nat)
    (hw : t.WF D o.nops X.nrows) (hX : XFinite X) (hc : ConstsFinite t) (ho : OpsFinite o) :
    ∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t :=
  fun j h1 h2 => allValid_of o ho _ D X.nrows (col_finite X hX j h1 h2) t hw hc

/-- Constant trees are well formed for zero features. -/
theorem wf_const_zero {D : Nat} {nops : Nat → Nat} {nf : Nat} :
    ∀ t : Tree T, isConstant t = true → t.WF D nops nf → t.WF D nops 0 := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _ _; simp [Tree.WF]
  | hf i => intro h; simp [isConstant] at h
  | hb op cs ih =>
    intro hcst hw
    simp only [Tree.WF] at hw ⊢
    refine ⟨hw.1, hw.2.1, fun c hm => ih c hm ?_ (hw.2.2 c hm)⟩
    exact isConstantL_mem cs (by simpa [isConstant] using hcst) c hm

theorem evalDenote_proof : evalDenote := by
  intro T _ ext impl D early fused o X t hA hn hw hX hc ho
  exact evalDenoteAV_proof T ext impl D early fused o X t hA hn hw
    (allValid_inputs o X t D hw hX hc ho)

theorem evalBuffer_proof : evalBuffer := by
  intro T _ ext impl D early fused o X t b hA hn hw hX hc ho hb
  exact evalBufferAV_proof T ext impl D early fused o X t b hA hn hw
    (allValid_inputs o X t D hw hX hc ho) hb

theorem evalConstant_proof : evalConstant := by
  intro T _ ext impl D early fused o X t hA hw hcst hc ho
  exact evalConstantAV_proof T ext impl D early fused o X t hA hw hcst
    (allValid_of o ho _ D 0 (fun i h1 h2 => by omega) t (wf_const_zero t hcst hw) hc)

theorem evalVector_proof : evalVector := by
  intro T _ ext impl D early fused o v t hA hw hv hc ho
  apply evalVectorAV_proof T ext impl D early fused o v t hA hw
  apply allValid_of o ho _ D v.size _ t hw hc
  intro i h1 h2
  refine ⟨v[i - 1]'(by omega), by simp [vecAssign, h1, show i - 1 < v.size by omega], ?_⟩
  exact hv _ (by simp)

theorem evalMixed_proof : evalMixed := by
  intro T1 T2 T _ c1 c2 ext impl D early fused o X t hA hn hw hX hc ho
  exact evalMixedAV_proof T1 T2 T c1 c2 ext impl D early fused o X t hA hn hw
    (allValid_inputs o (mapMat c2 X) (mapTree c1 t) D hw hX hc ho)

theorem evalDiffDenote_proof : evalDiffDenote := by
  intro T _ D o X t hmul hn hw hX hc ho
  exact evalDiffDenoteAV_proof T D o X t hmul hn hw (allValid_inputs o X t D hw hX hc ho)

theorem evalWideBufferExact_proof : evalWideBufferExact := by
  intro T _ ext impl D early fused o X t A i hA hn hw hX hc ho _ hr he
  rw [evalBuffer_proof T ext impl D early fused o X t (.mat A i) hA hn hw hX hc ho
    (Or.inr (Or.inr ⟨A, i, rfl, he, hr⟩))]

/-- eval-wide-buffer: since PR #265 a matrix slot is viewed only over the
sample columns, so extra buffer columns do not change the output. -/
theorem evalWideBuffer_proof : evalWideBuffer := by
  intro T _ ext impl D early fused o X t A i hA hn hw hX hc ho hcols hr
  have hv := shift_valid o X t (allValid_inputs o X t D hw hX hc ho)
  show (evalArr ⟨early, fused, D⟩ o X t (.mat A i)).map (·.1.toList) =
    (evalArr ⟨early, fused, D⟩ o X t .none).map (·.1.toList)
  rw [evalArr_valid _ o X t (.mat A i) hA hn hw hv ⟨hcols, hr⟩,
    evalArr_valid _ o X t .none hA hn hw hv trivial]

theorem evalTurboDispatch_proof : evalTurboDispatch := by
  intro T _ ext impl D o X t early fused b hf hn hl
  simp [evalTreeArray, hf, hl, hn]
  cases impl.turboEval t X <;> rfl

/-- `differentiable_eval_tree_array` children abort only with a false flag. -/
theorem diffL_inl (o : OpEnum T) (X : JMat T) :
    ∀ cs : List (Tree T), ∀ r, diffL o X cs = .ok (.inl r) → r.ok = false
  | [], r, h => by simp [diffL] at h
  | c :: cs, r, h => by
    rw [diffL] at h
    cases hc : diffT o X c with
    | error e => rw [hc] at h; cases h
    | ok r' =>
      rw [hc] at h
      simp only [jl_ok_bind] at h
      by_cases hok : r'.ok = true
      · simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
        cases hl : diffL o X cs with
        | error e => rw [hl] at h; cases h
        | ok s =>
          rw [hl] at h
          cases s with
          | inl e =>
            simp only [jl_ok_bind] at h
            cases h
            exact diffL_inl o X cs _ hl
          | inr xs => simp at h
      · simp only [Bool.not_eq_true] at hok
        simp only [hok, Bool.not_false, ↓reduceIte] at h
        cases h
        exact hok

private theorem diffFlag_sound (o : OpEnum T) (X : JMat T) (t : Tree T) (out : List T)
    (hmul : ∀ v : T, JlScalar.mul JlScalar.one v = v)
    (hrow : ∀ f r, X.row f = .ok r → isValidArray r = true →
      ∀ x ∈ r.toList, valid x = true)
    (h : obs (differentiableEvalTreeArray o X t) = .ok (out, true)) :
    ∀ x ∈ out, valid x = true := by
  intro x hx
  cases t with
  | const v =>
    simp only [obs, differentiableEvalTreeArray, diffT, Except.map, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, hv⟩ := h
    simp only [constRow, Array.toList_map, List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    simp at hu
    rw [hu.2, hmul]
    exact hv
  | feature f =>
    simp only [obs, differentiableEvalTreeArray, diffT] at h
    cases hr : X.row f with
    | error e => simp [hr, Except.map] at h
    | ok r =>
      simp only [hr, jl_ok_bind, jl_pure, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, ha⟩ := h
      exact hrow f r hr ha _ hx
  | branch op cs =>
    simp only [obs, differentiableEvalTreeArray] at h
    rw [diffT] at h
    cases hl : diffL o X cs with
    | error e => simp [hl, Except.map] at h
    | ok s =>
      cases s with
      | inl r =>
        have hr := diffL_inl o X cs r hl
        simp [hl, Except.map, hr] at h
      | inr xs =>
        simp only [hl, jl_ok_bind] at h
        cases hf : nifOp (opsOf o cs.length) op with
        | error e => simp [hf, Except.map] at h
        | ok f =>
          simp only [hf, jl_ok_bind] at h
          cases hb : bcast (fun args => Except.ok (f args)) xs with
          | error e => simp [hb, Except.map] at h
          | ok out' =>
            simp only [hb, jl_ok_bind, jl_pure, Except.map, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, hall⟩ := h
            exact (List.all_eq_true.mp hall) x hx

theorem evalDiffFlag_proof : evalDiffFlag := by
  intro T _ o X t out _ hmul ha h
  exact diffFlag_sound o X t out hmul (fun _ r _ hv => (ha r).mp hv) h

theorem evalDiffFlagFinite_proof : evalDiffFlagFinite := by
  intro T _ o X t out _ hmul ⟨hX, _⟩ h
  apply diffFlag_sound o X t out hmul _ h
  intro f r hr _ x hx
  unfold JMat.row at hr
  split at hr
  · cases hr
    simp only [Array.toList_ofFn, List.mem_ofFn] at hx
    obtain ⟨k, rfl⟩ := hx
    exact hX _ (by simp)
  · cases hr

/-- The input-level preconditions are satisfiable: `x1 + 1.0` with `+` on one
finite sample, under `JF`. -/
example : XFinite (⟨1, 1, #[.fin 0], rfl⟩ : JMat JF) ∧
    ConstsFinite (.branch 1 [.feature 1, .const (.fin 1)] : Tree JF) ∧
    OpsFinite (⟨[[], [fun xs => match xs with | [a, b] => JF.add a b | _ => .fin 0]]⟩ : OpEnum JF) ∧
    noConstBranch (.branch 1 [.feature 1, .const (.fin 1)] : Tree JF) = true := by
  refine ⟨?_, by unfold ConstsFinite; decide, ?_, by decide⟩
  · intro x hx; simp at hx; subst hx; rfl
  · intro d op f hf args hargs
    rcases d with _ | _ | _ | d <;> rcases op with _ | _ | op <;>
      simp [OpEnum.lookup] at hf
    subst hf
    match args, hargs with
    | [a, b], h =>
      have ha := h a (by simp)
      have hb := h b (by simp)
      cases a <;> cases b <;> simp_all [valid, JlValue.valid, JF.valid, JF.add]
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _ :: _, _ => rfl

end DynExpr.Eval
