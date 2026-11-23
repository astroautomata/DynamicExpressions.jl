import DynExpr.Eval.Main
import DynExpr.Eval.Scalars

/-!
The main induction over trees and the top-level evaluator properties
`evalDenoteAV`, `evalBufferAV`, `evalConstantAV`, `evalVectorAV`, `evalMixedAV`.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

theorem evalChildren_ok (cx : Ctx) (o : OpEnum T) (X : JMat T) (hA : ArrayValidSound T) :
    ∀ cs : List (Tree T), (∀ c ∈ cs, ChildOK cx o X c) →
      ∀ k (b : Buf T), Good X.ncols (k + (cs.map Tree.size).sum) b →
        ∃ xs b', evalChildren cx o X cs b = .ok (.inr (xs, b')) ∧
          xs.map Prod.fst = cs.map (canon o X) ∧ Good X.ncols k b'
  | [], _, k, b, hb => ⟨[], b, rfl, rfl, by simpa using hb⟩
  | c :: cs, hcs, k, b, hb => by
    obtain ⟨_, hcv, hce⟩ := hcs c (by simp)
    simp only [List.map_cons, List.sum_cons] at hb
    obtain ⟨id, b1, hev, hg1⟩ := hce (k + (cs.map Tree.size).sum) b (by
      have : k + (c.size + (List.map Tree.size cs).sum) =
          k + (List.map Tree.size cs).sum + c.size := by omega
      rw [← this]; exact hb)
    obtain ⟨xs, b', hrest, hxs, hg'⟩ :=
      evalChildren_ok cx o X hA cs (fun c' h => hcs c' (by simp [h])) k b1 hg1
    refine ⟨(canon o X c, id) :: xs, b', ?_, by simp [hxs], hg'⟩
    simp [evalChildren, hev, canon_isValid o X c hA hcv, hrest]

/-- Main theorem: with every intermediate valid, `_eval_tree_array` returns
the canonical output with flag true, consuming at most one buffer slot per
node. -/
theorem evalT_valid (cx : Ctx) (o : OpEnum T) (X : JMat T) (hA : ArrayValidSound T)
    (hn : 1 ≤ X.ncols) : ∀ t : Tree T, t.WF cx.D o.nops X.nrows →
      (∀ j, j < X.ncols → AllValid o (col X (j + 1)) t) → ChildOK cx o X t := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro hw hv
    refine ⟨hw, hv, fun k b hb => ?_⟩
    obtain ⟨b', hf, hg⟩ := getFilled_good (k := k) v (hb.mono (by simp [Tree.size]))
    refine ⟨nextId b, b', ?_, hg⟩
    have hvv : valid v = true := by simpa [AllValid] using hv 0 hn
    rw [canon_fill o X (.const v) v (fun j _ => cv_const o X v j)]
    simp [evalT, hf, hvv]
  | hf i =>
    intro hw hv
    refine ⟨hw, hv, fun k b hb => ?_⟩
    simp only [Tree.WF] at hw
    obtain ⟨b', hf, hg⟩ := getFeature_good (k := k) X i _ (rowInb_canon o X i hw.1 hw.2.1)
      (hb.mono (by simp [Tree.size]))
    exact ⟨nextId b, b', by simp [evalT, hf, chk_ok X i hw.1 hw.2.1], hg⟩
  | hb op cs ih =>
    intro hw hv
    refine ⟨hw, hv, fun k b hb => ?_⟩
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hlD, _⟩, _, hcs⟩ := hw'
    have hch : ∀ c ∈ cs, ChildOK cx o X c := fun c hc =>
      ih c hc (hcs c hc) (fun j hj => AllValid.children o _ op cs (hv j hj) c hc)
    by_cases hcon : isConstantL cs = true
    · -- constant-tree shortcut
      have hce := constEval_valid o (col X 1) cx.earlyExit (.branch op cs) hw (hv 0 hn)
        (by simpa [isConstant] using hcon)
      obtain ⟨b', hf, hg⟩ := getFilled_good (k := k) (vx o (col X 1) (.branch op cs))
        (hb.mono (by simp))
      refine ⟨nextId b, b', ?_, hg⟩
      have hcanon : canon o X (.branch op cs) = JVec.fill X.ncols (vx o (col X 1) (.branch op cs)) :=
        canon_fill o X _ _ (fun j _ => by
          simp only [cv, vx]
          rw [const_indep o (col X (j + 1)) (col X 1) _ (by simpa [isConstant] using hcon)])
      unfold evalT
      simp [hcon, constPath, hce, filled, hf, hcanon]
    · have hcon' : isConstantL cs = false := by simpa using hcon
      rcases cs with _ | ⟨c, _ | ⟨r, _ | ⟨s, rest⟩⟩⟩
      · simp at hl1
      · obtain ⟨id, b', hk, hg⟩ := deg1_case cx o X hA hn op c hw hv
          (by simpa [isConstantL] using hcon') (hch c (by simp)) hb
        exact ⟨id, b', by simp only [evalT, hcon', Bool.false_eq_true, ↓reduceIte]; exact hk, hg⟩
      · obtain ⟨id, b', hk, hg⟩ := deg2_case cx o X hA hn op c r hw
          (by simpa [isConstantL] using hcon') (hch c (by simp)) (hch r (by simp)) hb
        exact ⟨id, b', by simp only [evalT, hcon', Bool.false_eq_true, ↓reduceIte]; exact hk, hg⟩
      · -- three or more children: `D ≥ 3`
        have hD : cx.D ≠ 2 := by simp at hlD; omega
        simp only [List.length_cons] at hl1
        have hw2 := hw
        simp only [Tree.WF] at hw2
        obtain ⟨_, ⟨ho1, ho2, _⟩, _⟩ := hw2
        obtain ⟨g, hg, hnif⟩ := nifOp_lookup o (c :: r :: s :: rest).length op (by simp) ho1 ho2
        have hsum : (Tree.branch op (c :: r :: s :: rest)).size =
            1 + ((c :: r :: s :: rest).map Tree.size).sum := by simp
        rw [hsum] at hb
        obtain ⟨xs, b', hch', hxs, hg'⟩ :=
          evalChildren_ok cx o X hA (c :: r :: s :: rest) hch k b (hb.mono (by omega))
        refine ⟨(xs.head?.map Prod.snd).getD .fresh, b', ?_, hg'⟩
        have hvc : ∀ j, j < X.ncols → ∀ c' ∈ c :: r :: s :: rest, AllValid o (col X (j + 1)) c' :=
          fun j hj c' hc' => AllValid.children o _ op _ (hv j hj) c' hc'
        have hd := degnEval_canon o X g (c :: r :: s :: rest) (by simp)
        have hcanon := canon_branch o X op (c :: r :: s :: rest) g hg hvc
        simp only [evalT, hcon', Bool.false_eq_true, ↓reduceIte, hD, hch', jl_ok_bind,
          degnFinish]
        rw [show (s :: rest).length + 2 = (c :: r :: s :: rest).length by simp, hnif]
        simp only [jl_ok_bind, hxs, hd, hcanon]
        rfl

theorem evalArr_valid (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (hA : ArrayValidSound T) (hn : 1 ≤ X.ncols) (hw : t.WF cx.D o.nops X.nrows)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t)
    (hb : Good X.ncols t.size b) :
    evalArr cx o X t b = .ok (canon o X t, true) := by
  obtain ⟨_, _, he⟩ := evalT_valid cx o X hA hn t hw hv
  obtain ⟨id, b', hk, _⟩ := he 0 b (by simpa using hb)
  simp [evalArr, hk, canon_isValid o X t hA hv]

theorem denotes_canon (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hv : ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t) : Denotes o X t (canon o X t) := by
  refine ⟨canon_size o X t, fun j h1 h2 => ?_⟩
  have hj : j - 1 < X.ncols := by omega
  rw [canon_eq, range_map_get _ _ _ hj]
  have := AllValid.some o _ t (hv (j - 1) hj)
  rw [show j - 1 + 1 = j by omega] at this
  simp only [cv, show j - 1 + 1 = j by omega]
  rw [Tree.denoteRow]
  exact this.symm

theorem shift_valid (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hv : ∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) :
    ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t :=
  fun j hj => hv (j + 1) (by omega) (by omega)

theorem evalDenoteAV_proof : evalDenoteAV := by
  intro T _ ext impl D early fused o X t hA hn hw hv
  refine ⟨canon o X t, ?_, denotes_canon o X t (shift_valid o X t hv)⟩
  exact evalArr_valid ⟨early, fused, D⟩ o X t .none hA hn hw (shift_valid o X t hv) trivial

theorem evalBufferAV_proof : evalBufferAV := by
  intro T _ ext impl D early fused o X t b hA hn hw hv hfit
  have hgood : Good X.ncols t.size b := by
    rcases hfit with rfl | ⟨arrs, i, rfl⟩ | ⟨A, i, rfl, hc, hr⟩
    · trivial
    · trivial
    · exact ⟨by omega, hr⟩
  show evalArr ⟨early, fused, D⟩ o X t b = evalArr ⟨early, fused, D⟩ o X t .none
  rw [evalArr_valid _ o X t b hA hn hw (shift_valid o X t hv) hgood,
    evalArr_valid _ o X t .none hA hn hw (shift_valid o X t hv) trivial]

theorem evalConstantAV_proof : evalConstantAV := by
  intro T _ ext impl D early fused o X t hA hw hc hv
  refine ⟨vx o (fun _ => none) t, AllValid.some o _ t hv, ?_⟩
  have hval := AllValid.valid o _ t hv
  have hfill : isValidArray (JVec.fill X.ncols (vx o (fun _ => none) t)) = true := by
    apply hA
    intro x hx
    simp [JVec.fill] at hx
    rw [hx.2]; exact hval
  show evalArr ⟨early, fused, D⟩ o X t .none = _
  cases t with
  | const v =>
    have hv' : valid v = true := by simpa [vx, Tree.denote] using hval
    have hf' : isValidArray (JVec.fill X.ncols v) = true := by simpa [vx, Tree.denote] using hfill
    simp [evalArr, evalT, getFilled, hv', hf', vx, Tree.denote]
  | feature i => simp [isConstant] at hc
  | branch op cs =>
    have hce := constEval_valid o (fun _ => none) early (.branch op cs) hw hv hc
    have hcs : isConstantL cs = true := by simpa [isConstant] using hc
    simp only [evalArr]
    unfold evalT
    simp [hcs, constPath, hce, filled, getFilled, hfill]

/-- A vector reshaped to one sample has the vector's entries as features. -/
theorem col_colMatrix (v : JVec T) : col (colMatrix v) 1 = vecAssign v := by
  funext f
  by_cases hf : 1 ≤ f ∧ f ≤ v.size
  · rw [col, JMat.get?_eq (colMatrix v) f 1 hf.1 hf.2 (Nat.le_refl 1) (Nat.le_refl 1)]
    simp [vecAssign, hf.1, colMatrix, Except.toOption]
  · have hnone : col (colMatrix v) 1 f = none := by
      have hdef : (colMatrix v).get? f 1 = .error .boundsError := by
        show (if h : (1 ≤ f ∧ f ≤ (colMatrix v).nrows) ∧ (1 ≤ 1 ∧ 1 ≤ (colMatrix v).ncols)
          then _ else _) = _
        split
        · rename_i h; exact absurd h.1 hf
        · rfl
      simp [col, hdef, Except.toOption]
    rw [hnone]
    unfold vecAssign
    split
    · symm; apply Array.getElem?_eq_none; omega
    · rfl

theorem evalVectorAV_proof : evalVectorAV := by
  intro T _ ext impl D early fused o v t hA hw hv
  have hv' : ∀ j, j < (colMatrix v).ncols → AllValid o (col (colMatrix v) (j + 1)) t := by
    intro j hj
    have : j = 0 := by simp [colMatrix] at hj; omega
    subst this
    rw [col_colMatrix]; exact hv
  have hres := evalArr_valid ⟨early, fused, D⟩ o (colMatrix v) t .none hA (by simp [colMatrix])
    hw hv' trivial
  refine ⟨vx o (vecAssign v) t, AllValid.some o _ t hv, ?_, ?_⟩
  · show (evalArr ⟨early, fused, D⟩ o (colMatrix v) t .none).map (·.1.toList) = _
    have hc : canon o (colMatrix v) t = #[vx o (col (colMatrix v) 1) t] := rfl
    rw [col_colMatrix] at hc
    rw [hres, hc]
    rfl
  · show (evalArr ⟨early, fused, D⟩ o (colMatrix v) t .none).map Prod.snd = _
    rw [hres]
    rfl

theorem evalMixedAV_proof : evalMixedAV := by
  intro T1 T2 T _ c1 c2 ext impl D early fused o X t hA hn hw hv
  exact evalDenoteAV_proof T ext impl D early fused o (mapMat c2 X) (mapTree c1 t) hA hn hw hv

/-- The main hypotheses are satisfiable: `x1 + 1.0` on one `Float64` sample. -/
example : obs (evalTreeArray {} ⟨fun _ _ => .error .boundsError⟩
    2 (.branch 1 [.feature 1, .const (.fin 1)]) (⟨1, 1, #[.fin 0], rfl⟩ : JMat JF)
    ⟨[[], [fun xs => match xs with | [a, b] => JF.add a b | _ => .nan]]⟩
    (plainCtx true true .none)) = .ok ([.fin 1], true) := by decide +kernel

end DynExpr.Eval
