import DynExpr.Eval.Inputs
import DynExpr.Eval.FusedProofs
import DynExpr.Eval.TotalProofs
import DynExpr.Eval.NoEarlyProofs
import DynExpr.Eval.UnfusedProofs

/-!
Companion of eval-fused-flag-agree: with finite inputs the fused and unfused
completion flags agree.
-/

namespace DynExpr.Eval

theorem evalFusedFlagFinite_proof : evalFusedFlagFinite := by
  intro T _ ext impl D o X t hA hn hw hX
  have hw16 : t.WF D o.nops 65535 := by
    have := Tree.WF.representable t hw
    clear this
    induction t using Tree.induction with
    | hc v => simp [Tree.WF]
    | hf i => simp only [Tree.WF] at hw ⊢; omega
    | hb op cs ih =>
      simp only [Tree.WF] at hw ⊢
      exact ⟨hw.1, hw.2.1, fun c hc => ih c hc (hw.2.2 c hc)⟩
  have hS : ArrayValidSound T := fun a h => (hA a).mpr h
  -- unfused: flag ↔ every intermediate valid
  obtain ⟨outU, okU, hU, hiffU, _⟩ := evalUnfusedFlag_proof T ext impl D o X t hA hn hw
  -- fused: the call returns
  obtain ⟨⟨outF, okF⟩, hF⟩ := evalTotal_proof T ext impl D true true o X t hn hw16 hw
  have hFarr : evalArr ⟨true, true, D⟩ o X t .none = .ok (outF, okF) := hF
  have hiffF : okF = true ↔ ∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t := by
    constructor
    · intro hok j h1 h2
      subst hok
      have := fusedSound D o X t hA hn hw hX outF hFarr (j - 1) (by omega)
      rwa [show j - 1 + 1 = j by omega] at this
    · intro hv
      obtain ⟨out, hout, _⟩ := evalDenoteAV_proof T ext impl D true true o X t hS hn hw hv
      have : evalArr ⟨true, true, D⟩ o X t .none = .ok (out, true) := hout
      rw [hFarr] at this
      cases this
      rfl
  have hfl : okF = okU := by
    cases hF' : okF <;> cases hU' : okU
    · rfl
    · exact absurd (hiffF.mpr (hiffU.mp hU')) (by simp [hF'])
    · exact absurd (hiffU.mpr (hiffF.mp hF')) (by simp [hU'])
    · rfl
  rw [hF, hU, hfl]
  rfl

/-- eval-fused-flag-agree (documented on `use_fused`, PR #276): a completed
unfused call means every intermediate is valid, so the fused call completes
with the same output; with finite inputs the flags agree. -/
theorem evalFusedFlagAgree_proof : evalFusedFlagAgree := by
  intro T _ ext impl D o X t hA hn hw
  refine ⟨?_, evalFusedFlagFinite_proof T ext impl D o X t hA hn hw⟩
  intro out hU
  have hS : ArrayValidSound T := fun a h => (hA a).mpr h
  obtain ⟨outU, okU, hU', hiffU, _⟩ := evalUnfusedFlag_proof T ext impl D o X t hA hn hw
  rw [hU] at hU'
  cases hU'
  have hv := shift_valid o X t (hiffU.mp rfl)
  have hu : evalArr ⟨true, false, D⟩ o X t .none = .ok (out, true) := hU
  rw [evalArr_valid _ o X t .none hS hn hw hv trivial] at hu
  cases hu
  exact evalArr_valid ⟨true, true, D⟩ o X t .none hS hn hw hv trivial

theorem bufOK_of_fits {T : Type} [JlScalar T] {X : JMat T} {t : Tree T} {b : Buf T}
    (h : BufferFits X t b) : BufOK X t b := h

theorem evalAliasFresh_proof : evalAliasFresh := by
  intro T _ cx o X t hw
  obtain ⟨r, b', hr⟩ := evalT_total cx o X t .none hw (Or.inl rfl)
  obtain ⟨hid, hb⟩ := aliasFresh_of_ok cx o X t r b' hr
  subst hb
  exact ⟨r, hr, hid⟩

theorem evalAliasSlots_proof : evalAliasSlots := by
  intro T _ cx o X t b hw hfit hb
  obtain ⟨r, b', hr⟩ := evalT_total cx o X t b hw (bufOK_of_fits hfit)
  exact ⟨r, b', hr, aliasSlots_of_ok cx o X t b r b' hb hr⟩

theorem evalAliasSuccessive_proof : evalAliasSuccessive := by
  intro T _ cx o X t1 t2 b hw1 hw2 hb
  have hg : Good X.ncols (t1.size + t2.size) b ∧ b.isNone = false := by
    rcases hb with ⟨arrs, i, rfl⟩ | ⟨A, i, rfl, hc, hr⟩
    · exact ⟨trivial, rfl⟩
    · exact ⟨⟨by omega, by omega⟩, rfl⟩
  obtain ⟨r1, b1, h1, hg1⟩ := evalT_total_room cx o X t1 b t2.size hw1
    (by rw [Nat.add_comm]; exact hg.1)
  obtain ⟨r2, b2, h2, _⟩ := evalT_total_room cx o X t2 b1 0 hw2 (by simpa using hg1)
  exact ⟨r1, b1, r2, b2, h1, h2, aliasSuccessive_of_ok cx o X t1 t2 b b1 b2 r1 r2 hg.2 h1 h2⟩

/-- `tree(X, operators)` (src/Evaluate.jl, callable overload in
EvaluationHelpers.jl) on in-range features. -/
theorem evalCallable_proof : evalCallable := by
  intro T _ ext impl D early fused o X t inv hinv hw
  obtain ⟨r, b, hr, hs⟩ := evalT_total_size ⟨early, fused, D⟩ o X t .none hw (Or.inl rfl)
  have he : evalTreeArray ext impl D t X o (plainCtx early fused .none) =
      .ok (r.x, r.ok && (!early || isValidArray r.x)) := by
    simp [evalTreeArray, plainCtx, evalArr, hr]
  rw [he]
  cases hok : (r.ok && (!early || isValidArray r.x)) with
  | true => exact ⟨r.x, true, r.x, rfl, by simp [callTree], hs, fun _ => rfl, by simp⟩
  | false =>
    exact ⟨r.x, false, JVec.fill X.ncols inv, rfl, by simp [callTree, setInvalid, hinv, hs],
      by simp [JVec.fill], by simp, fun _ => rfl⟩

end DynExpr.Eval
