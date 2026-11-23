import DynExpr.StringsParse.Roundtrip.Domain

/-! Shape facts about `rotT`, the tree that reparsing yields when unary `+`
calls are `^` bases (Q40). -/

namespace DynExpr.StringsParse.Roundtrip

theorem rotT_unary (ops : Operators) (idx : Nat) (c : Tree Scalar) :
    rotT ops (.branch idx [c]) = .branch idx [rotT ops c] := by
  simp [rotT]

theorem rotT_pair (ops : Operators) {idx : Nat} {a b : Tree Scalar}
    (h : ¬ (opName ops 2 idx = "^" ∧ PlusLed ops a = true)) :
    rotT ops (.branch idx [a, b]) = .branch idx [rotT ops a, rotT ops b] := by
  show rotPow ops idx a (rotT ops a) (rotT ops b) = _
  unfold rotPow
  rw [if_neg h]

theorem plusLed_shape {ops : Operators} {a : Tree Scalar} (h : PlusLed ops a = true) :
    ∃ pidx c, a = .branch pidx [c] ∧ opName ops 1 pidx = "+" := by
  unfold PlusLed at h
  split at h
  · rename_i pidx c
    exact ⟨pidx, c, rfl, by simpa using h⟩
  · cases h

theorem rotT_plus (ops : Operators) {idx pidx : Nat} {c b : Tree Scalar}
    (h1 : opName ops 2 idx = "^") (h2 : opName ops 1 pidx = "+") :
    rotT ops (.branch idx [.branch pidx [c], b]) =
      .branch pidx [.branch idx [rotT ops c, rotT ops b]] := by
  show rotPow ops idx (.branch pidx [c]) (rotT ops (.branch pidx [c])) (rotT ops b) = _
  have hp : PlusLed ops (.branch pidx [c]) = true := by simp [PlusLed, h2]
  unfold rotPow
  rw [if_pos ⟨h1, hp⟩, rotT_unary]

/-- Without unary `+` power bases nothing moves. -/
theorem rotT_id (ops : Operators) (t : Tree Scalar) (h : NoPlusBase ops t) : rotT ops t = t := by
  induction t using Tree.induction with
  | hc v => rfl
  | hf k => rfl
  | hb idx cs ih =>
    simp only [NoPlusBase] at h
    match cs, ih, h with
    | [c], ih, h => rw [rotT_unary, ih c (by simp) (h.2 c (by simp))]
    | [a, b], ih, h =>
      have hn : ¬ (opName ops 2 idx = "^" ∧ PlusLed ops a = true) := by
        intro ⟨h1, h2⟩
        rw [h.1 a b rfl h1] at h2
        cases h2
      rw [rotT_pair ops hn, ih a (by simp) (h.2 a (by simp)), ih b (by simp) (h.2 b (by simp))]
    | [], _, _ => rfl
    | _ :: _ :: _ :: _, _, _ => rfl

theorem rotT_wf (ops : Operators) {D : Nat} {nops : Nat → Nat} {nf : Nat} (t : Tree Scalar)
    (hw : t.WF D nops nf) : (rotT ops t).WF D nops nf := by
  induction t using Tree.induction with
  | hc v => exact hw
  | hf k => exact hw
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨hl, hi, hcs⟩ := hw'
    match cs, ih, hl, hi, hcs with
    | [c], ih, hl, hi, hcs =>
      rw [rotT_unary]
      simp only [Tree.WF]
      refine ⟨hl, hi, ?_⟩
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ih c (by simp) (hcs c (by simp))
    | [a, b], ih, hl, hi, hcs =>
      by_cases hr : opName ops 2 idx = "^" ∧ PlusLed ops a = true
      · obtain ⟨pidx, c, rfl, hp⟩ := plusLed_shape hr.2
        rw [rotT_plus ops hr.1 hp]
        have haw := ih (.branch pidx [c]) (by simp) (hcs (.branch pidx [c]) (by simp))
        rw [rotT_unary] at haw
        simp only [Tree.WF] at haw
        obtain ⟨hla, hia, hca⟩ := haw
        have hbw := ih b (by simp) (hcs b (by simp))
        simp only [Tree.WF]
        refine ⟨hla, hia, ?_⟩
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        simp only [Tree.WF]
        refine ⟨hl, hi, ?_⟩
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hca _ (by simp)
        · exact hbw
      · rw [rotT_pair ops hr]
        simp only [Tree.WF]
        refine ⟨hl, hi, ?_⟩
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact ih a (by simp) (hcs a (by simp))
        · exact ih b (by simp) (hcs b (by simp))
    | [], _, _, _, _ => exact hw
    | _ :: _ :: _ :: _, _, _, _, _ => exact hw

theorem rotT_admissible (ops : Operators) (names : List String) (t : Tree Scalar)
    (ha : Admissible ops names t) : Admissible ops names (rotT ops t) := by
  induction t using Tree.induction with
  | hc v => exact ha
  | hf k => exact ha
  | hb idx cs ih =>
    simp only [Admissible] at ha
    match cs, ih, ha with
    | [c], ih, ha =>
      rw [rotT_unary]
      simp only [Admissible, List.mem_singleton, forall_eq]
      exact ih c (by simp) (ha c (by simp))
    | [a, b], ih, ha =>
      by_cases hr : opName ops 2 idx = "^" ∧ PlusLed ops a = true
      · obtain ⟨pidx, c, rfl, hp⟩ := plusLed_shape hr.2
        rw [rotT_plus ops hr.1 hp]
        have haa := ih (.branch pidx [c]) (by simp) (ha (.branch pidx [c]) (by simp))
        rw [rotT_unary] at haa
        simp only [Admissible, List.mem_singleton, forall_eq] at haa
        simp only [Admissible, List.mem_singleton, forall_eq, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq_or_imp]
        exact ⟨haa, ih b (by simp) (ha b (by simp))⟩
      · rw [rotT_pair ops hr]
        simp only [Admissible, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨ih a (by simp) (ha a (by simp)), ih b (by simp) (ha b (by simp))⟩
    | [], _, _ => simp [rotT, Admissible]
    | _ :: _ :: _ :: _, _, ha => simpa [rotT, Admissible] using ha

end DynExpr.StringsParse.Roundtrip
