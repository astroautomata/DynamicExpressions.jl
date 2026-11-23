import DynExpr.Simplify.CombineSpec

namespace DynExpr.Simplify

open DynExpr

private theorem num_neg (x : Rat) : x.num < 0 ↔ x < 0 := by
  rw [← Rat.not_le, ← Rat.num_nonneg]
  omega

private theorem pos_of_not_neg (x : Rat) (hz : x ≠ 0) (hs : ¬ x.num < 0) :
    0 < x := by
  exact Rat.lt_iff_le_and_ne.mpr ⟨Rat.num_nonneg.mp (by omega), Ne.symm hz⟩

private theorem mul_num_neg (x y : Rat) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).num < 0 ↔
      (x.num < 0 ∧ ¬ y.num < 0) ∨ (¬ x.num < 0 ∧ y.num < 0) := by
  by_cases sx : x.num < 0 <;> by_cases sy : y.num < 0
  · have nx := (num_neg x).mp sx
    have ny := (num_neg y).mp sy
    have px : 0 < -x := by simpa only [Rat.neg_zero] using Rat.neg_lt_neg nx
    have py : 0 < -y := by simpa only [Rat.neg_zero] using Rat.neg_lt_neg ny
    have hp : 0 < x * y := by
      simpa only [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg] using Rat.mul_pos px py
    have hn : ¬ (x * y).num < 0 :=
      fun h => (Rat.not_lt.mpr (Rat.lt_iff_le_and_ne.mp hp).1) ((num_neg _).mp h)
    simp [sx, sy, hn]
  · have hn : (x * y).num < 0 := (num_neg _).mpr
      ((Rat.mul_neg_iff_of_pos_right (pos_of_not_neg y hy sy)).mpr ((num_neg x).mp sx))
    simp [sx, sy, hn]
  · have hn : (x * y).num < 0 := (num_neg _).mpr
      ((Rat.mul_neg_iff_of_pos_left (pos_of_not_neg x hx sx)).mpr ((num_neg y).mp sy))
    simp [sx, sy, hn]
  · have hp := Rat.mul_pos (pos_of_not_neg x hx sx) (pos_of_not_neg y hy sy)
    have hn : ¬ (x * y).num < 0 :=
      fun h => (Rat.not_lt.mpr (Rat.lt_iff_le_and_ne.mp hp).1) ((num_neg _).mp h)
    simp [sx, sy, hn]

private theorem fin_posInf (x : Rat) : JF.mul (.fin x) .posInf =
    if x = 0 then .nan else if x.num < 0 then .negInf else .posInf := by
  change (if x = 0 then JF.nan else
    if (decide (x.num < 0) != false) = true then JF.negInf else JF.posInf) = _
  by_cases hz : x = 0 <;> by_cases hs : x.num < 0 <;> simp [hz, hs]

private theorem fin_negInf (x : Rat) : JF.mul (.fin x) .negInf =
    if x = 0 then .nan else if x.num < 0 then .posInf else .negInf := by
  change (if x = 0 then JF.nan else
    if (decide (x.num < 0) != true) = true then JF.negInf else JF.posInf) = _
  by_cases hz : x = 0 <;> by_cases hs : x.num < 0 <;> simp [hz, hs]

private theorem posInf_fin (x : Rat) : JF.mul .posInf (.fin x) =
    if x = 0 then .nan else if x.num < 0 then .negInf else .posInf := by
  change (if x = 0 then JF.nan else
    if (false != decide (x.num < 0)) = true then JF.negInf else JF.posInf) = _
  by_cases hz : x = 0 <;> by_cases hs : x.num < 0 <;> simp [hz, hs]

private theorem negInf_fin (x : Rat) : JF.mul .negInf (.fin x) =
    if x = 0 then .nan else if x.num < 0 then .posInf else .negInf := by
  change (if x = 0 then JF.nan else
    if (true != decide (x.num < 0)) = true then JF.negInf else JF.posInf) = _
  by_cases hz : x = 0 <;> by_cases hs : x.num < 0 <;> simp [hz, hs]

private theorem mul_finite (x y : Rat) : JF.mul (.fin x) (.fin y) = .fin (x * y) := rfl
private theorem mul_nan_left (x : JF) : JF.mul .nan x = .nan := by cases x <;> rfl
private theorem mul_nan_right (x : JF) : JF.mul x .nan = .nan := by cases x <;> rfl
private theorem mul_pp : JF.mul .posInf .posInf = .posInf := rfl
private theorem mul_pn : JF.mul .posInf .negInf = .negInf := rfl
private theorem mul_np : JF.mul .negInf .posInf = .negInf := rfl
private theorem mul_nn : JF.mul .negInf .negInf = .posInf := rfl

private theorem jf_mul_assoc (a b c : JF) : JF.mul (JF.mul a b) c = JF.mul a (JF.mul b c) := by
  cases a <;> cases b <;> cases c
  all_goals simp only [mul_finite, mul_nan_left, mul_nan_right, mul_pp, mul_pn, mul_np,
    mul_nn, fin_posInf, fin_negInf, posInf_fin, negInf_fin, Rat.mul_assoc]
  all_goals first
    | (rename_i x y
       by_cases hx : x = 0 <;> by_cases hy : y = 0
         <;> by_cases sx : x.num < 0 <;> by_cases sy : y.num < 0
         <;> simp [hx, hy, sx, sy, Rat.mul_eq_zero, mul_num_neg, mul_nan_left,
           mul_nan_right, fin_posInf, fin_negInf, posInf_fin, negInf_fin])
    | (rename_i x
       by_cases hx : x = 0 <;> by_cases sx : x.num < 0
         <;> simp [hx, sx, mul_nan_left, mul_nan_right, mul_pp, mul_pn,
           mul_np, mul_nn])
    | rfl

/-- The scalar arithmetic laws used by constant combination, including nonfinite values. -/
theorem jf_ringLaws : RingLaws JF where
  add_assoc := by
    intro a b c
    change JF.add (JF.add a b) c = JF.add a (JF.add b c)
    cases a <;> cases b <;> cases c <;> simp [JF.add, Rat.add_assoc]
  add_comm := by
    intro a b
    change JF.add a b = JF.add b a
    cases a <;> cases b <;> simp [JF.add, Rat.add_comm]
  mul_assoc := jf_mul_assoc
  mul_comm := by
    intro a b
    change JF.mul a b = JF.mul b a
    cases a <;> cases b <;> simp [mul_finite, mul_nan_left, mul_nan_right, mul_pp,
      mul_pn, mul_np, mul_nn, fin_posInf, fin_negInf, posInf_fin, negInf_fin, Rat.mul_comm]
  sub_eq := by intros; rfl
  neg_add := by
    intro a b
    change JF.neg (JF.add a b) = JF.add (JF.neg a) (JF.neg b)
    cases a <;> cases b <;> simp [JF.add, JF.neg, Rat.neg_add]
  neg_neg := by
    intro a
    change JF.neg (JF.neg a) = a
    cases a <;> simp [JF.neg, Rat.neg_neg]

example : ∃ x : Rat, x ≠ 0 ∧ ¬ x.num < 0 := by
  exact ⟨1, by decide +kernel⟩

example : ∃ x y : Rat, x ≠ 0 ∧ y ≠ 0 := by
  exact ⟨1, 1, by decide +kernel⟩

end DynExpr.Simplify
