import DynExpr.StringsParse.Surface

/-!
Exact decimal codec for the numeric literals printed by `string(val)`
(`src/Strings.jl:87-93`) and read back by `Meta.parse` (`src/Parse.jl:297`).
Every decimal `p / 10 ^ k` prints through `decimalChars`, and `numericToken`
decodes that text to the same value. Every finite binary float is such a value,
so this covers Julia's printer once its shortest-roundtrip digit choice is
modelled as exact decimal printing.
-/

namespace DynExpr.StringsParse
set_option maxHeartbeats 400000

/-- Exact decimal values: the denominator divides a power of ten. -/
def Terminating (q : Rat) : Prop := ∃ k : Nat, q.den ∣ 10 ^ k

/-- Scalar constructor chosen by the Float32 flag of a numeric literal. -/
def scalarOf (single : Bool) (q : Rat) : Scalar :=
  if single then .float32 (.fin q) else .real (.fin q)

/-! ### Digit lists -/

def digitStep (n : Nat) (c : Char) : Nat := n * 10 + (c.toNat - 48)

/-- Value of a decimal digit list, as computed by `decimalNat`. -/
def digitVal (cs : List Char) : Nat := cs.foldl digitStep 0

theorem foldl_digitStep (a : Nat) (cs : List Char) :
    cs.foldl digitStep a = a * 10 ^ cs.length + digitVal cs := by
  induction cs generalizing a with
  | nil => simp [digitVal]
  | cons c cs ih =>
    have h1 : (c :: cs).foldl digitStep a = cs.foldl digitStep (digitStep a c) := rfl
    have h2 : digitVal (c :: cs) = cs.foldl digitStep (digitStep 0 c) := rfl
    rw [h1, h2, ih, ih (digitStep 0 c)]
    simp only [digitStep, List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    ac_rfl

theorem digitVal_append (xs ys : List Char) :
    digitVal (xs ++ ys) = digitVal xs * 10 ^ ys.length + digitVal ys := by
  rw [digitVal, List.foldl_append, foldl_digitStep]
  rfl

theorem digitVal_replicate (n : Nat) : digitVal (List.replicate n '0') = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', digitVal_append, ih]
    rfl

theorem digitVal_zero_digit (xs : List Char) :
    digitVal (xs ++ ['0']) = digitVal xs * 10 ^ 1 := by
  rw [digitVal_append]
  rfl

theorem digitVal_toDigits (n : Nat) : digitVal (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · rename_i h
      show digitStep 0 _ = n
      simp [digitStep, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · rename_i h
      rw [digitVal_append, ih (n / 10) (by omega)]
      show n / 10 * 10 ^ 1 + digitStep 0 _ = n
      simp only [digitStep, Nat.toNat_digitChar_sub_48_of_lt_ten (Nat.mod_lt n (by decide))]
      omega

theorem toDigits_isDigit {n : Nat} : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
  fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem decimalNat_eq {cs : List Char} (hne : cs ≠ []) (hd : ∀ c ∈ cs, c.isDigit = true) :
    decimalNat cs = some (digitVal cs) := by
  have h1 : cs.isEmpty = false := by cases cs <;> simp_all
  have h2 : cs.all Char.isDigit = true := List.all_eq_true.2 hd
  rw [decimalNat]
  simp [h1, h2] <;> rfl

theorem toDigits_cons (n : Nat) : ∃ d ds, Nat.toDigits 10 n = d :: ds ∧ d.isDigit = true ∧
    ∀ c ∈ ds, c.isDigit = true := by
  have hd := @toDigits_isDigit n
  cases h : Nat.toDigits 10 n with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons d ds =>
    rw [h] at hd
    exact ⟨d, ds, rfl, hd d (by simp), fun c hc => hd c (by simp [hc])⟩

theorem digit_ne {c : Char} (h : c.isDigit = true) :
    c ≠ '-' ∧ c ≠ '+' ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ 'f' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro hc; subst hc; exact absurd h (by decide))

theorem digit_not_whitespace {c : Char} (h : c.isDigit = true) : c.isWhitespace = false := by
  have h1 : c ≠ ' ' := by intro hc; subst hc; exact absurd h (by decide)
  have h2 : c ≠ '\t' := by intro hc; subst hc; exact absurd h (by decide)
  have h3 : c ≠ '\r' := by intro hc; subst hc; exact absurd h (by decide)
  have h4 : c ≠ '\n' := by intro hc; subst hc; exact absurd h (by decide)
  simp [Char.isWhitespace, h1, h2, h3, h4]

theorem mem_of_take {l : List Char} {k : Nat} {c : Char} (h : c ∈ l.take k) : c ∈ l := by
  rw [← List.take_append_drop k l]
  exact List.mem_append_left _ h

theorem mem_of_drop {l : List Char} {k : Nat} {c : Char} (h : c ∈ l.drop k) : c ∈ l := by
  rw [← List.take_append_drop k l]
  exact List.mem_append_right _ h

theorem contains_eq_false {l : List Char} {a : Char} (h : ∀ c ∈ l, c ≠ a) :
    l.contains a = false := by
  have hn : a ∉ l := fun hm => h a hm rfl
  simpa using hn

theorem span_loop_append {α : Type} (p : α → Bool) (xs ys acc : List α)
    (hx : ∀ x ∈ xs, p x = true) (hy : ∀ y ∈ ys.head?, p y = false) :
    List.span.loop p (xs ++ ys) acc = (acc.reverse ++ xs, ys) := by
  induction xs generalizing acc with
  | nil =>
    cases ys with
    | nil => simp [List.span.loop]
    | cons y ys =>
      have hpy : p y = false := hy y (by simp)
      simp [List.span.loop, hpy]
  | cons x xs ih =>
    have hpx : p x = true := hx x (by simp)
    simp only [List.cons_append, List.span.loop, hpx]
    rw [ih (x :: acc) (fun z hz => hx z (by simp [hz]))]
    simp

theorem span_append {α : Type} (p : α → Bool) (xs ys : List α)
    (hx : ∀ x ∈ xs, p x = true) (hy : ∀ y ∈ ys.head?, p y = false) :
    (xs ++ ys).span p = (xs, ys) := by
  rw [List.span, span_loop_append p xs ys [] hx hy]
  simp

/-! ### Trailing zeros -/

theorem stripTrailingZeros_spec (cs : List Char) :
    ∃ t, cs = stripTrailingZeros cs ++ List.replicate t '0' := by
  induction cs with
  | nil => exact ⟨0, rfl⟩
  | cons c cs ih =>
    obtain ⟨t, ht⟩ := ih
    by_cases h : (stripTrailingZeros cs).isEmpty = true ∧ c = '0'
    · obtain ⟨he, hc⟩ := h
      have hnil : stripTrailingZeros cs = [] := List.isEmpty_iff.1 he
      refine ⟨t + 1, ?_⟩
      have hs : stripTrailingZeros (c :: cs) = [] := by
        simp [stripTrailingZeros, he, hc]
      rw [hs, List.nil_append, List.replicate_succ, hc]
      rw [hnil, List.nil_append] at ht
      rw [← ht]
    · refine ⟨t, ?_⟩
      have hif : ((stripTrailingZeros cs).isEmpty && c == '0') = false := by
        cases he : (stripTrailingZeros cs).isEmpty
        · rfl
        · have hc : c ≠ '0' := fun hc => h ⟨he, hc⟩
          simp [hc]
      have hs : stripTrailingZeros (c :: cs) = c :: stripTrailingZeros cs := by
        simp only [stripTrailingZeros, hif, Bool.false_eq_true, ↓reduceIte]
      rw [hs, List.cons_append, ← ht]

theorem mem_stripTrailingZeros {cs : List Char} {c : Char} (h : c ∈ stripTrailingZeros cs) :
    c ∈ cs := by
  obtain ⟨t, ht⟩ := stripTrailingZeros_spec cs
  rw [ht]
  exact List.mem_append_left _ h

/-! ### Scaled values -/

/-- `z * 10 ^ e` with an integer exponent. -/
def sciVal (z : Int) (e : Int) : Rat := (z : Rat) * (10 : Rat) ^ e

def signed (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

theorem ten_ne_zero : (10 : Rat) ≠ 0 := by decide

theorem natPow_cast (k : Nat) : ((10 ^ k : Nat) : Rat) = (10 : Rat) ^ (k : Int) := by
  rw [Rat.zpow_natCast]
  simp

theorem sciVal_shift (z : Int) (t : Nat) (e : Int) :
    sciVal (z * ((10 ^ t : Nat) : Int)) e = sciVal z (e + t) := by
  unfold sciVal
  rw [Rat.intCast_mul, Rat.intCast_natCast, natPow_cast, Rat.mul_assoc,
    ← Rat.zpow_add ten_ne_zero, Int.add_comm]

theorem sciVal_congr (z : Int) {e f : Int} (h : e = f) : sciVal z e = sciVal z f := by rw [h]

theorem signed_mul (neg : Bool) (a b : Nat) : signed neg (a * b) = signed neg a * (b : Int) := by
  cases neg <;> simp [signed, Int.natCast_mul, Int.neg_mul]

theorem signed_natAbs (z : Int) : signed (decide (z < 0)) z.natAbs = z := by
  unfold signed
  by_cases h : z < 0
  · simp only [h, decide_true, ↓reduceIte]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    omega

theorem mkRat_eq_sciVal (z : Int) (s : Nat) : mkRat z (10 ^ s) = sciVal z (-(s : Int)) := by
  rw [Rat.mkRat_eq_div, Rat.div_def, natPow_cast, ← Rat.zpow_neg]
  rfl

/-- The arithmetic of `numericToken` after its digits are read. -/
theorem decode_value (neg : Bool) (n f : Nat) (e : Int) :
    (if e ≥ 0 then ((if neg then -(n : Rat) else (n : Rat)) / ((10 ^ f : Nat) : Rat)) *
        ((10 ^ e.toNat : Nat) : Rat)
      else ((if neg then -(n : Rat) else (n : Rat)) / ((10 ^ f : Nat) : Rat)) /
        ((10 ^ (-e).toNat : Nat) : Rat)) = sciVal (signed neg n) (e - f) := by
  have hsign : (if neg then -(n : Rat) else (n : Rat)) = ((signed neg n : Int) : Rat) := by
    cases neg <;> simp [signed, Rat.intCast_natCast]
  rw [hsign]
  split
  · rename_i h
    rw [Rat.div_def, natPow_cast, natPow_cast, ← Rat.zpow_neg, Rat.mul_assoc,
      ← Rat.zpow_add ten_ne_zero]
    exact sciVal_congr _ (by omega)
  · rename_i h
    rw [Rat.div_def, Rat.div_def, natPow_cast, natPow_cast, ← Rat.zpow_neg, ← Rat.zpow_neg,
      Rat.mul_assoc, ← Rat.zpow_add ten_ne_zero]
    exact sciVal_congr _ (by omega)

/-! ### Decimal representation of terminating rationals -/

theorem decimalScale_dvd (fuel d : Nat) :
    d ∣ (decimalScale fuel d).2 * 10 ^ (decimalScale fuel d).1 := by
  induction fuel generalizing d with
  | zero => simp [decimalScale]
  | succ fuel ih =>
    by_cases h2 : d % 2 = 0 ∧ 0 < d
    · rw [decimalScale, if_pos h2]
      show d ∣ (decimalScale fuel (d / 2)).2 * 10 ^ ((decimalScale fuel (d / 2)).1 + 1)
      have hd : d = 2 * (d / 2) := by omega
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      have hx := ih (d / 2)
      generalize (decimalScale fuel (d / 2)).2 * 10 ^ (decimalScale fuel (d / 2)).1 = X at hx ⊢
      refine Nat.dvd_trans (b := 2 * X) ?_ ⟨5, by omega⟩
      rw [hd]
      exact Nat.mul_dvd_mul_left 2 hx
    · by_cases h5 : d % 5 = 0 ∧ 0 < d
      · rw [decimalScale, if_neg h2, if_pos h5]
        show d ∣ (decimalScale fuel (d / 5)).2 * 10 ^ ((decimalScale fuel (d / 5)).1 + 1)
        have hd : d = 5 * (d / 5) := by omega
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        have hx := ih (d / 5)
        generalize (decimalScale fuel (d / 5)).2 * 10 ^ (decimalScale fuel (d / 5)).1 = X at hx ⊢
        refine Nat.dvd_trans (b := 5 * X) ?_ ⟨2, by omega⟩
        rw [hd]
        exact Nat.mul_dvd_mul_left 5 hx
      · rw [decimalScale, if_neg h2, if_neg h5]
        show d ∣ d * 10 ^ 0
        simp

theorem decimalScale_residue_dvd (fuel d : Nat) : (decimalScale fuel d).2 ∣ d := by
  induction fuel generalizing d with
  | zero => exact Nat.dvd_refl d
  | succ fuel ih =>
    by_cases h2 : d % 2 = 0 ∧ 0 < d
    · rw [decimalScale, if_pos h2]
      exact Nat.dvd_trans (ih (d / 2)) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h2.1))
    · by_cases h5 : d % 5 = 0 ∧ 0 < d
      · rw [decimalScale, if_neg h2, if_pos h5]
        exact Nat.dvd_trans (ih (d / 5)) (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h5.1))
      · rw [decimalScale, if_neg h2, if_neg h5]
        exact Nat.dvd_refl d

theorem decimalScale_residue (fuel d : Nat) (hd : 0 < d) (hf : d ≤ fuel) :
    (decimalScale fuel d).2 % 2 ≠ 0 ∧ (decimalScale fuel d).2 % 5 ≠ 0 := by
  induction fuel generalizing d with
  | zero => omega
  | succ fuel ih =>
    by_cases h2 : d % 2 = 0 ∧ 0 < d
    · rw [decimalScale, if_pos h2]
      exact ih (d / 2) (by omega) (by omega)
    · by_cases h5 : d % 5 = 0 ∧ 0 < d
      · rw [decimalScale, if_neg h2, if_pos h5]
        exact ih (d / 5) (by omega) (by omega)
      · rw [decimalScale, if_neg h2, if_neg h5]
        show d % 2 ≠ 0 ∧ d % 5 ≠ 0
        constructor <;> omega

theorem coprime_ten {r : Nat} (h2 : r % 2 ≠ 0) (h5 : r % 5 ≠ 0) : Nat.Coprime r 10 := by
  have c2 : Nat.Coprime r 2 := by
    show Nat.gcd r 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, show r % 2 = 1 by omega]
    simp
  have c5 : Nat.Coprime r 5 := by
    show Nat.gcd r 5 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec]
    have : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> simp
  exact Nat.Coprime.mul_right c2 c5

/-- The scale chosen by `toDecimal` clears every terminating denominator. -/
theorem den_dvd_scale {q : Rat} (hq : Terminating q) :
    q.den ∣ 10 ^ (decimalScale q.den q.den).1 := by
  obtain ⟨k, hk⟩ := hq
  have hres := decimalScale_residue q.den q.den q.den_pos (Nat.le_refl _)
  have hco : Nat.Coprime (decimalScale q.den q.den).2 (10 ^ k) :=
    Nat.Coprime.pow_right k (coprime_ten hres.1 hres.2)
  have hdk : (decimalScale q.den q.den).2 ∣ 10 ^ k :=
    Nat.dvd_trans (decimalScale_residue_dvd q.den q.den) hk
  have hg := Nat.dvd_gcd (Nat.dvd_refl _) hdk
  rw [Nat.Coprime.gcd_eq_one hco] at hg
  have hone : (decimalScale q.den q.den).2 = 1 := Nat.dvd_one.1 hg
  have h := decimalScale_dvd q.den q.den
  rw [hone, Nat.one_mul] at h
  exact h

theorem scaleFactor_pos {q : Rat} (hq : Terminating q) :
    0 < 10 ^ (decimalScale q.den q.den).1 / q.den := by
  have hd := den_dvd_scale hq
  generalize (decimalScale q.den q.den).1 = s at hd ⊢
  have hc : q.den * (10 ^ s / q.den) = 10 ^ s := Nat.mul_div_cancel' hd
  have hpos : 10 ^ s ≠ 0 := by simp
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0, Nat.mul_zero] at hc
  exact hpos hc.symm

/-- `toDecimal` represents every terminating rational exactly. -/
theorem toDecimal_value {q : Rat} (hq : Terminating q) :
    mkRat (toDecimal q).mant (10 ^ (toDecimal q).scale) = q := by
  have hd := den_dvd_scale hq
  have hpos := scaleFactor_pos hq
  simp only [toDecimal]
  generalize (decimalScale q.den q.den).1 = s at hd hpos ⊢
  have hc : q.den * (10 ^ s / q.den) = 10 ^ s := Nat.mul_div_cancel' hd
  generalize 10 ^ s / q.den = c at hc hpos ⊢
  rw [← hc, Rat.mkRat_mul_right (Nat.ne_of_gt hpos), Rat.mkRat_self]

theorem terminating_decimal (p : Int) (k : Nat) : Terminating (mkRat p (10 ^ k)) := by
  refine ⟨k, ?_⟩
  have hk : 10 ^ k ≠ 0 := by simp
  rw [Rat.den_mkRat, if_neg hk]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

theorem terminating_neg {q : Rat} (hq : Terminating q) : Terminating (-q) := by
  obtain ⟨k, hk⟩ := hq
  exact ⟨k, by rw [Rat.neg_den]; exact hk⟩

theorem toDecimal_mant_nonneg {q : Rat} (hq : 0 ≤ q) : 0 ≤ (toDecimal q).mant := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.2 hq
  simp only [toDecimal]
  exact Int.mul_nonneg hn (by exact_mod_cast Nat.zero_le _)

theorem toDecimal_mant_neg {q : Rat} (hq : Terminating q) (hneg : q < 0) :
    (toDecimal q).mant < 0 := by
  have hn : q.num < 0 := by
    have : ¬ 0 ≤ q.num := fun h => Rat.not_le.2 hneg (Rat.num_nonneg.1 h)
    omega
  have hpos := scaleFactor_pos hq
  simp only [toDecimal]
  exact Int.mul_neg_of_neg_of_pos hn (by exact_mod_cast hpos)

theorem toDecimal_neg (q : Rat) :
    toDecimal (-q) = ⟨-(toDecimal q).mant, (toDecimal q).scale⟩ := by
  simp [toDecimal, Rat.neg_num, Rat.neg_den, Int.neg_mul]

/-! ### Printed layout -/

def signChars (neg : Bool) : List Char := if neg then ['-'] else []

/-- Exponent suffix `e<int>` or Float32 `f<int>`. -/
def expChars (single : Bool) (e : Int) : List Char :=
  (if single then 'f' else 'e') :: (toString e).toList

theorem minus_toList : ("-" : String).toList = ['-'] := by decide

theorem intChars (e : Int) :
    (toString e).toList = signChars (decide (e < 0)) ++ Nat.toDigits 10 e.natAbs := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  by_cases h : 0 ≤ e
  · have h1 : e.toNat = e.natAbs := by omega
    have h2 : decide (e < 0) = false := by simp; omega
    rw [if_pos h, h1, h2]
    simp [signChars]
  · have h1 : (-e).toNat = e.natAbs := by omega
    have h2 : decide (e < 0) = true := by simp; omega
    rw [if_neg h, h1, h2, String.toList_append, minus_toList]
    simp [signChars]

theorem intChars_ne_f (e : Int) : ∀ c ∈ (toString e).toList, c ≠ 'f' := by
  intro c hc
  rw [intChars] at hc
  rcases List.mem_append.1 hc with hc | hc
  · cases hb : decide (e < 0) <;> simp_all [signChars]
  · exact (digit_ne (toDigits_isDigit c hc)).2.2.2.2.2

theorem decimalInt_toString (e : Int) : decimalInt (toString e).toList = some e := by
  obtain ⟨d, ds, hD, hd, _⟩ := toDigits_cons e.natAbs
  have hN : decimalNat (d :: ds) = some e.natAbs := by
    rw [← hD, decimalNat_eq Nat.toDigits_ne_nil toDigits_isDigit, digitVal_toDigits]
  obtain ⟨hdm, hdp, -⟩ := digit_ne hd
  rw [intChars, hD]
  by_cases h : e < 0
  · simp [decimalInt, signChars, h, hN]
    omega
  · simp [decimalInt, signChars, h, hN, hdm, hdp]
    omega

/-- Shape of every printed decimal: sign, nonempty digits, point, digits, and
an optional exponent suffix, together with the decoded value equation. -/
theorem decimalChars_shape (x : Decimal) (single : Bool) : ∃ W F : List Char, ∃ e : Int,
    ∃ sfx : List Char,
    decimalChars x single = signChars (decide (x.mant < 0)) ++ W ++ '.' :: F ++ sfx ∧
    W ≠ [] ∧ (∀ c ∈ W, c.isDigit = true) ∧ (∀ c ∈ F, c.isDigit = true) ∧
    ((sfx = [] ∧ single = false ∧ e = 0) ∨ sfx = expChars single e) ∧
    sciVal (signed (decide (x.mant < 0)) (digitVal (W ++ F))) (e - F.length) =
      sciVal (signed (decide (x.mant < 0)) x.mant.natAbs) (-(x.scale : Int)) := by
  obtain ⟨z, s⟩ := x
  have hsign : (if z < 0 then ['-'] else []) = signChars (decide (z < 0)) := by
    by_cases h : z < 0 <;> simp [signChars, h]
  have hzero : ∀ c ∈ ['0'], c.isDigit = true := by
    intro c hc
    rw [List.mem_singleton.1 hc]
    decide
  unfold decimalChars
  simp only [hsign]
  generalize decide (z < 0) = neg
  generalize z.natAbs = m
  have hds := digitVal_toDigits m
  have hdd : ∀ c ∈ Nat.toDigits 10 m, c.isDigit = true := toDigits_isDigit
  split
  · -- scientific form
    rename_i hsci
    have hmpos : 0 < m := by
      rcases hsci with h | ⟨_, h, _⟩
      · apply Nat.pos_of_ne_zero
        intro h0
        rw [h0, Nat.zero_div] at h
        omega
      · exact h
    obtain ⟨t, ht⟩ := stripTrailingZeros_spec (Nat.toDigits 10 m)
    have hlen : (Nat.toDigits 10 m).length = (stripTrailingZeros (Nat.toDigits 10 m)).length + t := by
      conv => lhs; rw [ht]
      rw [List.length_append, List.length_replicate]
    rw [hlen]
    generalize stripTrailingZeros (Nat.toDigits 10 m) = sig at ht ⊢
    have hval : digitVal sig * 10 ^ t = m := by
      rw [← hds, ht, digitVal_append, digitVal_replicate, List.length_replicate, Nat.add_zero]
    have hsigd : ∀ c ∈ sig, c.isDigit = true :=
      fun c hc => hdd c (by rw [ht]; exact List.mem_append_left _ hc)
    have hslen : 1 ≤ sig.length := by
      cases sig with
      | nil =>
        rw [← hval] at hmpos
        simp [digitVal] at hmpos
      | cons c cs => simp
    have hW : sig.take 1 ≠ [] := by
      cases sig with
      | nil => simp at hslen
      | cons c cs => simp
    have hWd : ∀ c ∈ sig.take 1, c.isDigit = true := fun c hc => hsigd c (mem_of_take hc)
    by_cases htail : (sig.drop 1).isEmpty = true
    · have hdrop : sig.drop 1 = [] := List.isEmpty_iff.1 htail
      have hone : sig.length = 1 := by
        have h1 := List.length_drop (i := 1) (l := sig)
        rw [hdrop, List.length_nil] at h1
        omega
      have htake : sig.take 1 = sig := List.take_of_length_le (by omega)
      refine ⟨sig.take 1, ['0'], ((sig.length + t : Nat) : Int) - 1 - s,
        expChars single (((sig.length + t : Nat) : Int) - 1 - s), ?_, hW, hWd, hzero,
        Or.inr rfl, ?_⟩
      · simp only [htail, ↓reduceIte, expChars]
      · rw [htake, digitVal_zero_digit, signed_mul, ← hval, signed_mul, sciVal_shift, sciVal_shift]
        exact sciVal_congr _ (by simp only [List.length_cons, List.length_nil]; omega)
    · have hif : (sig.drop 1).isEmpty = false := by simpa using htail
      refine ⟨sig.take 1, sig.drop 1, ((sig.length + t : Nat) : Int) - 1 - s,
        expChars single (((sig.length + t : Nat) : Int) - 1 - s), ?_, hW, hWd,
        fun c hc => hsigd c (mem_of_drop hc), Or.inr rfl, ?_⟩
      · simp only [hif, Bool.false_eq_true, ↓reduceIte, expChars]
      · rw [List.take_append_drop, ← hval, signed_mul, sciVal_shift, List.length_drop]
        exact sciVal_congr _ (by omega)
  · -- plain decimal form
    generalize hpad : List.replicate (s + 1 - (Nat.toDigits 10 m).length) '0' ++
      Nat.toDigits 10 m = padded
    have hplen : s + 1 ≤ padded.length := by
      rw [← hpad, List.length_append, List.length_replicate]
      omega
    have hpval : digitVal padded = m := by
      rw [← hpad, digitVal_append, digitVal_replicate, Nat.zero_mul, Nat.zero_add, hds]
    have hpd : ∀ c ∈ padded, c.isDigit = true := by
      intro c hc
      rw [← hpad, List.mem_append] at hc
      rcases hc with hc | hc
      · rw [List.eq_of_mem_replicate hc]
        decide
      · exact hdd c hc
    have hW : padded.take (padded.length - s) ≠ [] := by
      intro h0
      have h1 := congrArg List.length h0
      rw [List.length_take, List.length_nil] at h1
      omega
    have hWd : ∀ c ∈ padded.take (padded.length - s), c.isDigit = true :=
      fun c hc => hpd c (mem_of_take hc)
    have hflen : (padded.drop (padded.length - s)).length = s := by
      rw [List.length_drop]
      omega
    have hsplit := List.take_append_drop (padded.length - s) padded
    generalize padded.take (padded.length - s) = W at hW hWd hsplit ⊢
    generalize padded.drop (padded.length - s) = Fr at hflen hsplit ⊢
    have hFrd : ∀ c ∈ Fr, c.isDigit = true :=
      fun c hc => hpd c (by rw [← hsplit]; exact List.mem_append_right _ hc)
    obtain ⟨t, ht⟩ := stripTrailingZeros_spec Fr
    have hstrd : ∀ c ∈ stripTrailingZeros Fr, c.isDigit = true :=
      fun c hc => hFrd c (mem_stripTrailingZeros hc)
    generalize stripTrailingZeros Fr = F' at ht hstrd ⊢
    have hmval : digitVal (W ++ F') * 10 ^ t = m := by
      rw [← hpval, ← hsplit, ht, ← List.append_assoc, digitVal_append (W ++ F'),
        digitVal_replicate, List.length_replicate, Nat.add_zero]
    have hslen : s = F'.length + t := by
      rw [← hflen, ht, List.length_append, List.length_replicate]
    have hsfx : ∃ sfx : List Char, (if single then ['f', '0'] else []) = sfx ∧
        ((sfx = [] ∧ single = false ∧ (0 : Int) = 0) ∨ sfx = expChars single 0) := by
      cases single
      · exact ⟨[], by simp, Or.inl ⟨rfl, rfl, rfl⟩⟩
      · refine ⟨['f', '0'], by simp, Or.inr ?_⟩
        rw [expChars, intChars]
        simp [signChars]
    obtain ⟨sfx, hsfxEq, hsfxOk⟩ := hsfx
    rw [hsfxEq]
    by_cases hfe : F'.isEmpty = true
    · have hnil : F' = [] := List.isEmpty_iff.1 hfe
      refine ⟨W, ['0'], 0, sfx, ?_, hW, hWd, hzero, hsfxOk, ?_⟩
      · simp [hfe]
      · rw [hnil, List.append_nil] at hmval
        rw [hnil, List.length_nil, Nat.zero_add] at hslen
        rw [digitVal_zero_digit, signed_mul, ← hmval, signed_mul, sciVal_shift, sciVal_shift]
        exact sciVal_congr _ (by simp only [List.length_cons, List.length_nil]; omega)
    · have hif : F'.isEmpty = false := by simpa using hfe
      refine ⟨W, F', 0, sfx, ?_, hW, hWd, hstrd, hsfxOk, ?_⟩
      · simp [hif]
      · rw [← hmval, signed_mul, sciVal_shift]
        exact sciVal_congr _ (by omega)

/-! ### Decoding the printed layout -/

theorem numericToken_layout (neg single : Bool) (W F sfx : List Char) (e : Int)
    (hW : W ≠ []) (hWd : ∀ c ∈ W, c.isDigit = true) (hFd : ∀ c ∈ F, c.isDigit = true)
    (hsfx : (sfx = [] ∧ single = false ∧ e = 0) ∨ sfx = expChars single e) :
    numericToken (String.ofList (signChars neg ++ W ++ '.' :: F ++ sfx)) =
      some (scalarOf single (sciVal (signed neg (digitVal (W ++ F))) (e - F.length))) := by
  obtain ⟨w, W', rfl⟩ : ∃ w W', W = w :: W' := by
    cases W with
    | nil => exact absurd rfl hW
    | cons w W' => exact ⟨w, W', rfl⟩
  have hw : w.isDigit = true := hWd w (by simp)
  obtain ⟨hwm, hwp, hwd, -, -, -⟩ := digit_ne hw
  have hpre : ∀ c ∈ signChars neg ++ (w :: W') ++ '.' :: F,
      c = '-' ∨ c = '.' ∨ c.isDigit = true := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · left
        cases neg <;> simp_all [signChars]
      · exact Or.inr (Or.inr (hWd c hc))
    · rcases List.mem_cons.1 hc with hc | hc
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (hFd c hc))
  have hnoF : ∀ c ∈ signChars neg ++ (w :: W') ++ '.' :: F, c ≠ 'f' := by
    intro c hc
    rcases hpre c hc with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · exact (digit_ne h).2.2.2.2.2
  have hpE : ∀ c ∈ signChars neg ++ (w :: W') ++ '.' :: F,
      (c != 'e' && c != 'E' && c != 'f') = true := by
    intro c hc
    rcases hpre c hc with h | h | h
    · rw [h]; decide
    · rw [h]; decide
    · obtain ⟨-, -, -, h1, h2, h3⟩ := digit_ne h
      simp [h1, h2, h3]
  have hsfxF : sfx.contains 'f' = single := by
    rcases hsfx with ⟨rfl, rfl, -⟩ | rfl
    · rfl
    · simp only [expChars, List.contains_cons, contains_eq_false (intChars_ne_f e), Bool.or_false]
      cases single <;> decide
  have hsfxStop : ∀ y ∈ sfx.head?, (y != 'e' && y != 'E' && y != 'f') = false := by
    rcases hsfx with ⟨rfl, -, -⟩ | rfl
    · simp
    · intro y hy
      simp only [expChars, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      cases single <;> decide
  have hcont : (signChars neg ++ (w :: W') ++ '.' :: F ++ sfx).contains 'f' = single := by
    rw [List.contains_append, contains_eq_false hnoF, hsfxF, Bool.false_or]
  have hspanE := span_append (fun c => c != 'e' && c != 'E' && c != 'f') _ sfx hpE hsfxStop
  have hneg : ((signChars neg ++ (w :: W') ++ '.' :: F).head? == some '-') = neg := by
    cases neg <;> simp [signChars, hwm]
  have hmant : (if (neg || (signChars neg ++ (w :: W') ++ '.' :: F).head? == some '+') = true
      then (signChars neg ++ (w :: W') ++ '.' :: F).tail!
      else signChars neg ++ (w :: W') ++ '.' :: F) = (w :: W') ++ '.' :: F := by
    cases neg <;> simp [signChars, hwp]
  have hspanD : ((w :: W') ++ '.' :: F).span (· != '.') = (w :: W', '.' :: F) := by
    apply span_append
    · intro c hc
      rcases List.mem_cons.1 hc with h | h
      · subst h; simp [hwd]
      · simp [(digit_ne (hWd c (by simp [h]))).2.2.1]
    · simp
  have hall : ((w :: W') ++ F).all Char.isDigit = true := by
    apply List.all_eq_true.2
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hWd c h
    · exact hFd c h
  have hdn : decimalNat ((w :: W') ++ F) = some (digitVal ((w :: W') ++ F)) :=
    decimalNat_eq (by simp) (List.all_eq_true.1 hall)
  have hval := decode_value neg (digitVal ((w :: W') ++ F)) F.length e
  unfold numericToken
  simp only [String.toList_ofList, hcont, hspanE, Option.bind_eq_bind, Option.bind_some,
    hneg, hmant, hspanD, List.isEmpty_cons, List.tail!_cons, hall, Bool.not_true,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, hdn, Option.pure_def]
  rcases hsfx with ⟨rfl, rfl, rfl⟩ | rfl
  · simp only [List.isEmpty_nil, ↓reduceIte, hval, scalarOf]
  · simp only [expChars, List.isEmpty_cons, List.tail!_cons, decimalInt_toString,
      Option.bind_some, Bool.false_eq_true, ↓reduceIte, hval, scalarOf]

/-- General codec identity: every exact decimal `p / 10 ^ k` prints to a
literal that `numericToken` decodes to the same value and Float32 flag. -/
theorem numericToken_decimalChars (x : Decimal) (single : Bool) :
    numericToken (String.ofList (decimalChars x single)) =
      some (scalarOf single (mkRat x.mant (10 ^ x.scale))) := by
  obtain ⟨W, F, e, sfx, hshape, hW, hWd, hFd, hsfx, hval⟩ := decimalChars_shape x single
  rw [hshape, numericToken_layout _ _ W F sfx e hW hWd hFd hsfx, hval, signed_natAbs,
    mkRat_eq_sciVal]

theorem numericToken_finiteText_any {q : Rat} (hq : Terminating q) (single : Bool) :
    numericToken (finiteText q single) = some (scalarOf single q) := by
  unfold finiteText
  rw [numericToken_decimalChars, toDecimal_value hq]

/-- Rendered `Float64` constants decode to the same real value. -/
theorem numericToken_finiteText {q : Rat} (hq : Terminating q) :
    numericToken (finiteText q false) = some (.real (.fin q)) :=
  numericToken_finiteText_any hq false

/-- Rendered `f0`-suffixed literals decode to the same Float32 value. -/
theorem numericToken_finiteText_single {q : Rat} (hq : Terminating q) :
    numericToken (finiteText q true) = some (.float32 (.fin q)) :=
  numericToken_finiteText_any hq true

/-- Arbitrary finite terminating decimal, Julia's `Float64` print path
(`src/Strings.jl:87-93`) followed by the numeric-literal decoder of `Meta.parse`
(`src/Parse.jl:297`). No output-success hypothesis. -/
def DecimalLiteralRoundtrip : Prop := ∀ (p : Int) (k : Nat),
  numericToken (realText (.fin (mkRat p (10 ^ k)))) = some (.real (.fin (mkRat p (10 ^ k))))

theorem decimalLiteralRoundtrip : DecimalLiteralRoundtrip :=
  fun p k => numericToken_finiteText (terminating_decimal p k)

/-- `Float32` constants print through the `Float64` path at
`src/Strings.jl:87-93`, so their decoded literal is a real, never a Float32. -/
theorem numericToken_scalarText_float32 {q : Rat} (hq : Terminating q) :
    numericToken (scalarText (.float32 (.fin q))) = some (.real (.fin q)) :=
  numericToken_finiteText hq

/-! ### Lexing printed literals -/

theorem finiteText_layout_nonneg {q : Rat} (hq : 0 ≤ q) : ∃ W F : List Char, ∃ e : Int,
    ∃ sfx : List Char, (finiteText q false).toList = W ++ '.' :: F ++ sfx ∧
    W ≠ [] ∧ (∀ c ∈ W, c.isDigit = true) ∧ (∀ c ∈ F, c.isDigit = true) ∧
    (sfx = [] ∨ sfx = expChars false e) := by
  obtain ⟨W, F, e, sfx, hshape, hW, hWd, hFd, hsfx, -⟩ := decimalChars_shape (toDecimal q) false
  have hm : decide ((toDecimal q).mant < 0) = false := by
    have := toDecimal_mant_nonneg hq
    simp only [decide_eq_false_iff_not]
    omega
  refine ⟨W, F, e, sfx, ?_, hW, hWd, hFd, ?_⟩
  · rw [finiteText, String.toList_ofList, hshape, hm]
    simp [signChars]
  · rcases hsfx with ⟨h, -, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h

/-- A nonnegative printed literal starts with a digit. -/
theorem finiteText_nonneg_head {q : Rat} (hq : 0 ≤ q) :
    ∃ c cs, (finiteText q false).toList = c :: cs ∧ c.isDigit = true := by
  obtain ⟨W, F, e, sfx, h, hW, hWd, -, -⟩ := finiteText_layout_nonneg hq
  cases W with
  | nil => exact absurd rfl hW
  | cons w W' =>
    exact ⟨w, W' ++ '.' :: F ++ sfx, by rw [h]; simp, hWd w (by simp)⟩

theorem decimalChars_neg (z : Int) (s : Nat) (single : Bool) (hz : z < 0) :
    decimalChars ⟨z, s⟩ single = '-' :: decimalChars ⟨-z, s⟩ single := by
  have hz' : ¬ -z < 0 := by omega
  unfold decimalChars
  simp only [hz, hz', ↓reduceIte, Int.natAbs_neg, List.cons_append, List.nil_append]
  split <;> simp

/-- Negative printed literals are a minus sign followed by the printed magnitude. -/
theorem finiteText_neg {q : Rat} (hq : Terminating q) (hneg : q < 0) :
    finiteText q false = "-" ++ finiteText (-q) false := by
  rw [← String.toList_inj, String.toList_append, minus_toList]
  unfold finiteText
  rw [String.toList_ofList, String.toList_ofList, toDecimal_neg]
  exact decimalChars_neg _ _ _ (toDecimal_mant_neg hq hneg)

theorem lex_layout (fuel : Nat) (W F sfx rest : List Char) (e : Int)
    (hW : W ≠ []) (hWd : ∀ c ∈ W, c.isDigit = true) (hFd : ∀ c ∈ F, c.isDigit = true)
    (hsfx : sfx = [] ∨ sfx = expChars false e)
    (hrest : ∀ c ∈ rest.head?, c.isDigit = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ 'f') :
    lex (fuel + 1) (W ++ '.' :: F ++ sfx ++ rest) =
      String.ofList (W ++ '.' :: F ++ sfx) :: lex fuel rest := by
  obtain ⟨w, W', rfl⟩ : ∃ w W', W = w :: W' := by
    cases W with
    | nil => exact absurd rfl hW
    | cons w W' => exact ⟨w, W', rfl⟩
  have hw : w.isDigit = true := hWd w (by simp)
  have hws := digit_not_whitespace hw
  have hbody : ∀ c ∈ W' ++ '.' :: F, (c.isDigit || c == '.') = true := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · simp [hWd c (by simp [h])]
    · rcases List.mem_cons.1 h with h | h
      · subst h; decide
      · simp [hFd c h]
  have hrestStop : ∀ y ∈ rest.head?, (y.isDigit || y == '.') = false := by
    intro y hy
    obtain ⟨h1, h2, -⟩ := hrest y hy
    simp [h1, h2]
  have hrestDigit : ∀ y ∈ rest.head?, Char.isDigit y = false := fun y hy => (hrest y hy).1
  rcases hsfx with rfl | rfl
  · have hspan : List.span (fun x => x.isDigit || x == '.') (W' ++ '.' :: (F ++ rest)) =
        (W' ++ '.' :: F, rest) := by
      have h := span_append (fun x => x.isDigit || x == '.') (W' ++ '.' :: F) rest hbody hrestStop
      rw [List.append_assoc, List.cons_append] at h
      exact h
    cases rest with
    | nil =>
      simp only [List.append_nil] at hspan
      simp only [lex, List.append_nil, List.cons_append, hws, hw, hspan,
        Bool.false_eq_true, ↓reduceIte]
    | cons r rs =>
      obtain ⟨-, -, hre, hrE, hrf⟩ := hrest r (by simp)
      have hr : (r == 'e' || r == 'E' || r == 'f') = false := by simp [hre, hrE, hrf]
      simp only [lex, List.append_nil, List.cons_append, List.append_assoc, hws,
        hw, hspan, hr, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨d, ds, hD, hd, hdsd⟩ := toDigits_cons e.natAbs
    obtain ⟨hdm, hdp, -⟩ := digit_ne hd
    have hspan2 : List.span Char.isDigit (d :: (ds ++ rest)) = (d :: ds, rest) := by
      have h := span_append Char.isDigit (d :: ds) rest
        (fun c hc => by
          rcases List.mem_cons.1 hc with h | h
          · rw [h]; exact hd
          · exact hdsd c h) hrestDigit
      rw [List.cons_append] at h
      exact h
    have hspan : List.span (fun x => x.isDigit || x == '.')
        (W' ++ '.' :: (F ++ 'e' :: (signChars (decide (e < 0)) ++ d :: (ds ++ rest)))) =
        (W' ++ '.' :: F, 'e' :: (signChars (decide (e < 0)) ++ d :: (ds ++ rest))) := by
      have h := span_append (fun x => x.isDigit || x == '.') (W' ++ '.' :: F)
        ('e' :: (signChars (decide (e < 0)) ++ d :: (ds ++ rest))) hbody (by simp)
      rw [List.append_assoc, List.cons_append] at h
      exact h
    have hdpm : (d == '+' || d == '-') = false := by simp [hdm, hdp]
    have hmp : ('-' == '+') = false := by decide
    rw [expChars, intChars, hD]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hb : decide (e < 0)
    all_goals
      rw [hb] at hspan
      simp only [signChars, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append]
        at hspan
      simp only [signChars, lex, List.nil_append, List.cons_append, List.append_assoc, hws, hw,
        hspan, hspan2, hdpm, hmp, Bool.false_eq_true, Bool.true_or, Bool.false_or,
        beq_self_eq_true, ↓reduceIte]

/-- Lexing a printed nonnegative literal followed by a separator yields the
literal as one token (`src/Parse.jl:297`). -/
theorem lex_finiteText_ctx {q : Rat} (hq : 0 ≤ q) (fuel : Nat) (rest : List Char)
    (hrest : ∀ c ∈ rest.head?, c.isDigit = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ 'f') :
    lex (fuel + 1) ((finiteText q false).toList ++ rest) = finiteText q false :: lex fuel rest := by
  obtain ⟨W, F, e, sfx, h, hW, hWd, hFd, hsfx⟩ := finiteText_layout_nonneg hq
  rw [h, lex_layout fuel W F sfx rest e hW hWd hFd hsfx hrest, ← h, String.ofList_toList]

theorem lex_minus (fuel : Nat) (cs : List Char) :
    lex (fuel + 2) ('-' :: cs) = "-" :: lex (fuel + 1) cs := by
  rw [show ("-" : String) = String.singleton '-' by decide]
  rfl

/-- Lexing a printed negative literal yields a minus token and the magnitude. -/
theorem lex_finiteText_neg {q : Rat} (hq : Terminating q) (hneg : q < 0) (fuel : Nat)
    (rest : List Char)
    (hrest : ∀ c ∈ rest.head?, c.isDigit = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' ∧ c ≠ 'f') :
    lex (fuel + 2) ((finiteText q false).toList ++ rest) =
      "-" :: finiteText (-q) false :: lex fuel rest := by
  have hpos : 0 ≤ -q := by
    have h := Rat.neg_le_neg (Rat.le_of_lt hneg)
    rwa [Rat.neg_zero] at h
  rw [finiteText_neg hq hneg, String.toList_append, minus_toList]
  simp only [List.cons_append, List.nil_append]
  rw [lex_minus, lex_finiteText_ctx hpos fuel rest hrest]

/-! ### Witnesses -/

example : finiteText (mkRat 15 (10 ^ 1)) false = "1.5" := by decide +kernel
example : finiteText (mkRat (-25) (10 ^ 7)) false = "-2.5e-6" := by decide +kernel
example : finiteText (mkRat 1000000 (10 ^ 0)) false = "1.0e6" := by decide +kernel
example : finiteText (mkRat 123456 (10 ^ 0)) false = "123456.0" := by decide +kernel
example : finiteText (mkRat 1 (10 ^ 4)) false = "0.0001" := by decide +kernel
example : finiteText (mkRat 0 (10 ^ 3)) false = "0.0" := by decide +kernel
example : finiteText (mkRat 125 (10 ^ 2)) true = "1.25f0" := by decide +kernel
example : finiteText (mkRat 12345678901234567890123456789 (10 ^ 50)) false =
    "1.2345678901234567890123456789e-22" := by decide +kernel
example : Terminating (mkRat 12345678901234567890123456789 (10 ^ 50)) :=
  terminating_decimal _ _

end DynExpr.StringsParse
