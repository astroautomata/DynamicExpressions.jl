import DynExpr.ParamStruct.Mirror

namespace DynExpr.ParamStruct

/-- The constant flag takes precedence over the inactive parameter flag. -/
def ActiveTag (a : Leaf) : Nat :=
  if a.constant then 0 else if a.isParameter then 2 else 1

/-- Only the active scalar field must be initialized. Inactive fields are arbitrary. -/
def LeafActiveInitialized (a : Leaf) : Prop :=
  if a.constant then ∃ v, a.val = some v
  else if a.isParameter then True else ∃ i, a.feature = some i

/-- Cross-tag feature comparisons require two initialized, unequal fields.
Cross-tag parameter comparisons require a false right flag or unequal indices. -/
def LeafEqualitySafeDirection (a b : Leaf) : Prop :=
  ActiveTag a ≠ ActiveTag b →
    if a.constant then True
    else if a.isParameter then b.isParameter = false ∨ a.parameter ≠ b.parameter
    else ∃ i j, a.feature = some i ∧ b.feature = some j ∧ i ≠ j

def LeafEqualitySafePair (a b : Leaf) : Prop :=
  LeafEqualitySafeDirection a b ∧ LeafEqualitySafeDirection b a

/-- A tag guard prevents reading inactive fields on mismatches. -/
def guardedLeafEqual (a b : Leaf) : Jl Bool :=
  if ActiveTag a = ActiveTag b then leafEqual a b else .ok false

/-- Since PR #244 `leaf_equal` checks the leaf kind itself: on initialized
leaves it equals the tag-guarded comparator. -/
theorem guardedLeafEqual_eq_leafEqual_master (a b : Leaf)
    (ha : LeafActiveInitialized a) (hb : LeafActiveInitialized b) :
    guardedLeafEqual a b = leafEqual a b := by
  rcases a with ⟨ac, av, af, ap, ai⟩
  rcases b with ⟨bc, bv, bf, bp, bi⟩
  cases ac <;> cases bc <;> cases ap <;> cases bp <;>
    cases av <;> cases bv <;> cases af <;> cases bf <;>
    simp_all [LeafActiveInitialized, ActiveTag, guardedLeafEqual, leafEqual, readField]

/-- A safe comparison agrees with the guarded comparator on arbitrary raw leaves. -/
theorem guardedLeafEqual_eq_leafEqual (a b : Leaf)
    (ha : LeafActiveInitialized a) (hb : LeafActiveInitialized b)
    (hs : LeafEqualitySafeDirection a b) :
    guardedLeafEqual a b = leafEqual a b := by
  rcases a with ⟨ac, av, af, ap, ai⟩
  rcases b with ⟨bc, bv, bf, bp, bi⟩
  cases ac <;> cases bc <;> cases ap <;> cases bp <;>
    cases av <;> cases bv <;> cases af <;> cases bf <;>
    simp_all [LeafActiveInitialized, LeafEqualitySafeDirection, ActiveTag,
      guardedLeafEqual, leafEqual, readField]

theorem guardedLeafEqual_tagDistinct (a b : Leaf)
    (h : ActiveTag a ≠ ActiveTag b) : guardedLeafEqual a b = .ok false := by
  simp [guardedLeafEqual, h]

private theorem uint16_beq_comm (x y : UInt16) : (x == y) = (y == x) := by
  cases hxy : x == y <;> cases hyx : y == x
  · rfl
  · have h : y = x := by simpa using hyx
    subst y
    simp at hxy
  · have h : x = y := by simpa using hxy
    subst y
    simp at hyx
  · rfl

/-- Numeric NaN is unequal in both directions; symmetry does not need a no-NaN assumption. -/
theorem guardedLeafEqual_symmetric (a b : Leaf)
    (ha : LeafActiveInitialized a) (hb : LeafActiveInitialized b) :
    guardedLeafEqual a b = guardedLeafEqual b a := by
  rcases a with ⟨ac, av, af, ap, ai⟩
  rcases b with ⟨bc, bv, bf, bp, bi⟩
  cases ac <;> cases bc <;> cases ap <;> cases bp <;>
    cases av <;> cases bv <;> cases af <;> cases bf <;>
    simp_all [LeafActiveInitialized, ActiveTag, guardedLeafEqual, leafEqual,
      readField, eq_comm, Bool.and_comm, uint16_beq_comm]

theorem guardedLeafEqual_hashKey (a b : Leaf)
    (ha : LeafActiveInitialized a) (hb : LeafActiveInitialized b)
    (he : guardedLeafEqual a b = .ok true) : hashKey a = hashKey b := by
  rcases a with ⟨ac, av, af, ap, ai⟩
  rcases b with ⟨bc, bv, bf, bp, bi⟩
  cases ac <;> cases bc <;> cases ap <;> cases bp <;>
    cases av <;> cases bv <;> cases af <;> cases bf <;>
    simp_all [LeafActiveInitialized, ActiveTag, guardedLeafEqual, leafEqual,
      hashKey, readField]

theorem guardedLeafEqual_success (a b : Leaf)
    (ha : LeafActiveInitialized a) (hb : LeafActiveInitialized b) :
    ∃ equal : Bool, guardedLeafEqual a b = .ok equal := by
  rcases a with ⟨ac, av, af, ap, ai⟩
  rcases b with ⟨bc, bv, bf, bp, bi⟩
  cases ac <;> cases bc <;> cases ap <;> cases bp <;>
    cases av <;> cases bv <;> cases af <;> cases bf <;>
    simp_all [LeafActiveInitialized, ActiveTag, guardedLeafEqual, leafEqual, readField]

/-- Every safely comparable tag case succeeds and has symmetric equality,
tag distinction, and equal hash keys when equal. Constant NaNs are permitted. -/
def LeafEqualitySafeCompanion : Prop := ∀ a b : Leaf,
  LeafActiveInitialized a → LeafActiveInitialized b → LeafEqualitySafePair a b →
  (∃ equal : Bool, leafEqual a b = .ok equal) ∧
  leafEqual a b = leafEqual b a ∧
  (ActiveTag a ≠ ActiveTag b → leafEqual a b = .ok false) ∧
  (leafEqual a b = .ok true → hashKey a = hashKey b)

theorem leafEqualitySafeCompanion_proven : LeafEqualitySafeCompanion := by
  intro a b ha hb hs
  have hab := guardedLeafEqual_eq_leafEqual a b ha hb hs.1
  have hba := guardedLeafEqual_eq_leafEqual b a hb ha hs.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hab]
    exact guardedLeafEqual_success a b ha hb
  · rw [← hab, ← hba]
    exact guardedLeafEqual_symmetric a b ha hb
  · intro h
    rw [← hab]
    exact guardedLeafEqual_tagDistinct a b h
  · intro h
    exact guardedLeafEqual_hashKey a b ha hb (hab.trans h)

/-- Reflexivity needs only the active constant value to differ from NaN;
finite values and both infinities remain allowed. -/
def LeafEqualityReflexiveCompanion : Prop := ∀ a : Leaf,
  LeafActiveInitialized a → (a.constant = true → a.val ≠ some JF.nan) →
  leafEqual a a = .ok true

theorem leafEqualityReflexiveCompanion_proven : LeafEqualityReflexiveCompanion := by
  intro a ha hn
  rcases a with ⟨ac, av, af, ap, ai⟩
  cases ac <;> cases ap <;> cases av <;> cases af <;>
    simp_all [LeafActiveInitialized, leafEqual, readField]

/-- Same active tags never need a cross-tag restriction. -/
theorem leafEqualitySafePair_sameTag (a b : Leaf) (h : ActiveTag a = ActiveTag b) :
    LeafEqualitySafePair a b := by
  simp [LeafEqualitySafePair, LeafEqualitySafeDirection, h]

-- Arbitrary values and indices, including arbitrary inactive fields.
example (v w : JF) (af bf : Option UInt16) (ap bp : Bool) (ai bi : UInt16) :
    LeafActiveInitialized ⟨true, some v, af, ap, ai⟩ ∧
    LeafActiveInitialized ⟨true, some w, bf, bp, bi⟩ ∧
    LeafEqualitySafePair ⟨true, some v, af, ap, ai⟩ ⟨true, some w, bf, bp, bi⟩ := by
  simp [LeafActiveInitialized, LeafEqualitySafePair, LeafEqualitySafeDirection, ActiveTag]

example (av bv : Option JF) (i j ai bi : UInt16) :
    LeafActiveInitialized ⟨false, av, some i, false, ai⟩ ∧
    LeafActiveInitialized ⟨false, bv, some j, false, bi⟩ ∧
    LeafEqualitySafePair ⟨false, av, some i, false, ai⟩
      ⟨false, bv, some j, false, bi⟩ := by
  simp [LeafActiveInitialized, LeafEqualitySafePair, LeafEqualitySafeDirection, ActiveTag]

example (av bv : Option JF) (af bf : Option UInt16) (i j : UInt16) :
    LeafActiveInitialized ⟨false, av, af, true, i⟩ ∧
    LeafActiveInitialized ⟨false, bv, bf, true, j⟩ ∧
    LeafEqualitySafePair ⟨false, av, af, true, i⟩ ⟨false, bv, bf, true, j⟩ := by
  simp [LeafActiveInitialized, LeafEqualitySafePair, LeafEqualitySafeDirection, ActiveTag]

example (v : JF) (av : Option JF) (i j ai bi : UInt16) (h : i ≠ j) :
    LeafEqualitySafePair ⟨false, av, some i, false, ai⟩
      ⟨true, some v, some j, true, bi⟩ ∧
    leafEqual ⟨false, av, some i, false, ai⟩
      ⟨true, some v, some j, true, bi⟩ = .ok false ∧
    leafEqual ⟨true, some v, some j, true, bi⟩
      ⟨false, av, some i, false, ai⟩ = .ok false := by
  simp [LeafEqualitySafePair, LeafEqualitySafeDirection, ActiveTag, leafEqual, readField, h]

example : LeafEqualitySafePair ⟨false, none, some 1, false, 7⟩
    ⟨true, some .nan, some 2, true, 7⟩ := by
  simp [LeafEqualitySafePair, LeafEqualitySafeDirection, ActiveTag]

example (af : Option UInt16) (ap : Bool) (ai : UInt16) :
    leafEqual ⟨true, some .nan, af, ap, ai⟩ ⟨true, some .nan, af, ap, ai⟩ =
      .ok false := by
  simp [leafEqual, readField]

example (af : Option UInt16) (ap : Bool) (ai : UInt16) :
    LeafActiveInitialized ⟨true, some .posInf, af, ap, ai⟩ ∧
    ((⟨true, some .posInf, af, ap, ai⟩ : Leaf).constant = true →
      (⟨true, some .posInf, af, ap, ai⟩ : Leaf).val ≠ some JF.nan) := by
  simp [LeafActiveInitialized]

end DynExpr.ParamStruct
