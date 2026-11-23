import DynExpr.Arena.Traversal

namespace DynExpr.Arena


set_option maxRecDepth 2048
/-- Reading children distinguishes the nullable slot from an out-of-range slot. -/
def child_bounds : Prop := ∀ (s : Store Nat) (p : Handle) (e : Entry Nat),
  loadEntry s p.idx = .ok e →
  getChild s p 0 = .error .boundsError ∧
  (∀ k, e.children.size < k → getChild s p k = .error .boundsError) ∧
  (∀ k, 0 < k → e.children[k - 1]? = some 0 → getChild s p k = .error .undefRefError) ∧
  (∀ k j, 0 < k → e.children[k - 1]? = some j → j ≠ 0 →
    getChild s p k = .ok ⟨p.arena, j⟩)

theorem child_bounds_holds : child_bounds := by
  intro s p e he
  constructor
  · simp [getChild, he, bind, Except.bind] <;> rfl
  constructor
  · intro k hk
    have hp : k ≠ 0 := by omega
    have hw : e.children.size ≤ k - 1 := by omega
    simp [getChild, he, hp, bind, Except.bind, Array.getElem?_eq_none hw] <;> rfl
  constructor
  · intro k hk hw
    have hp : k ≠ 0 := by omega
    simp [getChild, he, hp, hw, bind, Except.bind] <;> rfl
  · intro k j hk hw hj
    have hp : k ≠ 0 := by omega
    simp [getChild, he, hp, hw, hj, bind, Except.bind, pure, Except.pure]

example : loadEntry ({ nodes := #[some ⟨1, #[0], 0, 0, 0, true⟩] } : Store Nat) 1 =
    .ok ⟨1, #[0], 0, 0, 0, true⟩ := rfl

/-- With capacity changes and appends, existing handle indices still refer to the same entries. -/
def pushes_preserve_handles : Prop := ∀ (s s' : Store Nat) (e : Entry Nat) (j : Int32),
  push s e = .ok (s', j) → ∀ i : Nat, i < s.nodes.size → s'.nodes[i]? = s.nodes[i]?

theorem pushes_preserve_handles_holds : pushes_preserve_handles := by
  intro s s' e j h i hi
  have hs : (reserve s (s.nodes.size + 1)).nodes = s.nodes := by
    unfold reserve
    split <;> rfl
  unfold push at h
  simp only [hs, bind, Except.bind] at h
  cases hj : checkedIndex ((s.nodes.push (some e)).size : Int) with
  | error err => simp only [hj, reduceCtorEq] at h
  | ok idx =>
    simp only [hj, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp [Array.getElem?_push, hi, Nat.ne_of_lt hi]

example : ∃ (s s' : Store Nat) (j : Int32), push s ⟨1, #[], 0, 0, 0, true⟩ = .ok (s', j) :=
  ⟨{}, { nodes := #[some ⟨1, #[], 0, 0, 0, true⟩], capacity := 1 }, 1, rfl⟩

/-- Scalar writes at an index are visible through aliases, preserve the compact flag,
and leave every other vector location unchanged. -/
def scalar_frame : Prop := ∀ (s : Store Nat) (p : Handle) v (e : Entry Nat),
  loadEntry s p.idx = .ok e → ∃ s',
    setField s p.idx (.val v) = .ok s' ∧
    loadEntry s' p.idx = .ok { e with val := v } ∧ s'.compact = s.compact ∧
    ∀ j, j ≠ p.idx.toInt.toNat - 1 → s'.nodes[j]? = s.nodes[j]?

theorem scalar_frame_holds : scalar_frame := by
  intro s p v e he
  have hz : p.idx ≠ 0 := by
    intro h; subst_vars; simp [loadEntry, h] at he
  have hr : rawEntry s p.idx = .ok e := by simpa [loadEntry, hz] using he
  have hp : ¬ p.idx.toInt ≤ 0 := by
    intro h; simp [rawEntry, h] at hr
  change ∃ s', setField s p.idx (.val v) = .ok s' ∧
    loadEntry s' p.idx = .ok { e with val := v } ∧ s'.compact = s.compact ∧
    ∀ j, j ≠ p.idx.toNatClampNeg - 1 → s'.nodes[j]? = s.nodes[j]?
  generalize hj : p.idx.toNatClampNeg - 1 = j at *
  have hb : j < s.nodes.size := by
    by_cases h : j < s.nodes.size
    · exact h
    · simp [rawEntry, hp, hj, Array.getElem?_eq_none (by omega : s.nodes.size ≤ j)] at hr
  refine ⟨{ s with nodes := s.nodes.set! j (some { e with val := v }) }, ?_, ?_, rfl, ?_⟩
  · simp [setField, storeEntry, he, hr, hj, bind, Except.bind, pure, Except.pure]
  · simp [loadEntry, hz, rawEntry, hp, hj, Array.set!, hb]
  · intro k hk
    simp [Array.set!, Ne.symm hk]

example : loadEntry ({ nodes := #[some ⟨3, #[], 0, 0, 0, true⟩] } : Store Nat) 1 =
    .ok ⟨3, #[], 0, 0, 0, true⟩ := rfl

/-- The documented same-arena resolver retains the original index and changes no entries. -/
def same_arena_identity : Prop := ∀ (s src : Store Nat) (p : Handle) j d,
  resolveChild 0 d s p (.arena p.arena src j) = .ok (s, j)

theorem same_arena_identity_holds : same_arena_identity := by
  intro s src p j d
  simp [resolveChild]

/-- Numeric Node's generic factory converts stored children after promotion
(`465d0ec1:src/Node.jl:407-429`, `465d0ec1:src/Utils.jl:95-97`). -/
def plainPromotedConstants (convert : Nat → Nat) (values : List Nat) : Tree Nat :=
  .branch 1 (values.map fun n => .const (convert n))

/-- A scalar tagged with the selected output type, or a different convertible
numeric type. `Nat` denotes the exact values common to the two float widths. -/
def numericChild (selected : Bool) (x : Nat) : Child Nat :=
  if selected then .plain (.const x) else .incompatible

/-- If promotion selects the requested output type, both branch constructors
should accept the same convertible constant leaves. -/
def mixed_child_type : Prop := ∀ (x y : Nat) (xSelected ySelected : Bool),
  xSelected || ySelected →
  (do let (s, p) ← branchFactory 0 2 0 1 true
        [numericChild xSelected x, numericChild ySelected y]
      toTree s p) = .ok (plainPromotedConstants id [x, y])

theorem mixed_child_type_fails : ¬ mixed_child_type := by
  intro h
  have hx := h 1 2 false true (by decide)
  have ha : branchFactory 0 2 0 1 true [numericChild false 1, numericChild true 2] =
      .error (.argumentError "ArenaNode children must have identical type parameters") := rfl
  rw [ha] at hx
  contradiction

/-- For a mutable scalar, identity names its heap allocation and magnitude
records the numeric value. -/
structure MutableInteger where
  object : Nat
  value : Nat
  deriving DecidableEq

/-- `465d0ec1:src/base.jl:501-506` calls `copy_value`, whose generic path
(`465d0ec1:src/ValueInterface.jl:77-82`) deep-copies non-isbits values. -/
def copyPlainInteger (fresh : Nat) (old : MutableInteger) : MutableInteger :=
  ⟨fresh, old.value⟩

/-- Arena copy of a constant should expose the same independent value as
Node copy (object numbers here are used only to compare source with copy). -/
def copy_mutable_value : Prop := ∀ (x : MutableInteger) (fresh : Nat), fresh ≠ x.object →
  (do let (src, i) ← defaultNode x 2
      let (dest, j) ← copyNode src 2 i
      let val := (← loadEntry dest j).val
      pure (val.object == x.object, val.value)) =
    .ok ((copyPlainInteger fresh x).object == x.object, x.value)

theorem copy_mutable_value_fails : ¬ copy_mutable_value := by
  intro h
  have hx := h ⟨0, 1⟩ 1 (by decide)
  change Except.ok (true, 1) = Except.ok (false, 1) at hx
  have hbool := congrArg Prod.fst (Except.ok.inj hx)
  cases hbool

end DynExpr.Arena
