import DynExpr.Runtime.Errors
import Init.Data.Array.OfFn
import Init.Data.Nat.Div.Lemmas
import Init.Omega

namespace DynExpr

/-- Julia vectors used for evaluation results (src/Evaluate.jl:117-121). -/
abbrev JVec (T : Type) := Array T

namespace JVec

/-- Fill a vector with `n` copies, modelling `fill!` (src/Utils.jl:17-20). -/
def fill (n : Nat) (v : T) : JVec T := Array.replicate n v

end JVec

/-- Julia dense matrices have column-major storage; matrix and linear indexing are
used together at src/Evaluate.jl:124-128. -/
structure JMat (T : Type) where
  nrows : Nat
  ncols : Nat
  data : Array T
  size_eq : data.size = nrows * ncols

namespace JMat

private theorem offset_lt (nr nc i j : Nat)
    (hi : 1 ≤ i ∧ i ≤ nr) (hj : 1 ≤ j ∧ j ≤ nc) :
    nr * (j - 1) + (i - 1) < nr * nc := by
  have hir : i - 1 < nr := by omega
  calc
    nr * (j - 1) + (i - 1) < nr * (j - 1) + nr := Nat.add_lt_add_left hir _
    _ = nr * j := by rw [← Nat.mul_succ]; congr 1; omega
    _ ≤ nr * nc := Nat.mul_le_mul_left nr hj.2

/-- Common checked matrix access with an explicit Julia exception
(src/Evaluate.jl:127-128). -/
private def access (X : JMat T) (i j : Nat) (err : JlError) : Jl T :=
  if h : (1 ≤ i ∧ i ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols) then
    .ok (X.data[X.nrows * (j - 1) + (i - 1)]'(by
      rw [X.size_eq]
      exact offset_lt _ _ _ _ h.1 h.2))
  else .error err

/-- One-based matrix indexing, raising `BoundsError` for an invalid coordinate
(src/Evaluate.jl:113). -/
def get? (X : JMat T) (i j : Nat) : Jl T := access X i j .boundsError

/-- One-based unchecked matrix indexing; invalid `@inbounds` access is recorded
as undefined behaviour (src/Evaluate.jl:127-128). -/
def getInbounds (X : JMat T) (i j : Nat) : Jl T :=
  access X i j (.undefinedBehavior "matrix index out of bounds")

/-- One-based linear indexing of column-major storage
(src/Evaluate.jl:124-127). -/
def getLinear (X : JMat T) (i : Nat) : Jl T :=
  if h : 1 ≤ i ∧ i ≤ X.data.size then
    .ok (X.data[i - 1]'(by omega))
  else .error .boundsError

/-- Copy a feature row in column order, modelling `X[feature, :]`
(src/Evaluate.jl:113-120). -/
def row (X : JMat T) (i : Nat) : Jl (JVec T) :=
  if h : 1 ≤ i ∧ i ≤ X.nrows then
    .ok (Array.ofFn fun j : Fin X.ncols =>
      X.data[X.nrows * j.val + (i - 1)]'(by
        rw [X.size_eq]
        simpa using offset_lt X.nrows X.ncols i (j.val + 1) h
          ⟨by omega, by omega⟩))
  else .error .boundsError

/-- Construct dense column-major storage from a function of zero-based finite
row and column indices, modelling matrix storage used at src/Evaluate.jl:127-128. -/
def ofFn (nr nc : Nat) (f : Fin nr → Fin nc → T) : JMat T where
  nrows := nr
  ncols := nc
  data := Array.ofFn fun k : Fin (nr * nc) =>
    have hn : 0 < nr := Nat.pos_of_ne_zero (by
      intro hz
      have hk := k.isLt
      simp [hz] at hk)
    f ⟨k.val % nr, Nat.mod_lt _ hn⟩
      ⟨k.val / nr, (Nat.div_lt_iff_lt_mul hn).2 (by
        simp [Nat.mul_comm])⟩
  size_eq := by simp

/-- Infer the inner axis from the first list; no lists means a `0 × 0` matrix.
This supplies dense inputs for the matrix API at src/Evaluate.jl:280-284. -/
def width (xs : List (List T)) : Nat :=
  match xs with
  | [] => 0
  | x :: _ => x.length

/-- Require every inner list to have the same axis length, matching rectangular
`AbstractMatrix` inputs (src/Evaluate.jl:280-284). -/
abbrev Rectangular (xs : List (List T)) : Prop :=
  ∀ k : Fin xs.length, (xs[k.val]).length = width xs

/-- Construct from rows, rejecting ragged input. Empty input is `0 × 0`;
`r` empty rows are `r × 0` (src/Evaluate.jl:280-284). -/
def ofRows (xs : List (List T)) : Option (JMat T) :=
  if h : Rectangular xs then
    some (ofFn xs.length (width xs) fun i j =>
      (xs[i.val])[j.val]'(by
        have hi := h i
        simpa only [hi] using j.isLt))
  else none

/-- Construct from columns, rejecting ragged input. Empty input is `0 × 0`;
`c` empty columns are `0 × c` (src/Evaluate.jl:280-284). -/
def ofColumns (xs : List (List T)) : Option (JMat T) :=
  if h : Rectangular xs then
    some (ofFn (width xs) xs.length fun i j =>
      (xs[j.val])[i.val]'(by
        have hj := h j
        simpa only [hj] using i.isLt))
  else none

/-- Valid matrix coordinates always produce a value (src/Evaluate.jl:127-128). -/
theorem get?_exists (X : JMat T) (i j : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ X.nrows)
    (hj₁ : 1 ≤ j) (hj₂ : j ≤ X.ncols) :
    ∃ v, X.get? i j = .ok v := by
  have h : (1 ≤ i ∧ i ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols) :=
    ⟨⟨hi₁, hi₂⟩, ⟨hj₁, hj₂⟩⟩
  refine ⟨X.data[X.nrows * (j - 1) + (i - 1)]'(by
    rw [X.size_eq]
    exact offset_lt _ _ _ _ h.1 h.2), ?_⟩
  simp [get?, access, h]

/-- Checked and unchecked accesses agree on valid coordinates
(src/Evaluate.jl:127-128). -/
theorem getInbounds_eq_get? (X : JMat T) (i j : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ X.nrows)
    (hj₁ : 1 ≤ j) (hj₂ : j ≤ X.ncols) :
    X.getInbounds i j = X.get? i j := by
  have h : (1 ≤ i ∧ i ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols) :=
    ⟨⟨hi₁, hi₂⟩, ⟨hj₁, hj₂⟩⟩
  simp [getInbounds, get?, access, h]

/-- Every successfully copied row has one value per column
(src/Evaluate.jl:113-120). -/
theorem row_length (X : JMat T) (i : Nat) (v : JVec T)
    (h : X.row i = .ok v) : v.size = X.ncols := by
  unfold row at h
  split at h
  · cases h
    simp
  · cases h

/-- A valid feature row exists even when there are no columns
(src/Evaluate.jl:113-120). -/
theorem row_exists (X : JMat T) (i : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ X.nrows) :
    ∃ v, X.row i = .ok v ∧ v.size = X.ncols := by
  have h : 1 ≤ i ∧ i ≤ X.nrows := ⟨hi₁, hi₂⟩
  unfold row
  simp [h]

/-- Column-major construction returns the supplied element at each valid
coordinate (src/Evaluate.jl:127-128). -/
theorem get_ofFn (nr nc : Nat) (f : Fin nr → Fin nc → T) (i j : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ nr) (hj₁ : 1 ≤ j) (hj₂ : j ≤ nc) :
    (ofFn nr nc f).get? i j =
      .ok (f ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  have hir : i - 1 < nr := by omega
  have hn : 0 < nr := by omega
  have hmod : (nr * (j - 1) + (i - 1)) % nr = i - 1 := by
    simp [Nat.mod_eq_of_lt hir]
  have hdiv : (nr * (j - 1) + (i - 1)) / nr = j - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hir,
      Nat.zero_add]
  have h : (1 ≤ i ∧ i ≤ nr) ∧ (1 ≤ j ∧ j ≤ nc) :=
    ⟨⟨hi₁, hi₂⟩, ⟨hj₁, hj₂⟩⟩
  simp [get?, access, ofFn, h, hmod, hdiv]

/-- Constructing from explicit rectangular rows preserves their elements at
one-based coordinates (src/Evaluate.jl:113,280-284). -/
theorem get_ofRows (xs : List (List T)) (X : JMat T)
    (hrect : Rectangular xs) (hX : ofRows xs = some X) (i j : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ xs.length)
    (hj₁ : 1 ≤ j) (hj₂ : j ≤ width xs) :
    X.get? i j = .ok ((xs[i - 1]'(by omega))[j - 1]'(by
      have hw := hrect ⟨i - 1, by omega⟩
      dsimp at hw
      rw [hw]
      omega)) := by
  simp only [ofRows, dite_eq_left hrect] at hX
  cases hX
  exact get_ofFn _ _ _ _ _ hi₁ hi₂ hj₁ hj₂

example : (ofRows ([[1, 2, 3], [4, 5, 6]] : List (List Nat))).map
    (fun X => X.data) = some #[1, 4, 2, 5, 3, 6] := by decide

example : (ofColumns ([[1, 4], [2, 5], [3, 6]] : List (List Nat))).map
    (fun X => X.data) = some #[1, 4, 2, 5, 3, 6] := by decide

example : (ofRows ([[1], [2, 3]] : List (List Nat))).isNone = true := by decide

example : (ofRows ([[], []] : List (List Nat))).map
    (fun X => (X.nrows, X.ncols, X.data.size)) = some (2, 0, 0) := by decide

example : (ofColumns ([[], []] : List (List Nat))).map
    (fun X => (X.nrows, X.ncols, X.data.size)) = some (0, 2, 0) := by decide

example : (ofRows ([] : List (List Nat))).map
    (fun X => (X.nrows, X.ncols)) = some (0, 0) := by decide

example : JVec.fill 3 (7 : Nat) = #[7, 7, 7] := by decide

example : (ofColumns ([[1], [2, 3]] : List (List Nat))).isNone = true := by decide

example : (ofFn 2 3 (fun i j => 10 * i.val + j.val)).get? 2 3 =
    .ok 12 := by rfl

example : (ofFn 2 3 (fun i j => 10 * i.val + j.val)).getLinear 4 =
    .ok 11 := by rfl

example : (ofFn 2 3 (fun i j => 10 * i.val + j.val)).row 2 =
    .ok #[10, 11, 12] := by rfl

example : (ofFn 2 3 (fun i j => 10 * i.val + j.val)).get? 0 1 =
    .error .boundsError := by rfl

example : (ofFn 2 3 (fun i j => 10 * i.val + j.val)).getInbounds 3 1 =
    .error (.undefinedBehavior "matrix index out of bounds") := by rfl

end JMat
end DynExpr
