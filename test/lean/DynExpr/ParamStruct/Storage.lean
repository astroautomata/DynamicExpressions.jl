import DynExpr.ParamStruct.General

namespace DynExpr.ParamStruct

/-- Parameter arrays have identities independent of node identities. Undefined
storage is separate from shape, src/ParametricExpression.jl:477,484. -/
abbrev MatrixStore := Heap MatrixBuffer

/-- `similar` allocates distinct storage with defined shape and undefined
values, src/ParametricExpression.jl:477. -/
def allocateParameters (h : MatrixStore) (P : JMat JF) : Addr × MatrixStore :=
  h.alloc (emptyBuffer P)

/-- Broadcast into an allocated matrix retains destination identity,
src/ParametricExpression.jl:480-493. Reading uninitialized source storage and
shape mismatches fail explicitly. -/
def copyParameters (h : MatrixStore) (dest src : Addr) : Jl MatrixStore := do
  let S ← h.read src
  let P ← readField S.values
  let D ← h.read dest
  if D.nrows != P.nrows || D.ncols != P.ncols then
    .error (.argumentError "broadcast dimensions")
  else h.write dest (filledBuffer P)

/-- Copy writes through the destination identity and preserves the distinct
source identity, including the original source buffer. -/
def ParameterStorageCopy : Prop := ∀ h h' : MatrixStore, ∀ dest src P,
  src ≠ dest → h.read src = .ok (filledBuffer P) →
  copyParameters h dest src = .ok h' →
  h'.read dest = .ok (filledBuffer P) ∧ h'.read src = .ok (filledBuffer P)

theorem parameterStorageCopy_proven : ParameterStorageCopy := by
  intro h h' dest src P hne hp hc
  unfold copyParameters at hc
  rw [hp] at hc
  simp only [jl_bind_ok, filledBuffer, readField] at hc
  cases hd : h.read dest with
  | error err => simp [hd] at hc
  | ok D =>
    simp only [hd, jl_bind_ok] at hc
    split at hc
    · cases hc
    · exact ⟨Heap.read_write_same h h' dest (filledBuffer P) hc,
        (Heap.read_write_other h h' dest src (filledBuffer P) hc hne).trans hp⟩

/-- Allocation creates a new parameter identity and keeps prior matrices
visible through their original identities. -/
def ParameterStorageFresh : Prop := ∀ h : MatrixStore, ∀ P : JMat JF, ∀ src,
  src < h.next →
  (allocateParameters h P).1 ≠ src ∧
  (allocateParameters h P).2.read src = h.read src

theorem parameterStorageFresh_proven : ParameterStorageFresh := by
  intro h P src hs
  constructor
  · change h.next ≠ src; omega
  · apply Heap.read_alloc_other
    change src ≠ h.next; omega

example : let P : JMat JF := ⟨1,1,#[.fin 2],rfl⟩
    let initial := Heap.empty.alloc (filledBuffer P)
    let dest := allocateParameters initial.2 P
    (copyParameters dest.2 dest.1 initial.1).map (fun h =>
      ((h.read initial.1).map (fun m => m.values.map (fun P => P.data)),
       (h.read dest.1).map (fun m => m.values.map (fun P => P.data)))) =
      .ok (.ok (some #[.fin 2]), .ok (some #[.fin 2])) := rfl

end DynExpr.ParamStruct
