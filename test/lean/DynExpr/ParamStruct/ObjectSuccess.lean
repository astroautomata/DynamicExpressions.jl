import DynExpr.ParamStruct.ObjectCompanions

namespace DynExpr.ParamStruct

private theorem write_exists {T : Type} (h : Heap T) (a : Addr) (value old : T)
    (ha : h.cells a = some old) : ∃ result, h.write a value = .ok result := by
  unfold Heap.write
  split
  · rename_i hn
    rw [ha] at hn
    cases hn
  · exact ⟨_,rfl⟩

/-- Copying an initialized outer array/name buffer always allocates a result.
The assumption describes the input heap cell, not the result of the copy call. -/
def NestedCopySucceeds : Prop := ∀ h : NestedMemory, ∀ src values,
  h.cells src = some values → ∃ result, copyOuterMatrix h src = .ok result

theorem nestedCopySucceeds_proven : NestedCopySucceeds := by
  intro h src values hv
  exact ⟨h.alloc values,by simp [copyOuterMatrix,Heap.read,hv]⟩

/-- In-place copying between allocated outer buffers cannot throw. -/
def NestedCopyIntoSucceeds : Prop := ∀ h : NestedMemory, ∀ src dest values old,
  h.cells src = some values → h.cells dest = some old →
  ∃ result, copyIntoCompositeMatrix h src dest = .ok result

theorem nestedCopyIntoSucceeds_proven : NestedCopyIntoSucceeds := by
  intro h src dest values old hs hd
  obtain ⟨result,hw⟩ := write_exists h dest values old hd
  exact ⟨result,by simp [copyIntoCompositeMatrix,Heap.read,hs,hw]⟩

/-- Name-vector copying succeeds for every allocated name-vector object. -/
def NameCopySucceeds : Prop := ∀ h : NameMemory, ∀ src names,
  h.cells src = some names → ∃ result, copyNames h src = .ok result

theorem nameCopySucceeds_proven : NameCopySucceeds := by
  intro h src names hs
  exact ⟨h.alloc names,by simp [copyNames,Heap.read,hs]⟩

/-- Parameter-buffer copying succeeds for allocated, initialized source storage
and a matching destination shape, src/ParametricExpression.jl:480-484. -/
def ParameterBufferCopySucceeds : Prop := ∀ h : MatrixStore, ∀ src dest P D,
  h.cells src = some (filledBuffer P) → h.cells dest = some D →
  D.nrows = P.nrows → D.ncols = P.ncols →
  ∃ result, copyParameters h dest src = .ok result

theorem parameterBufferCopySucceeds_proven : ParameterBufferCopySucceeds := by
  intro h src dest P D hs hd hr hc
  obtain ⟨result,hw⟩ := write_exists h dest (filledBuffer P) D hd
  refine ⟨result,?_⟩
  simp [copyParameters,Heap.read,hs,hd,filledBuffer,readField,hr,hc]
  exact hw

example : let h : NestedMemory := ((Heap.empty.alloc [0]).2.alloc []).2
    h.cells 0 = some [0] ∧ h.cells 1 = some [] := ⟨rfl,rfl⟩
example : let h : NameMemory := (Heap.empty.alloc ["x1"]).2
    h.cells 0 = some ["x1"] := rfl
example : let P : JMat JF := ⟨1,1,#[.fin 2],rfl⟩
    let D := emptyBuffer P
    let h : MatrixStore := ((Heap.empty.alloc (filledBuffer P)).2.alloc D).2
    h.cells 0 = some (filledBuffer P) ∧ h.cells 1 = some D ∧
    D.nrows = P.nrows ∧ D.ncols = P.ncols := ⟨rfl,rfl,rfl,rfl⟩

end DynExpr.ParamStruct
