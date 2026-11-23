import DynExpr.ParamStruct.ObjectSuccess
import DynExpr.ParamStruct.BoundaryCompanions
import DynExpr.ParamStruct.LeafLaws
import DynExpr.ParamStruct.SafeSetters

namespace DynExpr.ParamStruct

/-- Readonly initial-cell allocation condition, independent of any package call. -/
def AllocatedReferences (h : Heap JF) (refs : List Addr) : Prop :=
  ∀ a ∈ refs, ∃ v, h.cells a = some v

/-- Every allocated constant reference can be written for an exact-size input. -/
def ConstantWritesSucceed : Prop := ∀ h : Heap JF, ∀ refs values,
  AllocatedReferences h refs → values.length = refs.length →
  ∃ result, writeConstants h refs values = .ok result

theorem constantWritesSucceed_proven : ConstantWritesSucceed := writeConstants_exists

/-- Scalar getters succeed on every initialized reference list. -/
def ScalarGetSucceeds : Prop := ∀ s : ConstantState,
  AllocatedReferences s.heap s.refs → ∃ values, getConstants s = .ok values

theorem scalarGetSucceeds_proven : ScalarGetSucceeds := getConstants_exists

/-- Exact-size updates succeed on every initialized scalar state. -/
def ScalarSetSucceeds : Prop := ∀ s : ConstantState, ∀ values,
  AllocatedReferences s.heap s.refs →
  values.length = s.refs.length + s.params.length →
  ∃ result, setConstants s values = .ok result

theorem scalarSetSucceeds_proven : ScalarSetSucceeds := setConstants_exists

/-- Member getters succeed for arbitrary initialized member states. -/
def StructuredScalarGetSucceeds : Prop := ∀ states : List ConstantState,
  (∀ s ∈ states, AllocatedReferences s.heap s.refs) →
  ∃ groups, states.mapM getConstants = .ok groups

theorem structuredScalarGetSucceeds_proven : StructuredScalarGetSucceeds :=
  getConstants_members_exists

/-- Exact-size member updates succeed on arbitrary initialized member lists. -/
def StructuredScalarSetSucceeds : Prop := ∀ states : List ConstantState, ∀ values,
  (∀ s ∈ states, AllocatedReferences s.heap s.refs) →
  values.length = (states.map fun s => s.refs.length + s.params.length).sum →
  ∃ result, setS states values = .ok result

theorem structuredScalarSetSucceeds_proven : StructuredScalarSetSucceeds := setS_exists

/-- Nonempty valid class vectors always produce the augmented matrix. -/
def AugmentationSucceeds : Prop := ∀ P X : JMat JF, ∀ classes : List Int,
  classes.length = X.ncols → classes ≠ [] →
  (∀ c ∈ classes, 1 ≤ c ∧ c ≤ Int.ofNat P.ncols) →
  ∃ Y, augment P X classes = .ok Y

theorem augmentationSucceeds_proven : AugmentationSucceeds := augment_exists

/-- Pure parametric tree copying succeeds and preserves every active tag/value
for representable input, using the actual heap allocation mirror. -/
def ParametricNodeCopyContents : Prop := ∀ g : Graph PVal, ∀ t : PTree, ∀ fuel,
  t.Representable → t.depth ≤ fuel →
  (g.ofTree t).2.unfold fuel (g.ofTree t).1 = some t

theorem parametricNodeCopyContents_proven : ParametricNodeCopyContents := by
  intro g t fuel hr hd
  exact Graph.unfold_ofTree g t hr fuel hd

private def h : Heap JF := (Heap.empty.alloc (.fin 2)).2
private def s : ConstantState := ⟨h,[0],[.fin 3]⟩

example : AllocatedReferences h [0] := by
  intro a ha
  simp at ha
  subst a
  exact ⟨.fin 2,rfl⟩
example : ([.fin 5] : List JF).length = ([0] : List Addr).length := rfl
example : ([.fin 5,.fin 6] : List JF).length = s.refs.length + s.params.length := rfl
example : ∀ t ∈ [s], AllocatedReferences t.heap t.refs := by
  intro t ht
  simp at ht
  subst t
  intro a ha
  simp [s] at ha
  subst a
  exact ⟨.fin 2,rfl⟩
example : ([.fin 5,.fin 6] : List JF).length =
    ([s].map fun s => s.refs.length + s.params.length).sum := rfl
example : let P : JMat JF := ⟨1,1,#[.fin 2],rfl⟩
    let X : JMat JF := ⟨1,1,#[.fin 3],rfl⟩
    ([1] : List Int).length = X.ncols ∧ ([1] : List Int) ≠ [] ∧
    (∀ c ∈ ([1] : List Int), 1 ≤ c ∧ c ≤ Int.ofNat P.ncols) := by
  refine ⟨rfl,by decide,?_⟩
  intro c hc
  simp at hc
  subst c
  decide
example : let t : PTree := .const (.constant (.fin 2))
    t.Representable ∧ t.depth ≤ 1 := by simp [Tree.Representable,Tree.depth]

end DynExpr.ParamStruct
