import DynExpr.ParamStruct.Forwarding

namespace DynExpr.ParamStruct

/-- Dense arrays and views refer to scalar storage addresses. Views can reorder
or select addresses without copying, as permitted by the AbstractArray inputs
at src/ParametricExpression.jl:270,282 and src/StructuredExpression.jl:162. -/
abbrev ScalarMemory := Heap JF
abbrev ScalarView := List Addr

def readView (h : ScalarMemory) (v : ScalarView) : Jl (List JF) := v.mapM h.read

def NoOverlap (a b : ScalarView) : Prop := ∀ p ∈ a, p ∉ b

/-- `_set_constants_array!` reads the next input scalar immediately before its
write. It does not copy an overlapping input first, src/ParametricExpression.jl:252-258. -/
def setArrayView (h : ScalarMemory) : ScalarView → ScalarView → Jl ScalarMemory
  | [], _ | _, [] => .ok h
  | d :: ds, x :: xs => do
    let v ← h.read x
    let h' ← h.write d v
    setArrayView h' ds xs

/-- Structured setters copy each member slice immediately before setting that
member; later member slices read the already modified memory,
src/StructuredExpression.jl:168-175. -/
def setStructuredViews (h : ScalarMemory) : List ScalarView → ScalarView → Jl ScalarMemory
  | [], _ => .ok h
  | d :: ds, xs => do
    if xs.length < d.length then .error .boundsError
    else
      let values ← readView h (xs.take d.length)
      let h' ← writeConstants h d values
      setStructuredViews h' ds (xs.drop d.length)

/-- Allocate a fresh vector from copied scalars, as vcat does for the flattened
getter result, src/ParametricExpression.jl:266 and src/StructuredExpression.jl:156. -/
def allocateScalars (h : ScalarMemory) : List JF → ScalarView × ScalarMemory
  | [] => ([],h)
  | x :: xs =>
    let (a,h') := h.alloc x
    let (as,h'') := allocateScalars h' xs
    (a :: as,h'')

def freshScalarGetter (h : ScalarMemory) (refs : ScalarView) : Jl (ScalarView × ScalarMemory) := do
  let vs ← readView h refs
  pure (allocateScalars h vs)

private theorem allocateScalars_lower (h : ScalarMemory) (vs : List JF) :
    ∀ a ∈ (allocateScalars h vs).1, h.next ≤ a := by
  induction vs generalizing h with
  | nil => simp [allocateScalars]
  | cons v vs ih =>
    intro a ha
    simp only [allocateScalars, Heap.alloc, List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := ih (h.alloc v).2 a ha
      simp only [Heap.alloc] at this
      omega

/-- Flattened scalar getters have storage disjoint from every source address. -/
def ScalarGetterIndependent : Prop := ∀ h : ScalarMemory, ∀ refs vs,
  (∀ a ∈ refs, a < h.next) → readView h refs = .ok vs →
  NoOverlap (allocateScalars h vs).1 refs

theorem scalarGetterIndependent_proven : ScalarGetterIndependent := by
  intro h refs vs hvalid _ a ha href
  have hn := allocateScalars_lower h vs a ha
  have ho := hvalid a href
  omega

private def pairMemory : ScalarMemory :=
  ((Heap.empty.alloc (JF.fin 10)).2.alloc (JF.fin 20)).2

/-- Setter output equals the input snapshot taken before mutation. PR #274
documents the precondition that the input must not share memory with the
expression's parameters (src/NodeUtils.jl:123-124); Miles ruled the overlapping
case a documented precondition (Q47). Proved in `SafeSetters`. -/
def ParameterOverlappingInputSafe : Prop := ∀ h : ScalarMemory,
    ∀ destination input,
  destination.Nodup → input.length = destination.length →
  NoOverlap input destination →
  (∀ a ∈ destination ++ input, ∃ v, h.read a = .ok v) →
  (setArrayView h destination input).bind (fun result => readView result destination) =
    readView h input

/-- Copying member slices preserves the snapshot when the input shares no
memory with any member's parameters (documented precondition, PR #274, Q47). -/
def StructuredOverlappingInputSafe : Prop := ∀ h : ScalarMemory,
    ∀ members input,
  members.flatten.Nodup → input.length = members.flatten.length →
  NoOverlap input members.flatten →
  (∀ a ∈ members.flatten ++ input, ∃ v, h.read a = .ok v) →
  (setStructuredViews h members input).bind (fun result => readView result members.flatten) =
    readView h input

example : (∀ a ∈ ([0,1] : ScalarView), a < pairMemory.next) ∧
    readView pairMemory [0,1] = .ok [.fin 10,.fin 20] := by
  constructor
  · intro a ha; simp at ha; rcases ha with rfl | rfl <;> decide
  · rfl

private theorem allocateScalars_preserves (h : ScalarMemory) (vs : List JF)
    (a : Addr) (ha : a < h.next) :
    (allocateScalars h vs).2.read a = h.read a := by
  induction vs generalizing h with
  | nil => rfl
  | cons v vs ih =>
    change (allocateScalars (h.alloc v).2 vs).2.read a = h.read a
    have ha' : a < (h.alloc v).2.next :=
      Nat.lt_trans ha (by change h.next < h.next+1; exact Nat.lt_succ_self _)
    rw [ih (h.alloc v).2 ha']
    exact Heap.read_alloc_other h v a (Nat.ne_of_lt ha)

/-- Getter/copy/augmentation allocations preserve every original source cell. -/
def FreshArraysPreserveSources : Prop := ∀ h : ScalarMemory, ∀ vs a,
  a < h.next → (allocateScalars h vs).2.read a = h.read a

theorem freshArraysPreserveSources_proven : FreshArraysPreserveSources :=
  allocateScalars_preserves

example : 0 < ((Heap.empty : ScalarMemory).alloc (.fin 1)).2.next := by decide


end DynExpr.ParamStruct
