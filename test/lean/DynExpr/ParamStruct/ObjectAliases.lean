import DynExpr.ParamStruct.ArrayAliases
import DynExpr.Model.NodeHeap

namespace DynExpr.ParamStruct

/-- Name vectors are mutable objects with immutable string elements. Copying a
vector allocates a new object; its contents may therefore be copied by value,
src/ParametricExpression.jl:216-218 and src/Expression.jl:42-52. -/
abbrev NameMemory := Heap (List String)

def copyNames (h : NameMemory) (src : Addr) : Jl (Addr × NameMemory) := do
  let ns ← h.read src
  pure (h.alloc ns)

/-- Name-vector copy cannot retain the source object identity. -/
def CopyNamesIndependent : Prop := ∀ h : NameMemory, ∀ src ns result,
  src < h.next → h.read src = .ok ns → copyNames h src = .ok result →
  result.1 ≠ src ∧ result.2.read src = .ok ns ∧ result.2.read result.1 = .ok ns

theorem copyNamesIndependent_proven : CopyNamesIndependent := by
  intro h src ns result hs hr hc
  simp [copyNames,hr] at hc
  subst result
  refine ⟨?_,?_,Heap.read_alloc_same h ns⟩
  · change h.next ≠ src; omega
  · exact (Heap.read_alloc_other h ns src (by change src ≠ h.next; omega)).trans hr

/-- Copying/allocating ordinary ParametricNode trees uses fresh node identities;
PVal records parameter tags without changing the shared graph memory API,
src/ParametricExpression.jl:126-167,216-218. -/
def parametricCopyGraph (g : Graph PVal) (t : PTree) := g.ofTree t

/-- Parametric copy has no internal sharing and all copied nodes are disjoint
from every old allocated node. This applies to alias-free source trees. -/
def ParametricNodesIndependent : Prop := ∀ g : Graph PVal, ∀ t : PTree,
  Graph.NoAlias (parametricCopyGraph g t).2 (parametricCopyGraph g t).1 ∧
  (∀ a, Graph.Reachable (parametricCopyGraph g t).2
    (parametricCopyGraph g t).1 a → g.next ≤ a) ∧
  (∀ a, a < g.next →
    (parametricCopyGraph g t).2.read a = g.read a)

theorem parametricNodesIndependent_proven : ParametricNodesIndependent := by
  intro g t
  exact ⟨Graph.noAlias_ofTree g t,Graph.reachable_ofTree_fresh g t,Graph.read_ofTree g t⟩

/-- Conversion allocates new ordinary nodes; features/parameters are not reused
as source mutable node objects, src/ParametricExpression.jl:305-331. -/
def ConvertedNodesIndependent : Prop := ∀ g : Graph JF, ∀ np t,
  Graph.NoAlias (g.ofTree (convertTree np t)).2 (g.ofTree (convertTree np t)).1 ∧
  (∀ a, Graph.Reachable (g.ofTree (convertTree np t)).2
    (g.ofTree (convertTree np t)).1 a → g.next ≤ a)

theorem convertedNodesIndependent_proven : ConvertedNodesIndependent := by
  intro g np t
  exact ⟨Graph.noAlias_ofTree g _,Graph.reachable_ofTree_fresh g _⟩

/-- Array-valued scalar objects are represented by references to inner buffers.
`copy(parameters)` only copies the outer matrix, so these inner references
survive, src/ParametricExpression.jl:216-218 and src/Expression.jl:42-52. -/
abbrev NestedMemory := Heap (List Addr)
def copyOuterMatrix (h : NestedMemory) (src : Addr) : Jl (Addr × NestedMemory) := do
  let innerRefs ← h.read src
  pure (h.alloc innerRefs)

/-- Contents of value objects such as `Vector{Float64}`: immutable scalars, so
copying one level is a complete `deepcopy`. -/
abbrev ValueMemory := Heap (List JF)

/-- `copy_value(x) = isbitstype(T) ? x : deepcopy(x)`, src/ValueInterface.jl:82.
Non-isbits values are copied into a freshly allocated object. -/
def copyValue (vm : ValueMemory) (isBits : Bool) (valueObject : Addr) :
    Jl (Addr × ValueMemory) :=
  if isBits then .ok (valueObject, vm)
  else do
    let contents ← vm.read valueObject
    pure (vm.alloc contents)

/-- Copying a constant ParametricNode allocates a new node holding
`copy_value(t.val)`, src/ParametricExpression.jl:127-129 (PRs #248, #243).
Graph Addr records node identities separately from scalar payload identities. -/
def copyCompositeConstant (g : Graph Addr) (vm : ValueMemory) (isBits : Bool)
    (valueObject : Addr) : Jl ((Addr × Graph Addr) × ValueMemory) := do
  let (v, vm') ← copyValue vm isBits valueObject
  pure (g.ofTree (.const v), vm')

/-- A freshly copied constant node owns a new VALUE object with equal contents
whenever the value type is not isbits (every mutable type), and the source
object is unchanged (fixed in PR #248; Q31). -/
def CompositeCopyIndependent : Prop := ∀ g : Graph Addr, ∀ vm : ValueMemory,
    ∀ valueObject : Addr, ∀ contents : List JF,
  vm.read valueObject = .ok contents →
  ∃ copied vm' fresh, copyCompositeConstant g vm false valueObject = .ok (copied, vm') ∧
    (copied.2.read copied.1).map (fun cell => cell.val) = .ok (some fresh) ∧
    fresh ≠ valueObject ∧ vm'.read fresh = .ok contents ∧
    vm'.read valueObject = .ok contents

theorem compositeCopy_proven : CompositeCopyIndependent := by
  intro g vm obj c hr
  have hlt : obj < vm.next := by
    cases hc : vm.cells obj with
    | none => simp [Heap.read, hc] at hr
    | some v =>
      exact Nat.lt_of_not_le (fun hle => by rw [vm.fresh obj hle] at hc; cases hc)
  refine ⟨g.ofTree (.const vm.next), (vm.alloc c).2, vm.next, ?_, ?_, Nat.ne_of_gt hlt,
    Heap.read_alloc_same vm c, ?_⟩
  · simp only [copyCompositeConstant, copyValue, Bool.false_eq_true, ↓reduceIte, hr,
      jl_bind_ok]
    rfl
  · simp [Graph.ofTree, Heap.read, Heap.alloc] <;> rfl
  · exact (Heap.read_alloc_other vm c obj (Nat.ne_of_lt hlt)).trans hr

/-- Broadcast and leaf mutation in copy_into! also copy mutable composite
references, src/ParametricExpression.jl:140-154,480-484. -/
def copyIntoCompositeMatrix (h : NestedMemory) (src dest : Addr) : Jl NestedMemory := do
  let innerRefs ← h.read src
  h.write dest innerRefs


/-- Dense numeric array/parameter copying creates disjoint scalar storage;
all existing source data remain reachable at their original addresses. -/
def NumericArrayCopyIndependent : Prop := ∀ h : ScalarMemory, ∀ source values,
  (∀ a ∈ source, a < h.next) → readView h source = .ok values →
  NoOverlap (allocateScalars h values).1 source

theorem numericArrayCopyIndependent_proven : NumericArrayCopyIndependent :=
  scalarGetterIndependent_proven

/-- Parametric augmentation uses matrix comprehensions and vcat copies before
ordinary evaluation. Its new storage cannot alias any original parameter/input
cell, src/ParametricExpression.jl:387-392. -/
def AugmentedStorageIndependent : Prop := ∀ h : ScalarMemory, ∀ source values,
  (∀ a ∈ source, a < h.next) → readView h source = .ok values →
  NoOverlap (allocateScalars h values).1 source

theorem augmentedStorageIndependent_proven : AugmentedStorageIndependent :=
  scalarGetterIndependent_proven

example : let h : NameMemory := (Heap.empty.alloc ["p1"]).2
    0 < h.next ∧ h.read 0 = .ok ["p1"] ∧
      copyNames h 0 = .ok (h.alloc ["p1"]) := by exact ⟨by decide,rfl,rfl⟩

end DynExpr.ParamStruct
