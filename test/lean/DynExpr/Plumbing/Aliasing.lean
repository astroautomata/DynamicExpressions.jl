import DynExpr.Plumbing.ConstantsAliases

namespace DynExpr.Plumbing

@[local simp] theorem ownershipMapOk (v : A) (f : A → B) :
    f <$> (Except.ok v : Jl A) = .ok (f v) := rfl
@[local simp] theorem ownershipMapError (e : JlError) (f : A → B) :
    f <$> (Except.error e : Jl A) = .error e := rfl
@[local simp] theorem ownershipPure (v : A) : (pure v : Jl A) = .ok v := rfl
@[local simp] theorem ownershipBindOk (v : A) (f : A → Jl B) :
    ((Except.ok v : Jl A) >>= f) = f v := rfl
@[local simp] theorem ownershipBindError (e : JlError) (f : A → Jl B) :
    ((Except.error e : Jl A) >>= f) = .error e := rfl

/-- Numeric map/filter_map arrays, src/NodeUtils.jl:102-107. Ref payloads are
projected to their borrowed node addresses; wrapper identity is modelled below. -/
inductive ConstantArray where
  | values (values : List Nat)
  | refs (nodes : List Addr)
structure ConstantArrays where
  values : Addr
  refs : Addr
  arrays : Heap ConstantArray

/-- filter_map allocates refs before map allocates values, including empty arrays. -/
def publishConstants (arrays : Heap ConstantArray) (values : List Nat) (refs : List Addr) : ConstantArrays :=
  let (ra, arrays) := arrays.alloc (.refs refs)
  let (va, arrays) := arrays.alloc (.values values)
  ⟨va, ra, arrays⟩

/-- Complete numeric getter mirror: public traversal/read control flow followed
by the two fresh array allocations, src/deprecated.jl:87-90 and NodeUtils.jl:99-107. -/
def getConstantsAllocated (g : Graph Nat) (arrays : Heap ConstantArray)
    (sharing : Bool) (fuel root : Nat) : Jl ConstantArrays := do
  let (vs,rs) ← NodeUtils.getScalarConstants g sharing fuel root
  return publishConstants arrays vs rs

/-- Julia setindex! on the returned scalar vector changes only its array heap. -/
def mutateReturnedValues (g : Graph Nat) (out : ConstantArrays) (values : List Nat) :
    Jl (Graph Nat × Heap ConstantArray) := do
  let arrays ← out.arrays.write out.values (.values values)
  return (g,arrays)

private theorem arrays_fresh (arrays : Heap ConstantArray) (vs rs) :
    (publishConstants arrays vs rs).values ≠ (publishConstants arrays vs rs).refs ∧
    arrays.next ≤ (publishConstants arrays vs rs).values ∧
    arrays.next ≤ (publishConstants arrays vs rs).refs := by
  simp [publishConstants, Heap.alloc]

private theorem array_mutation (g : Graph Nat) (arrays : Heap ConstantArray) vs rs replacement :
    ∃ arrays', mutateReturnedValues g (publishConstants arrays vs rs) replacement = .ok (g,arrays') := by
  simp [mutateReturnedValues, publishConstants, Heap.alloc, Heap.write]

/-- Success is proved from initialized finite structure and enough fuel, not
assumed. Every real getter output has distinct fresh arrays, and mutating its
numeric values vector succeeds without changing source nodes. -/
def getterArrayMutationIsolated : Prop := ∀ (g : Graph Nat) (arrays : Heap ConstantArray)
    sharing fuel root,
  NodeUtils.Traversable g fuel root → (sharing = false → Graph.NoAlias g root) →
  ∃ out, getConstantsAllocated g arrays sharing fuel root = .ok out ∧
    out.values ≠ out.refs ∧ arrays.next ≤ out.values ∧ arrays.next ≤ out.refs ∧
    ∀ replacement, ∃ arrays', mutateReturnedValues g out replacement = .ok (g,arrays')
theorem getterArrayMutationIsolated_proof : getterArrayMutationIsolated := by
  intro g arrays sharing fuel root ht hn
  obtain ⟨vs,rs,hget⟩ := NodeUtils.scalarGetterSuccess_proven Nat g sharing fuel root ht hn
  refine ⟨publishConstants arrays vs rs, ?_, ?_⟩
  · simp [getConstantsAllocated, hget, bind, Except.bind]
  · have hf := arrays_fresh arrays vs rs
    exact ⟨hf.1,hf.2.1,hf.2.2,array_mutation g arrays vs rs⟩

private theorem getter_reads_source (g : Graph T) sharing fuel root vs rs
    (h : NodeUtils.getScalarConstants g sharing fuel root = .ok (vs,rs)) :
    NodeUtils.readValues g rs = .ok vs := by
  unfold NodeUtils.getScalarConstants at h
  cases ht : NodeUtils.constantRefs g sharing fuel root [] with
  | error e => simp [ht] at h
  | ok p =>
    cases hv : NodeUtils.readValues g p.1 with
    | error e => simp [ht,hv] at h
    | ok values =>
      simp [ht,hv] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hv

/-- The numeric getter succeeds and exposes its original value objects and node
refs, including mutable Number objects. This is shallow map semantics;
mutation isolation holds for immutable scalar contents. -/
def borrowedReferenceMutation : Prop := ∀ (T : Type) (g : Graph T) sharing fuel root,
  NodeUtils.Traversable g fuel root → (sharing = false → Graph.NoAlias g root) →
  ∃ values refs, NodeUtils.getScalarConstants g sharing fuel root = .ok (values,refs) ∧
    NodeUtils.readValues g refs = .ok values
theorem borrowedReferenceMutation_proof : borrowedReferenceMutation := by
  intro T g sharing fuel root ht hn
  obtain ⟨values,refs,hget⟩ := NodeUtils.scalarGetterSuccess_proven T g sharing fuel root ht hn
  exact ⟨values,refs,hget,getter_reads_source g sharing fuel root values refs hget⟩

example : NodeUtils.Traversable
    (Heap.empty.alloc (NodeUtils.constantCell (1 : Nat))).2 1 0 ∧
    Graph.NoAlias (Heap.empty.alloc (NodeUtils.constantCell (1 : Nat))).2 0 := by
  constructor
  · exact ⟨NodeUtils.constantCell 1,rfl,rfl,by intro _ _; exact ⟨1,rfl⟩,
      by simp [NodeUtils.constantCell]⟩
  · exact Graph.noAlias_ofTree Heap.empty (.const 1)

/-- Mutable NodeIndex observations, src/NodeUtils.jl:148-200. The real public
indexer computes each value/child structure, then each occurrence is allocated
as a fresh object. Extra Cell fields are unobserved by the NodeIndex interface. -/
def indexShape : NodeUtils.NodeIndex → Tree Nat
  | .leaf v => .const v
  | .branch cs => .branch 0 (cs.map indexShape)
def indexConstantsAllocated (g : Graph Nat) (t : Tree Nat) : Addr × Graph Nat :=
  g.ofTree (indexShape (NodeUtils.indexConstants t 0).1)
def indexedObjectsFresh : Prop := ∀ g t old a,
  old < g.next →
  Graph.Reachable (indexConstantsAllocated g t).2 (indexConstantsAllocated g t).1 a →
  a ≠ old ∧ (indexConstantsAllocated g t).2.cells old = g.cells old
theorem indexedObjectsFresh_proof : indexedObjectsFresh := by
  intro g t old a ho ha
  have hf := Graph.reachable_ofTree_fresh g (indexShape (NodeUtils.indexConstants t 0).1) a ha
  exact ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le ho hf),Graph.cells_ofTree g _ old ho⟩
example : 0 < (Heap.empty.alloc (NodeUtils.constantCell (1 : Nat))).2.next := by
  simp [Heap.alloc,Heap.empty]
def indexedObjectsNoAlias : Prop := ∀ g t,
  Graph.NoAlias (indexConstantsAllocated g t).2 (indexConstantsAllocated g t).1
theorem indexedObjectsNoAlias_proof : indexedObjectsNoAlias := by
  intro g t; exact Graph.noAlias_ofTree g _

/-- Ref(node) object identities in filter_map, src/NodeUtils.jl:102-104, and
Julia ref[]=replacement. Two separate getter-created wrappers may borrow the
same node address but rebinding one must not rebind the other. -/
def rebindReference (refs : Heap Addr) (node replacement : Addr) : Jl (Heap Addr) :=
  let first := refs.alloc node
  let second := first.2.alloc node
  second.2.write first.1 replacement

private theorem reference_read (refs : Heap Addr) node replacement h
    (hw : rebindReference refs node replacement = .ok h) :
    h.read ((refs.alloc node).2.alloc node).1 = .ok node := by
  have ne : ((refs.alloc node).2.alloc node).1 ≠ (refs.alloc node).1 := by simp [Heap.alloc]
  have hr := Heap.read_write_other _ h (refs.alloc node).1
    ((refs.alloc node).2.alloc node).1 replacement hw ne
  rw [hr]
  exact Heap.read_alloc_same _ _

def referenceRebindingIsolated : Prop := ∀ (refs : Heap Addr) node replacement,
  ∃ h, rebindReference refs node replacement = .ok h ∧
    h.read ((refs.alloc node).2.alloc node).1 = .ok node ∧
    (refs.alloc node).1 ≠ ((refs.alloc node).2.alloc node).1
theorem referenceRebindingIsolated_proof : referenceRebindingIsolated := by
  intro refs node replacement
  have hs : ∃ h, rebindReference refs node replacement = .ok h := by
    simp [rebindReference,Heap.alloc,Heap.write]
  obtain ⟨h,hw⟩ := hs
  exact ⟨h,hw,reference_read refs node replacement h hw,by simp [Heap.alloc]⟩

end DynExpr.Plumbing
