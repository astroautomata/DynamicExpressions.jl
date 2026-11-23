import DynExpr.Expressions.HeapCopy
import DynExpr.Expressions.Sampling
import DynExpr.Expressions.DeepCopy

namespace DynExpr.Expressions.Aliasing

/-- Heterogeneous NamedTuple metadata values, src/Expression.jl:32-52 on origin/master.
Array identities point into Memory; tuple fields retain keys and order. -/
inductive Value where
  | number (value : Nat)
  | array (address : Addr)
  | tuple (fields : List (String × Value))
/-- Source contents and metadata have separate mutable identity domains,
src/Expression.jl:93-96. -/
structure Expression where
  contents : Addr
  metadata : Value
/-- src/Expression.jl:216-218,267-268: these accessors return the stored object. -/
def getContents (ex : Expression) := ex.contents
/-- src/Expression.jl:234-236,35-39: array fields of the returned metadata
retain the source buffer identities. -/
def getMetadata (ex : Expression) := ex.metadata
/-- src/Expression.jl:213-215: new contents and unchanged metadata are borrowed. -/
def withContents (ex : Expression) (contents : Addr) : Expression :=
  ⟨contents, getMetadata ex⟩
/-- src/Expression.jl:231-233: new metadata and unchanged contents are borrowed. -/
def withMetadata (ex : Expression) (metadata : Value) : Expression :=
  ⟨getContents ex, metadata⟩
/-- src/Expression.jl:226-229: keyword merge copies the NamedTuple structure;
existing and newly supplied array values retain their identities. -/
def withKeywords (ex : Expression) (updates : List (String × Value)) : Jl Expression :=
  match ex.metadata with
  | .tuple fields => .ok ⟨ex.contents, .tuple (updates.foldl (fun fs kv => setField kv.1 kv.2 fs) fields)⟩
  | _ => .error (.methodError "metadata is not a NamedTuple")
@[simp] private theorem jl_error_bind {α β : Type} (e : JlError) (f : α → Jl β) :
    ((.error e : Jl α) >>= f) = .error e := rfl
@[simp] private theorem jl_ok_bind {α β : Type} (a : α) (f : α → Jl β) :
    ((.ok a : Jl α) >>= f) = f a := rfl
@[simp] private theorem jl_error_map {α β : Type} (e : JlError) (f : α → β) :
    f <$> (.error e : Jl α) = (.error e : Jl β) := rfl
@[simp] private theorem jl_ok_map {α β : Type} (a : α) (f : α → β) :
    f <$> (.ok a : Jl α) = (.ok (f a) : Jl β) := rfl
@[simp] private theorem state_bind {σ α β : Type} (m : StateT σ Jl α)
    (f : α → StateT σ Jl β) (s : σ) :
    (m >>= f) s = (m s >>= fun pair => f pair.1 pair.2) := rfl
@[simp] private theorem state_map {σ α β : Type} (m : StateT σ Jl α)
    (f : α → β) (s : σ) :
    (f <$> m) s = ((fun pair => (f pair.1, pair.2)) <$> m s) := rfl
@[simp] private theorem state_get {σ : Type} (s : σ) :
    (get : StateT σ Jl σ) s = .ok (s, s) := rfl
@[simp] private theorem state_set {σ : Type} (s s' : σ) :
    (set s' : StateT σ Jl PUnit) s = .ok (PUnit.unit, s') := rfl
@[simp] private theorem state_lift {σ α : Type} (s : σ) (m : Jl α) :
    (liftM m : StateT σ Jl α) s = ((fun a => (a, s)) <$> m) := rfl
@[simp] private theorem jl_pure {α : Type} (a : α) : (pure a : Jl α) = .ok a := rfl
@[simp] private theorem state_pure {σ α : Type} (s : σ) (a : α) :
    (pure a : StateT σ Jl α) s = .ok (a, s) := rfl

private theorem heap_write_success (heap : Heap α) (address : Addr) (before after : α)
    (h : heap.read address = .ok before) : ∃ written, heap.write address after = .ok written := by
  cases hc : heap.cells address with
  | none => simp [Heap.read, hc] at h
  | some value => simp [Heap.write, hc]

mutual
  /-- `_copy` on NamedTuple metadata values, src/Expression.jl:42-49 on
  origin/master: numbers are static and shared, NamedTuples are copied field by
  field, and arrays follow `_copy(::AbstractArray)` (`copyArray`). -/
  def copyValue : Value → StateT Memory Jl Value
    | .number n => pure (.number n)
    | .array a => do
      let memory ← get
      let result ← liftM (copyArray a memory)
      set result.2
      pure (.array result.1)
    | .tuple fields => do
      pure (.tuple (← copyFields fields))
  termination_by value => sizeOf value
  decreasing_by all_goals simp_wf <;> omega
  def copyFields : List (String × Value) → StateT Memory Jl (List (String × Value))
    | [] => pure []
    | (key, value) :: fields => do
      let value' ← copyValue value
      let fields' ← copyFields fields
      pure ((key, value') :: fields')
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf <;> omega
end
/-- `Base.copy(::Metadata)`, src/Expression.jl:50-52 and 275-277 on
origin/master. Tree copying is handled by HeapCopy; this function models the
separately copied metadata object. -/
def copyMetadata (memory : Memory) (ex : Expression) : Jl (Expression × Memory) := do
  let (metadata, memory') ← (copyValue ex.metadata).run memory
  pure (⟨ex.contents, metadata⟩, memory')

/-- Complete wrapper copy, src/Expression.jl:275-277 on origin/master: copy the
heap tree first, then recursively copy NamedTuple metadata with `_copy`. -/
def copyExpression (graph : Graph JF) (memory : Memory) (ex : Expression)
    (fuel : Nat) (preserveSharing breakSharing : Bool) :
    Jl (Expression × Graph JF × Memory) := do
  let (root, state) ← (HeapCopy.copyNode graph (preserveSharing && !breakSharing) fuel ex.contents).run (graph, [])
  let (metadata, memory') ← (copyValue ex.metadata).run memory
  pure (⟨root, metadata⟩, state.1, memory')


/-- Read an array field identity through any sequence of nested NamedTuple keys,
src/Expression.jl:35-39. -/
def arrayField : Value → List String → Option Addr
  | .array a, [] => some a
  | .tuple fields, key :: rest => do
    let (_, value) ← fields.find? (fun kv => kv.1 == key)
    arrayField value rest
  | _, _ => none
/-- Read a reference-valued array element, retaining the nested buffer identity,
src/Expression.jl:43 on origin/master. -/
def nestedArray (memory : Memory) (outer : Addr) (idx : Nat) : Option Addr := do
  let values ← memory.cells outer
  match values[idx]? with
  | some (.reference inner) => some inner
  | _ => none

/-- Specialization of src/ExpressionAlgebra.jl:15-27 to two expression
arguments: operand roots and first-operand metadata pass directly to the new
branch; there is no copy of either operand node. -/
def insertExpressions (graph : Graph JF) (op : Nat) (left right : Expression) : Expression × Graph JF :=
  let (root, graph') := graph.alloc ⟨2, false, none, 0, op, [left.contents, right.contents]⟩
  (⟨root, left.metadata⟩, graph')

/-- Numeric get_scalar_constants forwards tree getter storage,
src/Expression.jl:324-329 and src/NodeUtils.jl:99-116. Values are allocated
in a fresh vector; references contain live source node identities. -/
def getConstants (g : Graph JF) (root fuel : Nat) (preserve : Bool)
    (buffers : Heap (List JF)) : Jl (Addr × List Addr × Heap (List JF)) := do
  let nodes ← Sampling.traversal g fuel root preserve false
  let pairs ← nodes.filterMapM fun a => do
    let cell ← g.read a
    if cell.degree = 0 && cell.constant then
      match cell.val with
      | some v => pure (some (v, a))
      | none => throw .undefRefError
    else pure none
  let (values, buffers') := buffers.alloc (pairs.map Prod.fst)
  pure (values, pairs.map Prod.snd, buffers')
/-- Scalar setter forwarding keeps the node references,
src/Expression.jl:327-329 and src/NodeUtils.jl:119-140. -/
def setConstant (g : Graph JF) (reference : Addr) (value : JF) : Jl (Graph JF) := do
  let cell ← g.read reference
  g.write reference { cell with val := some value }

private def flatMemory : Memory := (Heap.empty.alloc [.number 1, .number 2]).2
private def flatExpression : Expression := ⟨7, .tuple [("names", .array 0)]⟩
private def nestedMemory : Memory :=
  let (_, m) := Heap.empty.alloc [.number 1]
  (m.alloc [.reference 0]).2
private def nestedExpression : Expression := ⟨7, .tuple [("payload", .array 1)]⟩

/-- Field-like getters expose their stored mutable identities. -/
def gettersExposureProperty : Prop :=
  ∀ (ex : Expression) (path : List String),
    getContents ex = ex.contents ∧ getMetadata ex = ex.metadata ∧
    arrayField (getMetadata ex) path = arrayField ex.metadata path
 theorem gettersExposure_proven : gettersExposureProperty := by
  intro ex path; exact ⟨rfl, rfl, rfl⟩

/-- Replacement semantics retain the untouched component's live identities. -/
def replacementsExposureProperty : Prop :=
  ∀ (ex : Expression) (root : Addr) (metadata : Value) (path : List String),
    (withContents ex root).contents = root ∧
    (withContents ex root).metadata = ex.metadata ∧
    arrayField (withContents ex root).metadata path = arrayField ex.metadata path ∧
    (withMetadata ex metadata).contents = ex.contents ∧
    (withMetadata ex metadata).metadata = metadata ∧
    arrayField (withMetadata ex metadata).metadata path = arrayField metadata path
 theorem replacementsExposure_proven : replacementsExposureProperty := by
  intro ex root metadata path; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Metadata copying detaches every allocated mutable inner array. -/
def deepMetadataCopyProperty : Prop :=
  ∀ (memory memory' : Memory) (ex out : Expression) (path : List String)
    (outer copied inner : Addr) (idx : Nat) (values : List Atom),
    arrayField ex.metadata path = some outer → memory.read inner = .ok values →
    nestedArray memory outer idx = some inner →
    copyMetadata memory ex = .ok (out, memory') →
    arrayField out.metadata path = some copied →
    nestedArray memory' copied idx ≠ some inner

private def operandGraph : Graph JF :=
  (Heap.empty.alloc (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF)).2
example : Graph.NoAlias operandGraph 0 := Graph.noAlias_ofTree Heap.empty (.const (JF.fin 1))


/-- A successful numeric-array copy allocates fresh storage and preserves the
source through arbitrary writes to the copy. -/
def flatCopyProperty : Prop :=
  ∀ (memory memory' written : Memory) (root source copied : Addr) (key : String)
    (values writes : List Nat) (out : Expression),
    memory.read source = .ok (values.map Atom.number) →
    copyMetadata memory ⟨root, .tuple [(key, .array source)]⟩ = .ok (out, memory') →
    arrayField out.metadata [key] = some copied →
    memory'.write copied (writes.map Atom.number) = .ok written →
    copied ≠ source ∧ memory'.read copied = .ok (values.map Atom.number) ∧
    written.read source = .ok (values.map Atom.number)
 theorem flatCopy_proven : flatCopyProperty := by
  intro memory memory' written root source copied key values writes out hs hc ha hw
  simp [copyMetadata, copyValue, copyFields, StateT.run, copyArray_numbers memory source values hs] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp [arrayField] at ha
  subst copied
  have fresh : memory.cells memory.next = none := Heap.alloc_fresh memory (values.map Atom.number)
  have ne : source ≠ memory.next := by
    intro eq; subst source; simp [Heap.read, fresh] at hs
  refine ⟨Ne.symm ne, Heap.read_alloc_same _ _, ?_⟩
  rw [Heap.read_write_other _ _ _ _ _ hw ne, Heap.read_alloc_other _ _ _ ne]
  exact hs

mutual
  /-- Mutable identities directly stored in recursively nested NamedTuples. -/
  def arrayIdentities : Value → List Addr
    | .number _ => []
    | .array a => [a]
    | .tuple fields => fieldIdentities fields
  termination_by value => sizeOf value
  decreasing_by all_goals simp_wf <;> omega
  def fieldIdentities : List (String × Value) → List Addr
    | [] => []
    | (_, value) :: fields => arrayIdentities value ++ fieldIdentities fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals simp_wf <;> omega
end

private theorem copyValue_array_run (a : Addr) (memory : Memory) :
    (copyValue (.array a)).run memory =
      (fun result => (Value.array result.1, result.2)) <$> copyArray a memory := by
  cases h : copyArray a memory with
  | error e => simp [copyValue, StateT.run, h]
  | ok result =>
    obtain ⟨c, m⟩ := result
    simp [copyValue, StateT.run, h]

private theorem ownedAbove_compose {first middle last : Memory}
    (head : OwnedAbove first.next middle) (frame : MemoryFrame middle last)
    (tail : OwnedAbove middle.next last) (grow : first.next ≤ middle.next) :
    OwnedAbove first.next last := by
  intro a values ha hc r hr
  by_cases low : a < middle.next
  · rw [frame.2 a low] at hc
    exact head a values ha hc r hr
  · exact Nat.le_trans grow (tail a values (Nat.le_of_not_gt low) hc r hr)

mutual
  /-- Every successful copy extends memory, returns distinct fresh array
  identities, and every array it allocates references only arrays it
  allocated. -/
  theorem copyValue_frame (value : Value) (memory memory' : Memory) (out : Value)
      (h : (copyValue value).run memory = .ok (out, memory')) :
      MemoryFrame memory memory' ∧
      (∀ a, a ∈ arrayIdentities out → memory.next ≤ a ∧ a < memory'.next) ∧
      (arrayIdentities out).Nodup ∧ OwnedAbove memory.next memory' := by
    cases hvalue : value with
    | number n =>
      rw [hvalue] at h
      simp [copyValue, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨MemoryFrame.refl _, by simp [arrayIdentities], by simp [arrayIdentities],
        ownedAbove_next _⟩
    | array source =>
      rw [hvalue, copyValue_array_run] at h
      cases hc : copyArray source memory with
      | error e => simp [hc] at h
      | ok result =>
        obtain ⟨copied, last⟩ := result
        simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨frame, low, high, owned⟩ := copyArray_frame source memory last copied hc
        refine ⟨frame, ?_, by simp [arrayIdentities], owned⟩
        intro a ha
        simp only [arrayIdentities, List.mem_singleton] at ha
        subst a
        exact ⟨low, high⟩
    | tuple fields =>
      rw [hvalue] at h
      simp only [copyValue] at h
      change ((copyFields fields).run memory >>= fun pair =>
        pure (.tuple pair.1, pair.2)) = .ok (out, memory') at h
      cases hc : (copyFields fields).run memory with
      | error e => simp [hc] at h
      | ok pair =>
        obtain ⟨fields', last⟩ := pair
        simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [arrayIdentities] using copyFields_frame fields memory last fields' hc
  termination_by sizeOf value
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
  theorem copyFields_frame (fields : List (String × Value)) (memory memory' : Memory)
      (out : List (String × Value))
      (h : (copyFields fields).run memory = .ok (out, memory')) :
      MemoryFrame memory memory' ∧
      (∀ a, a ∈ fieldIdentities out → memory.next ≤ a ∧ a < memory'.next) ∧
      (fieldIdentities out).Nodup ∧ OwnedAbove memory.next memory' := by
    cases hfields : fields with
    | nil =>
      rw [hfields] at h
      simp [copyFields, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨MemoryFrame.refl _, by simp [fieldIdentities], by simp [fieldIdentities],
        ownedAbove_next _⟩
    | cons kv fields =>
      cases hkv : kv with
      | mk key value =>
        rw [hfields, hkv] at h
        simp only [copyFields] at h
        change ((copyValue value).run memory >>= fun pair =>
          (copyFields fields).run pair.2 >>= fun tail =>
          pure ((key, pair.1) :: tail.1, tail.2)) = .ok (out, memory') at h
        cases hv : (copyValue value).run memory with
        | error e => simp [hv] at h
        | ok pair =>
          obtain ⟨value', middle⟩ := pair
          cases hf : (copyFields fields).run middle with
          | error e => simp [hv, hf] at h
          | ok pair =>
            obtain ⟨fields', last⟩ := pair
            simp [hv, hf] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hvm, hvf, hvn, hvo⟩ := copyValue_frame value memory middle value' hv
            obtain ⟨hfm, hff, hfn, hfo⟩ := copyFields_frame fields middle last fields' hf
            refine ⟨hvm.trans hfm, ?_, ?_, ownedAbove_compose hvo hfm hfo hvm.1⟩
            · intro a ha
              simp only [fieldIdentities, List.mem_append] at ha
              exact ha.elim
                (fun ha => ⟨(hvf a ha).1, Nat.lt_of_lt_of_le (hvf a ha).2 hfm.1⟩)
                (fun ha => ⟨Nat.le_trans hvm.1 (hff a ha).1, (hff a ha).2⟩)
            · simp only [fieldIdentities, List.nodup_append]
              refine ⟨hvn, hfn, ?_⟩
              intro a ha b hb eq
              subst b
              have low := (hff a hb).1
              have high := (hvf a ha).2
              exact Nat.not_lt_of_ge low high
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
end

/-- All successful recursive field copies allocate outside the complete source
address space, including repeated fields, and preserve all source cells. -/
def tupleAndRepeatedCopyProperty : Prop :=
  (∀ (memory memory' : Memory) (value out : Value),
    (copyValue value).run memory = .ok (out, memory') →
    MemoryFrame memory memory' ∧ (arrayIdentities out).Nodup ∧
      ∀ a, a ∈ arrayIdentities out → memory.cells a = none) ∧
  (∀ (memory memory' : Memory) (fields out : List (String × Value)),
    (copyFields fields).run memory = .ok (out, memory') →
    MemoryFrame memory memory' ∧ (fieldIdentities out).Nodup ∧
      ∀ a, a ∈ fieldIdentities out → memory.cells a = none)
 theorem tupleAndRepeatedCopy_proven : tupleAndRepeatedCopyProperty := by
  constructor
  · intro memory memory' value out h
    obtain ⟨frame, fresh, independent, _⟩ := copyValue_frame value memory memory' out h
    exact ⟨frame, independent, fun a ha => memory.fresh a (fresh a ha).1⟩
  · intro memory memory' fields out h
    obtain ⟨frame, fresh, independent, _⟩ := copyFields_frame fields memory memory' out h
    exact ⟨frame, independent, fun a ha => memory.fresh a (fresh a ha).1⟩

private theorem find_mem_fieldIdentities (fields : List (String × Value)) (key : String)
    (kv : String × Value) (h : fields.find? (fun kv => kv.1 == key) = some kv) (a : Addr)
    (ha : a ∈ arrayIdentities kv.2) : a ∈ fieldIdentities fields := by
  induction fields with
  | nil => simp at h
  | cons head fields ih =>
    obtain ⟨k, v⟩ := head
    by_cases hk : (k == key) = true
    · simp [List.find?, hk] at h
      subst kv
      simp [fieldIdentities, ha]
    · simp [List.find?, hk] at h
      simp [fieldIdentities, ih h]

/-- Every array reached through a field path is a stored array identity. -/
private theorem arrayField_mem : ∀ (path : List String) (value : Value) (a : Addr),
    arrayField value path = some a → a ∈ arrayIdentities value
  | [], .array b, a, h => by simp [arrayField] at h; simp [arrayIdentities, h]
  | [], .number _, _, h => by simp [arrayField] at h
  | [], .tuple _, _, h => by simp [arrayField] at h
  | _ :: _, .number _, _, h => by simp [arrayField] at h
  | _ :: _, .array _, _, h => by simp [arrayField] at h
  | key :: rest, .tuple fields, a, h => by
    cases hf : fields.find? (fun kv => kv.1 == key) with
    | none => simp [arrayField, hf] at h
    | some kv =>
      simp [arrayField, hf] at h
      simp only [arrayIdentities]
      exact find_mem_fieldIdentities fields key kv hf a (arrayField_mem rest kv.2 a h)

private theorem copyMetadata_run {memory memory' : Memory} {ex out : Expression}
    (h : copyMetadata memory ex = .ok (out, memory')) :
    (copyValue ex.metadata).run memory = .ok (out.metadata, memory') := by
  unfold copyMetadata at h
  cases hv : (copyValue ex.metadata).run memory with
  | error e => simp [hv] at h
  | ok pair =>
    obtain ⟨metadata, last⟩ := pair
    simp [hv] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Every copied array references only arrays allocated by the same copy, so no
copied array can reference a source array. -/
 theorem deepMetadataCopy_proven : deepMetadataCopyProperty := by
  intro memory memory' ex out path _ copied inner idx values _ hinner _ hcopy hpath hnested
  obtain ⟨_, bounds, _, owned⟩ := copyValue_frame _ _ _ _ (copyMetadata_run hcopy)
  have low := (bounds copied (arrayField_mem path out.metadata copied hpath)).1
  unfold nestedArray at hnested
  cases hc : memory'.cells copied with
  | none => simp [hc] at hnested
  | some vs =>
    cases hi : vs[idx]? with
    | none => simp [hc, hi] at hnested
    | some atom =>
      cases atom with
      | number n => simp [hc, hi] at hnested
      | reference r =>
        simp [hc, hi] at hnested
        rw [hnested] at hi
        have high := owned copied vs low hc inner (List.mem_iff_getElem?.mpr ⟨idx, hi⟩)
        exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (heap_read_lt hinner) high)

example : arrayField nestedExpression.metadata ["payload"] = some 1 ∧
    nestedMemory.read 0 = .ok [.number 1] ∧ nestedArray nestedMemory 1 0 = some 0 ∧
    (copyMetadata nestedMemory nestedExpression).toOption.map
      (fun result => (arrayField result.1.metadata ["payload"], nestedArray result.2 2 0)) =
      some (some 2, some 3) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [copyMetadata, copyValue, copyFields, nestedExpression]
  rfl

/-- Keyword merge retains the supplied live values for arbitrary field lists. -/
def keywordAliasProperty : Prop :=
  ∀ (root : Addr) (fields updates : List (String × Value)) (query : String),
    (withKeywords ⟨root, .tuple fields⟩ updates).toOption.map Expression.contents = some root ∧
    (withKeywords ⟨root, .tuple fields⟩ updates).toOption.bind (fun out =>
      match out.metadata with
      | .tuple merged => fieldValue query merged
      | _ => none) =
        updates.foldl (fun current kv => if kv.1 = query then some kv.2 else current)
          (fieldValue query fields)
 theorem keywordAlias_proven : keywordAliasProperty := by
  intro root fields updates query
  constructor
  · rfl
  · change fieldValue query (mergeMetadata (⟨fields⟩ : Metadata Value) ⟨updates⟩).data = _
    exact keywordMerge_proven Value ⟨fields⟩ ⟨updates⟩ query


/-- The getter's per-node numeric selection, src/NodeUtils.jl:99-116. -/
def constantEntry (g : Graph JF) (a : Addr) : Jl (Option (JF × Addr)) := do
  let cell ← g.read a
  if cell.degree = 0 && cell.constant then
    match cell.val with
    | some value => pure (some (value, a))
    | none => throw .undefRefError
  else pure none
/-- A returned scalar pair contains an allocated constant's live identity. -/
def LiveConstant (g : Graph JF) (pair : JF × Addr) : Prop :=
  ∃ cell, g.read pair.2 = .ok cell ∧ cell.degree = 0 ∧
    cell.constant = true ∧ cell.val = some pair.1
private theorem constantEntry_live (g : Graph JF) (a : Addr) (pair : JF × Addr)
    (h : constantEntry g a = .ok (some pair)) : LiveConstant g pair := by
  unfold constantEntry at h
  cases hr : g.read a with
  | error e => simp [hr] at h
  | ok cell =>
    simp only [hr, jl_ok_bind] at h
    split at h
    · rename_i selected
      cases hv : cell.val with
      | none => simp [hv] at h
      | some value =>
        simp [hv] at h
        subst pair
        simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
        exact ⟨cell, hr, selected.1, selected.2, hv⟩
    · simp at h

private theorem filterMap_live_loop (g : Graph JF) (nodes : List Addr)
    (acc out : List (JF × Addr))
    (ha : ∀ pair, pair ∈ acc → LiveConstant g pair)
    (h : List.filterMapM.loop (constantEntry g) nodes acc = .ok out) :
    ∀ pair, pair ∈ out → LiveConstant g pair := by
  induction nodes generalizing acc out with
  | nil =>
    simp [List.filterMapM.loop] at h
    subst out
    intro pair hp
    exact ha pair (by simpa using hp)
  | cons a nodes ih =>
    simp only [List.filterMapM.loop] at h
    cases hs : constantEntry g a with
    | error e => simp [hs] at h
    | ok value =>
      cases value with
      | none =>
        simp only [hs, jl_ok_bind] at h
        exact ih acc out ha h
      | some entry =>
        simp only [hs, jl_ok_bind] at h
        apply ih (entry :: acc) out _ h
        intro pair hp
        simp only [List.mem_cons] at hp
        exact hp.elim (fun eq => eq ▸ constantEntry_live g a entry hs) (ha pair)

private theorem filterMap_live (g : Graph JF) (nodes : List Addr) (pairs : List (JF × Addr))
    (h : nodes.filterMapM (constantEntry g) = .ok pairs) :
    ∀ pair, pair ∈ pairs → LiveConstant g pair :=
  filterMap_live_loop g nodes [] pairs (by simp) h


 theorem getConstants_result (g : Graph JF) (root fuel : Nat) (preserve : Bool)
    (buffers buffers' : Heap (List JF)) (address : Addr) (refs : List Addr)
    (h : getConstants g root fuel preserve buffers = .ok (address, refs, buffers')) :
    ∃ nodes pairs, Sampling.traversal g fuel root preserve false = .ok nodes ∧
      nodes.filterMapM (constantEntry g) = .ok pairs ∧
      address = buffers.next ∧ refs = pairs.map Prod.snd ∧
      buffers' = (buffers.alloc (pairs.map Prod.fst)).2 := by
  change (Sampling.traversal g fuel root preserve false >>= fun nodes =>
    nodes.filterMapM (constantEntry g) >>= fun pairs =>
    pure (buffers.next, pairs.map Prod.snd, (buffers.alloc (pairs.map Prod.fst)).2)) =
      .ok (address, refs, buffers') at h
  cases ht : Sampling.traversal g fuel root preserve false with
  | error e => simp [ht] at h
  | ok nodes =>
    cases hp : nodes.filterMapM (constantEntry g) with
    | error e => simp [ht, hp] at h
    | ok pairs =>
      simp [ht, hp] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨nodes, pairs, rfl, hp, rfl, rfl, rfl⟩

/-- Returned reference identities are the selected source identities. Setting
any allocated reference writes the original node through that same identity. -/
def constantsAliasProperty : Prop :=
  (∀ (g : Graph JF) (root fuel : Nat) (preserve : Bool)
    (buffers buffers' : Heap (List JF)) (address : Addr) (refs : List Addr),
    getConstants g root fuel preserve buffers = .ok (address, refs, buffers') →
    ∃ nodes pairs, Sampling.traversal g fuel root preserve false = .ok nodes ∧
      nodes.filterMapM (constantEntry g) = .ok pairs ∧
      refs = pairs.map Prod.snd ∧ buffers'.read address = .ok (pairs.map Prod.fst) ∧
      ∀ pair, pair ∈ pairs → LiveConstant g pair) ∧
  (∀ (g : Graph JF) (reference : Addr) (cell : Cell JF) (value : JF),
    g.read reference = .ok cell → ∃ g', setConstant g reference value = .ok g' ∧
      g'.read reference = .ok { cell with val := some value })
 theorem constantsAlias_proven : constantsAliasProperty := by
  constructor
  · intro g root fuel preserve buffers buffers' address refs h
    obtain ⟨nodes, pairs, ht, hp, rfl, hr, rfl⟩ :=
      getConstants_result g root fuel preserve buffers buffers' address refs h
    exact ⟨nodes, pairs, ht, hp, hr, Heap.read_alloc_same _ _, filterMap_live g nodes pairs hp⟩
  · intro g reference cell value hr
    obtain ⟨g', hw⟩ := heap_write_success g reference cell {cell with val := some value} hr
    exact ⟨g', by simp [setConstant, hr, hw], Heap.read_write_same _ _ _ _ hw⟩

example : getConstants operandGraph 0 1 false (Heap.empty : Heap (List JF)) =
    .ok (0, [0], (Heap.empty.alloc [.fin 1]).2) := rfl
example : operandGraph.read 0 = .ok (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF) ∧
    setConstant operandGraph 0 (.fin 9) =
      operandGraph.write 0 ⟨0, true, some (.fin 9), 0, 0, []⟩ := ⟨rfl, rfl⟩


/-- Declared expression operations borrow operand roots and first-operand
metadata while allocating only the new branch root. -/
def operandBorrowingProperty : Prop := ∀ (g : Graph JF) (left right : Expression) op,
  let out := insertExpressions g op left right
  (out.2.cells out.1.contents).map Cell.children = some [left.contents, right.contents] ∧
  out.1.metadata = left.metadata ∧ out.1.contents = g.next
 theorem operandBorrowing_proven : operandBorrowingProperty := by
  intro g left right op
  simp [insertExpressions, Heap.alloc]

/-- Every successful scalar getter allocates a fresh vector. Writes to that
vector preserve every allocated caller buffer. -/
def scalarVectorIsolationProperty : Prop :=
  ∀ (g : Graph JF) (root fuel : Nat) (preserve : Bool)
    (buffers buffers' written : Heap (List JF)) (address source : Addr)
    (refs : List Addr) (values writes : List JF),
    getConstants g root fuel preserve buffers = .ok (address, refs, buffers') →
    buffers.read source = .ok values → buffers'.write address writes = .ok written →
    buffers.cells address = none ∧ address ≠ source ∧
    buffers'.read source = .ok values ∧ written.read source = .ok values
 theorem scalarVectorIsolation_proven : scalarVectorIsolationProperty := by
  intro g root fuel preserve buffers buffers' written address source refs values writes hg hs hw
  obtain ⟨nodes, pairs, ht, hp, rfl, hr, rfl⟩ :=
    getConstants_result g root fuel preserve buffers buffers' address refs hg
  have fresh : buffers.cells buffers.next = none := Heap.alloc_fresh buffers (pairs.map Prod.fst)
  have ne : source ≠ buffers.next := by
    intro eq; subst source; simp [Heap.read, fresh] at hs
  refine ⟨fresh, Ne.symm ne, ?_, ?_⟩
  · rw [Heap.read_alloc_other _ _ _ ne]; exact hs
  · rw [Heap.read_write_other _ _ _ _ _ hw ne, Heap.read_alloc_other _ _ _ ne]; exact hs

example : getConstants operandGraph 0 1 false (Heap.empty.alloc [.fin 42]).2 =
    .ok (1, [0], ((Heap.empty.alloc [.fin 42]).2.alloc [.fin 1]).2) := rfl


/-- Julia dictionaries stored as metadata fields. A Dict is never static, so
`_copy(x) = _is_static(x) ? x : deepcopy(x)` (src/Expression.jl:42 and
src/Utils.jl:32-55 on origin/master) deep-copies it:
`deepcopy_internal(::Dict)`, Julia base/deepcopy.jl:144-159, copies every
value in iteration order with one identity dictionary for the whole call
(`isbitstype(eltype(x))` is false because keys are Strings). Keys are immutable
strings, modelled by value. Reference-valued entries point to arrays in
`memory`; array atoms cannot reference dictionaries, so allocating the
destination Dict (`dest = empty(x)`) after its values is unobservable. -/
abbrev DictionaryMemory := Heap (List (String × Atom))
def copyDictionaryField (dictionaries : DictionaryMemory) (memory : Memory) (root : Addr) :
    Jl (Addr × DictionaryMemory × Memory) :=
  match dictionaries.read root with
  | .error e => .error e
  | .ok entries =>
    match copyAtomsWith (deepCopyArray (memory.next + 1)) (entries.map Prod.snd) (memory, []) with
    | .error e => .error e
    | .ok (values, state) =>
      .ok ((dictionaries.alloc ((entries.map Prod.fst).zip values)).1,
        (dictionaries.alloc ((entries.map Prod.fst).zip values)).2, state.1)
example :
    let dictionaries : DictionaryMemory := (Heap.empty.alloc [("weights", Atom.reference 0)]).2
    let memory : Memory := (Heap.empty.alloc [.number 1, .number 2]).2
    (copyDictionaryField dictionaries memory 0).toOption.map
      (fun result => (result.2.1.cells result.1, result.2.2.cells 1)) =
      some (some [("weights", Atom.reference 1)], some [.number 1, .number 2]) := rfl


/-- A sampler with one eligible object returns that exact live identity.
There is no node copy, even when its traversal breaks sharing. -/
def samplerBorrowProperty : Prop := ∀ (s : Sampling.NodeSampler JF) (rng : Sampling.RNG) a,
  Sampling.matching s = .ok [a] → s.weighting = none →
  (Sampling.rand s rng).1 = .ok a
 theorem samplerBorrow_proven : samplerBorrowProperty := by
  intro s rng a hm hw
  simp [Sampling.rand, hm, hw, Sampling.getNode]
example : Sampling.matching (⟨operandGraph, 0, 1, fun _ => true, none, false, false⟩ : Sampling.NodeSampler JF) =
  .ok [0] := rfl


/-- Heap-node copying only extends its allocation state. -/
def GraphFrame (before after : Graph JF) : Prop :=
  before.next ≤ after.next ∧ ∀ a, a < before.next → after.cells a = before.cells a
private theorem graphFrame_refl (g : Graph JF) : GraphFrame g g :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩
private theorem graphFrame_trans {g h k : Graph JF}
    (gh : GraphFrame g h) (hk : GraphFrame h k) : GraphFrame g k :=
  ⟨Nat.le_trans gh.1 hk.1, fun a ha => (hk.2 a (Nat.lt_of_lt_of_le ha gh.1)).trans (gh.2 a ha)⟩
private theorem graphFrame_alloc (g : Graph JF) (cell : Cell JF) :
    GraphFrame g (g.alloc cell).2 := by
  refine ⟨by simp [Heap.alloc], ?_⟩
  intro a ha; simp [Heap.alloc, Nat.ne_of_lt ha]

/-- Every cached result was allocated beyond the original source address space. -/
def CopyInvariant (floor : Nat) (state : HeapCopy.CopyState) : Prop :=
  floor ≤ state.1.next ∧ ∀ pair, pair ∈ state.2 → floor ≤ pair.2

private theorem find_member (p : α → Bool) (xs : List α) (x : α)
    (h : xs.find? p = some x) : x ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    cases hp : p a <;> simp [List.find?, hp] at h
    · exact List.mem_cons_of_mem a (ih h)
    · subst x; exact List.mem_cons_self

private theorem mapCopy_frame_loop (f : Addr → StateT HeapCopy.CopyState Jl Addr)
    (floor : Nat)
    (step : ∀ a initial copied final, CopyInvariant floor initial →
      (f a).run initial = .ok (copied, final) →
      GraphFrame initial.1 final.1 ∧ CopyInvariant floor final)
    (xs acc : List Addr) (initial final : HeapCopy.CopyState) (out : List Addr)
    (hi : CopyInvariant floor initial)
    (h : (List.mapM.loop f xs acc).run initial = .ok (out, final)) :
    GraphFrame initial.1 final.1 ∧ CopyInvariant floor final := by
  induction xs generalizing acc initial final out with
  | nil =>
    simp [List.mapM.loop, StateT.run] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨graphFrame_refl _, hi⟩
  | cons a xs ih =>
    simp only [List.mapM.loop] at h
    change ((f a).run initial >>= fun pair =>
      (List.mapM.loop f xs (pair.1 :: acc)).run pair.2) = .ok (out, final) at h
    cases hs : (f a).run initial with
    | error e => simp [hs] at h
    | ok pair =>
      obtain ⟨copied, middle⟩ := pair
      simp only [hs, jl_ok_bind] at h
      obtain ⟨frame, hm⟩ := step a initial copied middle hi hs
      obtain ⟨rest, hf⟩ := ih (copied :: acc) middle final out hm h
      exact ⟨graphFrame_trans frame rest, hf⟩

 theorem copyNode_frame (source : Graph JF) (cache : Bool) (fuel root : Nat)
    (floor : Nat) (initial final : HeapCopy.CopyState) (out : Addr)
    (hi : CopyInvariant floor initial)
    (h : (HeapCopy.copyNode source cache fuel root).run initial = .ok (out, final)) :
    GraphFrame initial.1 final.1 ∧ CopyInvariant floor final ∧ floor ≤ out := by
  induction fuel generalizing root initial final out with
  | zero => cases h
  | succ fuel ih =>
    simp only [HeapCopy.copyNode] at h
    cases hc : (if cache then (initial.2.find? (fun kv => kv.1 == root)).map Prod.snd else none) with
    | some copied =>
      simp [StateT.run, hc] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨graphFrame_refl _, hi, ?_⟩
      cases cache with
      | false => simp at hc
      | true =>
        cases hf : initial.2.find? (fun kv => kv.1 == root) with
        | none => simp [hf] at hc
        | some pair =>
          simp [hf] at hc
          subst copied
          exact hi.2 pair (find_member _ _ _ hf)
    | none =>
      simp only [StateT.run, state_bind, state_get, jl_ok_bind, hc, state_lift,
        state_set, state_pure] at h
      cases hr : source.read root with
      | error e => simp [hr] at h
      | ok cell =>
        simp only [hr, jl_ok_map, jl_ok_bind] at h
        cases hm : (cell.children.mapM (HeapCopy.copyNode source cache fuel)).run initial with
        | error e =>
          have hm' : cell.children.mapM (HeapCopy.copyNode source cache fuel) initial = .error e := hm
          simp [hm'] at h
        | ok pair =>
          obtain ⟨children, middle⟩ := pair
          have hm' : cell.children.mapM (HeapCopy.copyNode source cache fuel) initial = .ok (children, middle) := hm
          simp [hm'] at h
          obtain ⟨rfl, rfl⟩ := h
          have step : ∀ a initial copied final, CopyInvariant floor initial →
              (HeapCopy.copyNode source cache fuel a).run initial = .ok (copied, final) →
              GraphFrame initial.1 final.1 ∧ CopyInvariant floor final := by
            intro a initial copied final hinit hrun
            exact ⟨(ih a initial final copied hinit hrun).1,
              (ih a initial final copied hinit hrun).2.1⟩
          have hmLoop : (List.mapM.loop (HeapCopy.copyNode source cache fuel) cell.children []).run initial =
              .ok (children, middle) := hm
          obtain ⟨frame, fresh⟩ := mapCopy_frame_loop _ floor step cell.children [] initial middle children hi hmLoop
          refine ⟨graphFrame_trans frame (graphFrame_alloc _ _), ?_, fresh.1⟩
          refine ⟨Nat.le_trans fresh.1 (by simp [Heap.alloc]), ?_⟩
          intro pair hp
          simp only [List.mem_cons] at hp
          exact hp.elim (fun eq => by subst pair; exact fresh.1) (fresh.2 pair)

/-- Every successful full copy allocates a fresh root and recursive metadata
arrays while preserving all source node and metadata cells. -/
def fullCopyIsolationProperty : Prop :=
  ∀ (graph graph' : Graph JF) (memory memory' : Memory) (ex out : Expression)
    (fuel : Nat) (preserve breakSharing : Bool),
    copyExpression graph memory ex fuel preserve breakSharing = .ok (out, graph', memory') →
    graph.cells out.contents = none ∧ GraphFrame graph graph' ∧
    MemoryFrame memory memory' ∧
    ∀ a, a ∈ arrayIdentities out.metadata → memory.cells a = none
 theorem fullCopyIsolation_proven : fullCopyIsolationProperty := by
  intro graph graph' memory memory' ex out fuel preserve breakSharing h
  unfold copyExpression at h
  cases hc : (HeapCopy.copyNode graph (preserve && !breakSharing) fuel ex.contents).run (graph, []) with
  | error e => simp [hc] at h
  | ok pair =>
    obtain ⟨root, state⟩ := pair
    cases hv : (copyValue ex.metadata).run memory with
    | error e => simp [hc, hv] at h
    | ok pair =>
      obtain ⟨metadata, after⟩ := pair
      simp [hc, hv] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hi : CopyInvariant graph.next (graph, []) := ⟨Nat.le_refl _, by simp⟩
      obtain ⟨frame, _, fresh⟩ := copyNode_frame graph _ fuel ex.contents graph.next (graph, []) state root hi hc
      obtain ⟨metadataFrame, metadataFresh, _⟩ := copyValue_frame ex.metadata memory after metadata hv
      exact ⟨graph.fresh root fresh, frame, metadataFrame,
        fun a ha => memory.fresh a (metadataFresh a ha).1⟩

example : (copyValue (.array 0)).run flatMemory =
    .ok (.array 1, (flatMemory.alloc [.number 1, .number 2]).2) := by
  simp only [copyValue]; rfl
example : (copyFields [("a", .array 0), ("b", .array 0)]).run flatMemory =
    .ok ([("a", .array 1), ("b", .array 2)],
      ((flatMemory.alloc [.number 1, .number 2]).2.alloc [.number 1, .number 2]).2) := by
  simp only [copyValue, copyFields]; rfl
example : copyExpression operandGraph flatMemory ⟨0, flatExpression.metadata⟩ 1 false false =
    .ok (⟨1, .tuple [("names", .array 1)]⟩,
      (operandGraph.alloc ⟨0, true, some (.fin 1), 0, 0, []⟩).2,
      (flatMemory.alloc [.number 1, .number 2]).2) := by
  simp only [copyExpression, copyValue, copyFields, flatExpression]; rfl
example : ∃ (memory' written : Memory) (out : Expression),
    flatMemory.read 0 = .ok ([1, 2].map Atom.number) ∧
    copyMetadata flatMemory ⟨7, .tuple [("names", .array 0)]⟩ = .ok (out, memory') ∧
    arrayField out.metadata ["names"] = some 1 ∧
    memory'.write 1 ([9].map Atom.number) = .ok written := by
  let memory' := (flatMemory.alloc [.number 1, .number 2]).2
  have hw : ∃ written, memory'.write 1 ([9].map Atom.number) = .ok written := by
    simp [memory', Heap.write, Heap.alloc, Heap.empty, flatMemory]
  obtain ⟨written, hw⟩ := hw
  refine ⟨memory', written, ⟨7, .tuple [("names", .array 1)]⟩, rfl, ?_, rfl, hw⟩
  simp only [copyMetadata, copyValue, copyFields]; rfl
example : ∃ (buffers' written : Heap (List JF)),
    getConstants operandGraph 0 1 false (Heap.empty.alloc [.fin 42]).2 = .ok (1, [0], buffers') ∧
    (Heap.empty.alloc [JF.fin 42]).2.read 0 = .ok [JF.fin 42] ∧
    buffers'.write 1 [.fin 9] = .ok written := by
  let buffers' := ((Heap.empty.alloc [JF.fin 42]).2.alloc [JF.fin 1]).2
  have hw : ∃ written, buffers'.write 1 [JF.fin 9] = .ok written := by
    simp [buffers', Heap.write, Heap.alloc, Heap.empty]
  obtain ⟨written, hw⟩ := hw
  exact ⟨buffers', written, rfl, rfl, hw⟩


/-- Source paths remain unchanged when allocating an unrelated fresh branch. -/
private theorem path_before_alloc (g : Graph JF) (cell : Cell JF) (source start : Addr)
    (allocated : ∀ a, Graph.Reachable g source a → a < g.next)
    (reach : Graph.Reachable g source start) {path : List Nat} {target : Addr}
    (h : Graph.Path (g.alloc cell).2 start path target) : Graph.Path g start path target := by
  induction h with
  | nil => exact .nil _
  | @cons a b z i p c hc hi hp ih =>
    have ne : a ≠ g.next := Nat.ne_of_lt (allocated a reach)
    have hcOld : g.cells a = some c := by simpa [Heap.alloc, ne] using hc
    have childReach : Graph.Reachable g source b := by
      obtain ⟨initialPath, hprefix⟩ := reach
      exact ⟨initialPath ++ [i], Graph.Path.append hprefix (.cons hcOld hi (.nil b))⟩
    exact .cons hcOld hi (ih childReach)

private theorem inserted_path (g : Graph JF) (left right : Expression) (op : Nat)
    (al : ∀ a, Graph.Reachable g left.contents a → a < g.next)
    (ar : ∀ a, Graph.Reachable g right.contents a → a < g.next)
    {path : List Nat} {a : Addr}
    (h : Graph.Path (insertExpressions g op left right).2 g.next path a) :
    (path = [] ∧ a = g.next) ∨
    (∃ tail, path = 0 :: tail ∧ Graph.Path g left.contents tail a) ∨
    (∃ tail, path = 1 :: tail ∧ Graph.Path g right.contents tail a) := by
  cases h with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | @cons start b z i p c hc hi hp =>
    have same : c = ⟨2, false, none, 0, op, [left.contents, right.contents]⟩ := by
      simpa [insertExpressions, Heap.alloc] using hc.symm
    subst c
    cases i with
    | zero =>
      simp at hi
      subst b
      exact Or.inr (Or.inl ⟨p, rfl, path_before_alloc g _ left.contents left.contents al
        ⟨[], .nil _⟩ hp⟩)
    | succ i =>
      cases i with
      | zero =>
        simp at hi
        subst b
        exact Or.inr (Or.inr ⟨p, rfl, path_before_alloc g _ right.contents right.contents ar
          ⟨[], .nil _⟩ hp⟩)
      | succ i => simp at hi

/-- Disjoint unaliased operand trees remain unaliased under binary insertion. -/
def operatorDisjointNoAliasProperty : Prop :=
  ∀ (g : Graph JF) (left right : Expression) (op : Nat),
    Graph.NoAlias g left.contents → Graph.NoAlias g right.contents →
    (∀ a, Graph.Reachable g left.contents a → a < g.next) →
    (∀ a, Graph.Reachable g right.contents a → a < g.next) →
    (∀ a, Graph.Reachable g left.contents a → ¬ Graph.Reachable g right.contents a) →
    1 ≤ op → op ≤ 255 →
    Graph.NoAlias (insertExpressions g op left right).2 (insertExpressions g op left right).1.contents
 theorem operatorDisjointNoAlias_proven : operatorDisjointNoAliasProperty := by
  intro g left right op hl hr al ar disjoint _ _ p q a hp hq
  change Graph.Path (insertExpressions g op left right).2 g.next p a at hp
  change Graph.Path (insertExpressions g op left right).2 g.next q a at hq
  rcases inserted_path g left right op al ar hp with ⟨rfl, rfl⟩ | ⟨p, rfl, hpl⟩ | ⟨p, rfl, hpr⟩ <;>
    rcases inserted_path g left right op al ar hq with ⟨rfl, he⟩ | ⟨q, rfl, hql⟩ | ⟨q, rfl, hqr⟩
  · rfl
  · exact False.elim (Nat.lt_irrefl _ (al g.next ⟨q, hql⟩))
  · exact False.elim (Nat.lt_irrefl _ (ar g.next ⟨q, hqr⟩))
  · subst a; exact False.elim (Nat.lt_irrefl _ (al g.next ⟨p, hpl⟩))
  · exact congrArg (List.cons 0) (hl p q a hpl hql)
  · exact False.elim (disjoint a ⟨p, hpl⟩ ⟨q, hqr⟩)
  · subst a; exact False.elim (Nat.lt_irrefl _ (ar g.next ⟨p, hpr⟩))
  · exact False.elim (disjoint a ⟨q, hql⟩ ⟨p, hpr⟩)
  · exact congrArg (List.cons 1) (hr p q a hpr hqr)


/-- Safe metadata arrays contain only immutable numeric elements. -/
def FlatArrays (memory : Memory) (identities : List Addr) : Prop :=
  ∀ a, a ∈ identities → ∃ values : List Nat, memory.read a = .ok (values.map Atom.number)

private theorem flatArrays_frame (before after : Memory) (ids : List Addr)
    (frame : MemoryFrame before after) (bounds : ∀ a, a ∈ ids → a < before.next)
    (flat : FlatArrays before ids) : FlatArrays after ids := by
  intro a ha
  obtain ⟨values, hr⟩ := flat a ha
  refine ⟨values, ?_⟩
  unfold Heap.read at hr ⊢
  rw [frame.2 a (bounds a ha)]
  exact hr

theorem flat_reachable {memory : Memory} {ids : List Addr} (flat : FlatArrays memory ids) :
    ReachableArraysAllocated memory ids := by
  intro root hroot a reach
  obtain ⟨values, h⟩ := flat root hroot
  rw [reach_flat h reach]
  exact ⟨_, h⟩

mutual
  theorem copyValue_flat (value : Value) (memory memory' : Memory) (out : Value)
      (flat : FlatArrays memory (arrayIdentities value))
      (h : (copyValue value).run memory = .ok (out, memory')) :
      FlatArrays memory' (arrayIdentities out) := by
    cases hvalue : value with
    | number n =>
      rw [hvalue] at h
      simp [copyValue, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [FlatArrays, arrayIdentities]
    | array source =>
      obtain ⟨values, hr⟩ := flat source (by simp [hvalue, arrayIdentities])
      rw [hvalue, copyValue_array_run, copyArray_numbers memory source values hr] at h
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      intro a ha
      simp only [arrayIdentities, List.mem_singleton] at ha
      subst a
      exact ⟨values, Heap.read_alloc_same _ _⟩
    | tuple fields =>
      rw [hvalue] at h
      simp only [copyValue] at h
      change ((copyFields fields).run memory >>= fun pair =>
        pure (.tuple pair.1, pair.2)) = .ok (out, memory') at h
      cases hc : (copyFields fields).run memory with
      | error e => simp [hc] at h
      | ok pair =>
        obtain ⟨fields', last⟩ := pair
        simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [arrayIdentities] using
          copyFields_flat fields memory last fields' (by simpa [hvalue, arrayIdentities] using flat) hc
  termination_by sizeOf value
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
  theorem copyFields_flat (fields : List (String × Value)) (memory memory' : Memory)
      (out : List (String × Value)) (flat : FlatArrays memory (fieldIdentities fields))
      (h : (copyFields fields).run memory = .ok (out, memory')) :
      FlatArrays memory' (fieldIdentities out) := by
    cases hfields : fields with
    | nil =>
      rw [hfields] at h
      simp [copyFields, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [FlatArrays, fieldIdentities]
    | cons kv fields =>
      cases hkv : kv with
      | mk key value =>
        have flatHead : FlatArrays memory (arrayIdentities value) := by
          intro a ha
          exact flat a (by simp [hfields, hkv, fieldIdentities, ha])
        have flatTail : FlatArrays memory (fieldIdentities fields) := by
          intro a ha
          exact flat a (by simp [hfields, hkv, fieldIdentities, ha])
        rw [hfields, hkv] at h
        simp only [copyFields] at h
        change ((copyValue value).run memory >>= fun pair =>
          (copyFields fields).run pair.2 >>= fun tail =>
          pure ((key, pair.1) :: tail.1, tail.2)) = .ok (out, memory') at h
        cases hv : (copyValue value).run memory with
        | error e => simp [hv] at h
        | ok pair =>
          obtain ⟨value', middle⟩ := pair
          cases hf : (copyFields fields).run middle with
          | error e => simp [hv, hf] at h
          | ok pair =>
            obtain ⟨fields', last⟩ := pair
            simp [hv, hf] at h
            obtain ⟨rfl, rfl⟩ := h
            have head := copyValue_flat value memory middle value' flatHead hv
            obtain ⟨headFrame, headBounds, _⟩ := copyValue_frame value memory middle value' hv
            obtain ⟨tailFrame, _, _⟩ := copyFields_frame fields middle last fields' hf
            have tailMiddle : FlatArrays middle (fieldIdentities fields) := by
              intro a ha
              obtain ⟨values, hr⟩ := flatTail a ha
              have low : a < memory.next := by
                by_cases low : a < memory.next
                · exact low
                · have missing := memory.fresh a (Nat.le_of_not_gt low)
                  simp [Heap.read, missing] at hr
              refine ⟨values, ?_⟩
              unfold Heap.read at hr ⊢
              rw [headFrame.2 a low]
              exact hr
            have tail := copyFields_flat fields middle last fields' tailMiddle hf
            have headLast := flatArrays_frame middle last (arrayIdentities value') tailFrame
              (fun a ha => (headBounds a ha).2) head
            intro a ha
            simp only [fieldIdentities, List.mem_append] at ha
            exact ha.elim (headLast a) (tail a)
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
end

private theorem cells_write_other (before after : Heap α) (a b : Addr) (value : α)
    (h : before.write a value = .ok after) (ne : b ≠ a) : after.cells b = before.cells b := by
  unfold Heap.write at h
  split at h
  · cases h
  · cases h; simp [ne]


/-- Numeric arrays nested arbitrarily in NamedTuples copy to fresh numeric
arrays, and writes to the copies preserve every source cell. -/
def flatOwnedMetadataCopyProperty : Prop :=
  ∀ (memory memory' : Memory) (ex out : Expression),
    FlatArrays memory (arrayIdentities ex.metadata) →
    copyMetadata memory ex = .ok (out, memory') →
    FlatArrays memory' (arrayIdentities out.metadata) ∧
    MemoryFrame memory memory' ∧ (arrayIdentities out.metadata).Nodup ∧
    (∀ a, a ∈ arrayIdentities out.metadata → memory.cells a = none) ∧
    ∀ a, a ∈ arrayIdentities out.metadata → ∀ writes : List Atom,
      ∃ written, memory'.write a writes = .ok written ∧
        ∀ source, source < memory.next → written.cells source = memory.cells source
 theorem flatOwnedMetadataCopy_proven : flatOwnedMetadataCopyProperty := by
  intro memory memory' ex out flat h
  unfold copyMetadata at h
  cases hv : (copyValue ex.metadata).run memory with
  | error e => simp [hv] at h
  | ok pair =>
    obtain ⟨metadata, last⟩ := pair
    simp [hv] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨frame, bounds, independent, _⟩ := copyValue_frame ex.metadata memory last metadata hv
    have flatOut := copyValue_flat ex.metadata memory last metadata flat hv
    refine ⟨flatOut, frame, independent, fun a ha => memory.fresh a (bounds a ha).1, ?_⟩
    intro a ha writes
    obtain ⟨values, hr⟩ := flatOut a ha
    obtain ⟨written, hw⟩ := heap_write_success last a _ writes hr
    refine ⟨written, hw, ?_⟩
    intro source low
    have ne : source ≠ a := by
      have high := (bounds a ha).1
      omega
    rw [cells_write_other _ _ _ _ _ hw ne, frame.2 source low]

private theorem zip_fst_snd {α β : Type} : ∀ (pairs : List (α × β)),
    (pairs.map Prod.fst).zip (pairs.map Prod.snd) = pairs
  | [] => rfl
  | pair :: pairs => by simp [zip_fst_snd pairs]

/-- Dictionaries with immutable values allocate fresh, equal outer storage and
allocate no arrays. -/
def dictionaryFlatCopyProperty : Prop :=
  ∀ (dictionaries dictionaries' : DictionaryMemory) (memory memory' : Memory)
    (source copied : Addr) (entries : List (String × Nat)),
    dictionaries.read source = .ok (entries.map (fun kv => (kv.1, Atom.number kv.2))) →
    copyDictionaryField dictionaries memory source = .ok (copied, dictionaries', memory') →
    copied ≠ source ∧ dictionaries.cells copied = none ∧
    dictionaries'.read copied = .ok (entries.map (fun kv => (kv.1, Atom.number kv.2))) ∧
    dictionaries'.read source = dictionaries.read source ∧ memory' = memory ∧
    ∀ writes : List (String × Atom), ∃ written, dictionaries'.write copied writes = .ok written ∧
      written.read source = dictionaries.read source
 theorem dictionaryFlatCopy_proven : dictionaryFlatCopyProperty := by
  intro dictionaries dictionaries' memory memory' source copied entries hr hc
  have numbers : ((entries.map (fun kv => (kv.1, Atom.number kv.2))).map Prod.snd).all
      Atom.isNumber = true := by
    simpa using all_isNumber_map (entries.map Prod.snd)
  have keep := copyAtomsWith_numbers (deepCopyArray (memory.next + 1)) _ (memory, []) numbers
  simp only [copyDictionaryField, hr, keep, zip_fst_snd, Except.ok.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  have fresh := Heap.alloc_fresh dictionaries (entries.map (fun kv => (kv.1, Atom.number kv.2)))
  have ne : source ≠ (dictionaries.alloc (entries.map (fun kv => (kv.1, Atom.number kv.2)))).1 := by
    intro eq; rw [eq] at hr; simp [Heap.read, fresh] at hr
  refine ⟨Ne.symm ne, fresh, Heap.read_alloc_same _ _, Heap.read_alloc_other _ _ _ ne, rfl, ?_⟩
  intro writes
  obtain ⟨written, hw⟩ := heap_write_success _ _ _ writes (Heap.read_alloc_same dictionaries _)
  refine ⟨written, hw, ?_⟩
  rw [Heap.read_write_other _ _ _ _ _ hw ne, Heap.read_alloc_other _ _ _ ne]

/-- Every successful dictionary copy is detached from every allocated source
array: no copied entry references one. -/
def dictionaryDeepCopyProperty : Prop :=
  ∀ (dictionaries dictionaries' : DictionaryMemory) (memory memory' : Memory)
    (source copied inner : Addr) (entries : List (String × Atom)) (key : String)
    (values : List Atom),
    memory.read inner = .ok values →
    copyDictionaryField dictionaries memory source = .ok (copied, dictionaries', memory') →
    dictionaries'.read copied = .ok entries →
    (key, Atom.reference inner) ∉ entries
 theorem dictionaryDeepCopy_proven : dictionaryDeepCopyProperty := by
  intro dictionaries dictionaries' memory memory' source copied inner entries key values
    hinner hc hread hmem
  unfold copyDictionaryField at hc
  cases hr : dictionaries.read source with
  | error e => simp [hr] at hc
  | ok original =>
    simp only [hr] at hc
    cases hl : copyAtomsWith (deepCopyArray (memory.next + 1)) (original.map Prod.snd) (memory, []) with
    | error e => simp [hl] at hc
    | ok result =>
      obtain ⟨copiedValues, state⟩ := result
      simp only [hl, Except.ok.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      rw [Heap.read_alloc_same] at hread
      injection hread with hread
      subst hread
      obtain ⟨_, _, refs⟩ := copyAtomsWith_preserves (deepCopyArray (memory.next + 1))
        (DeepInvariant memory.next) (fun r => memory.next ≤ r)
        (fun a s r s' hs hrun =>
          let ⟨f, i, l, _⟩ := deepCopyArray_invariant _ _ _ _ _ _ hs hrun
          ⟨f, i, l⟩)
        _ _ _ _ (deepInvariant_start memory) hl
      have high := refs inner (List.of_mem_zip hmem).2
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (heap_read_lt hinner) high)
example : (Heap.empty.alloc [.number 1, .number 2] : Addr × Memory).2.read 0 =
      .ok [.number 1, .number 2] ∧
    (copyDictionaryField (Heap.empty.alloc [("weights", Atom.reference 0)]).2
      (Heap.empty.alloc [.number 1, .number 2]).2 0).toOption.map
      (fun result => result.2.1.read result.1) = some (.ok [("weights", Atom.reference 1)]) :=
  ⟨rfl, rfl⟩

mutual
  theorem copyValue_success (value : Value) (memory : Memory) (P : Addr → Prop)
      (closed : ClosedAllocated memory P) (covered : ∀ a, a ∈ arrayIdentities value → P a) :
      ∃ out memory', (copyValue value).run memory = .ok (out, memory') := by
    cases hvalue : value with
    | number n =>
      refine ⟨.number n, memory, ?_⟩
      simp [copyValue, StateT.run]
    | array a =>
      obtain ⟨copied, memory', hc⟩ :=
        copyArray_success a memory P closed (covered a (by simp [hvalue, arrayIdentities]))
      exact ⟨.array copied, memory', by rw [copyValue_array_run, hc]; rfl⟩
    | tuple fields =>
      obtain ⟨out, memory', hc⟩ := copyFields_success fields memory P closed
        (by simpa [hvalue, arrayIdentities] using covered)
      refine ⟨.tuple out, memory', ?_⟩
      have hc' : copyFields fields memory = .ok (out, memory') := hc
      simp [copyValue, StateT.run, hc']
  termination_by sizeOf value
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
  theorem copyFields_success (fields : List (String × Value)) (memory : Memory) (P : Addr → Prop)
      (closed : ClosedAllocated memory P) (covered : ∀ a, a ∈ fieldIdentities fields → P a) :
      ∃ out memory', (copyFields fields).run memory = .ok (out, memory') := by
    cases hfields : fields with
    | nil => refine ⟨[], memory, ?_⟩; simp [copyFields, StateT.run]
    | cons kv fields =>
      cases hkv : kv with
      | mk key value =>
        have ch : ∀ a, a ∈ arrayIdentities value → P a := by
          intro a ha; exact covered a (by simp [hfields, hkv, fieldIdentities, ha])
        have ct : ∀ a, a ∈ fieldIdentities fields → P a := by
          intro a ha; exact covered a (by simp [hfields, hkv, fieldIdentities, ha])
        obtain ⟨head, middle, hv⟩ := copyValue_success value memory P closed ch
        have frame := (copyValue_frame value memory middle head hv).1
        obtain ⟨tail, last, hf⟩ :=
          copyFields_success fields middle P (closedAllocated_frame closed frame) ct
        refine ⟨(key, head) :: tail, last, ?_⟩
        have hv' : copyValue value memory = .ok (head, middle) := hv
        have hf' : copyFields fields middle = .ok (tail, last) := hf
        simp [copyFields, StateT.run, hv', hf']
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
end

/-- All well-typed metadata whose transitively referenced arrays are allocated
succeeds under recursive copying. -/
def metadataCopySuccessProperty : Prop :=
  (∀ (memory : Memory) (value : Value), ReachableArraysAllocated memory (arrayIdentities value) →
    ∃ out memory', (copyValue value).run memory = .ok (out, memory')) ∧
  (∀ (memory : Memory) (fields : List (String × Value)),
    ReachableArraysAllocated memory (fieldIdentities fields) →
    ∃ out memory', (copyFields fields).run memory = .ok (out, memory')) ∧
  (∀ (memory : Memory) (ex : Expression),
    ReachableArraysAllocated memory (arrayIdentities ex.metadata) →
    ∃ out memory', copyMetadata memory ex = .ok (out, memory'))
 theorem metadataCopySuccess_proven : metadataCopySuccessProperty := by
  refine ⟨fun memory value h => ?_, fun memory fields h => ?_, ?_⟩
  · obtain ⟨P, closed, covered⟩ := reachable_closed h
    exact copyValue_success value memory P closed covered
  · obtain ⟨P, closed, covered⟩ := reachable_closed h
    exact copyFields_success fields memory P closed covered
  intro memory ex h
  obtain ⟨P, closed, covered⟩ := reachable_closed h
  obtain ⟨metadata, memory', hv⟩ := copyValue_success ex.metadata memory P closed covered
  refine ⟨⟨ex.contents, metadata⟩, memory', ?_⟩
  simp [copyMetadata, hv]

def dictionaryCopySuccessProperty : Prop :=
  ∀ (dictionaries : DictionaryMemory) (memory : Memory) (source : Addr)
    (entries : List (String × Atom)),
    dictionaries.read source = .ok entries →
    (∀ key inner, (key, Atom.reference inner) ∈ entries →
      ReachableArraysAllocated memory [inner]) →
    ∃ copied dictionaries' memory',
      copyDictionaryField dictionaries memory source = .ok (copied, dictionaries', memory')
 theorem dictionaryCopySuccess_proven : dictionaryCopySuccessProperty := by
  intro dictionaries memory source entries hr allocated
  let P : Addr → Prop := fun b =>
    ∃ key inner, (key, Atom.reference inner) ∈ entries ∧ ArrayReach memory inner b
  have closed : ClosedAllocated memory P := by
    intro b ⟨key, inner, hmem, reach⟩
    obtain ⟨values, hread⟩ := allocated key inner hmem inner (by simp) b reach
    exact ⟨values, hread, fun r hr => ⟨key, inner, hmem, .step reach hread hr⟩⟩
  obtain ⟨values, state, hc, _⟩ := copyAtomsWith_success (deepCopyArray (memory.next + 1))
    (fun s => DeepInvariant memory.next s ∧ MemoryFrame memory s.1) P
    (fun a s hs ha => by
      obtain ⟨c, s', run, inv, frame, _⟩ := deepCopyArray_success memory P closed
        (memory.next + 1) a s hs.1 hs.2 ha (Nat.succ_le_succ (missingKeys_le _ _))
      exact ⟨c, s', run, inv, frame⟩)
    (entries.map Prod.snd) (memory, []) ⟨deepInvariant_start memory, MemoryFrame.refl _⟩
    (fun r hr => by
      obtain ⟨kv, hkv, heq⟩ := List.mem_map.mp hr
      exact ⟨kv.1, r, by rw [← heq]; exact hkv, .root⟩)
  exact ⟨(dictionaries.alloc ((entries.map Prod.fst).zip values)).1,
    (dictionaries.alloc ((entries.map Prod.fst).zip values)).2, state.1,
    by simp only [copyDictionaryField, hr, hc]⟩


private theorem listMap_success_loop {α β : Type} (f : α → Jl β) (P : β → Prop)
    (xs : List α) (acc : List β)
    (step : ∀ a, a ∈ xs → ∃ b, f a = .ok b ∧ P b)
    (initial : ∀ b, b ∈ acc → P b) :
    ∃ out, List.mapM.loop f xs acc = .ok out ∧ ∀ b, b ∈ out → P b := by
  induction xs generalizing acc with
  | nil =>
    refine ⟨acc.reverse, by simp [List.mapM.loop], ?_⟩
    intro b hb; exact initial b (by simpa using hb)
  | cons a xs ih =>
    obtain ⟨b, hb, pb⟩ := step a (by simp)
    have next : ∀ c, c ∈ b :: acc → P c := by
      intro c hc; simp only [List.mem_cons] at hc
      exact hc.elim (fun eq => eq ▸ pb) (initial c)
    obtain ⟨out, hout, pout⟩ := ih (b :: acc) (fun a ha => step a (by simp [ha])) next
    exact ⟨out, by simp [List.mapM.loop, hb, hout], pout⟩

private theorem listMap_success {α β : Type} (f : α → Jl β) (P : β → Prop)
    (xs : List α) (step : ∀ a, a ∈ xs → ∃ b, f a = .ok b ∧ P b) :
    ∃ out, xs.mapM f = .ok out ∧ ∀ b, b ∈ out → P b :=
  listMap_success_loop f P xs [] step (by simp)

def ReadableConstant (g : Graph JF) (a : Addr) : Prop :=
  ∃ cell, g.read a = .ok cell ∧
    (cell.degree = 0 → cell.constant = true → ∃ value, cell.val = some value)

private theorem decoded_readable (g : Graph JF) (fuel root : Nat)
    (decoded : ∃ tree, g.unfold fuel root = some tree) : ReadableConstant g root := by
  cases fuel with
  | zero => simp [Graph.unfold] at decoded
  | succ fuel =>
    obtain ⟨cell, hc, _⟩ := HeapCopy.decoded_children decoded
    refine ⟨cell, by simp [Heap.read, hc], ?_⟩
    intro hd hconstant
    cases hv : cell.val with
    | some value => exact ⟨value, rfl⟩
    | none => simp [Graph.unfold, hc, hd, hconstant, hv] at decoded

 theorem occurrences_success (g : Graph JF) (fuel root : Nat)
    (decoded : ∃ tree, g.unfold fuel root = some tree) :
    ∃ nodes, Sampling.occurrences g fuel root = .ok nodes ∧
      ∀ a, a ∈ nodes → ReadableConstant g a := by
  induction fuel generalizing root with
  | zero => simp [Graph.unfold] at decoded
  | succ fuel ih =>
    obtain ⟨cell, hc, children⟩ := HeapCopy.decoded_children decoded
    obtain ⟨lists, hlists, readable⟩ := listMap_success (Sampling.occurrences g fuel)
      (fun nodes => ∀ a, a ∈ nodes → ReadableConstant g a) cell.children
      (fun child hchild => ih child (children child hchild))
    refine ⟨root :: lists.flatten, ?_, ?_⟩
    · simp [Sampling.occurrences, Heap.read, hc, hlists]
    · intro a ha
      simp only [List.mem_cons, List.mem_flatten] at ha
      rcases ha with rfl | ⟨nodes, hnodes, ha⟩
      · exact decoded_readable g (fuel + 1) _ decoded
      · exact readable nodes hnodes a ha

private theorem constantEntry_success (g : Graph JF) (a : Addr)
    (readable : ReadableConstant g a) : ∃ pair, constantEntry g a = .ok pair := by
  obtain ⟨cell, hr, ready⟩ := readable
  unfold constantEntry
  simp only [hr, jl_ok_bind]
  split
  · rename_i selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
    obtain ⟨value, hv⟩ := ready selected.1 selected.2
    exact ⟨some (value, a), by simp [hv]⟩
  · exact ⟨none, rfl⟩

private theorem listFilter_success_loop {α β : Type} (f : α → Jl (Option β))
    (xs : List α) (acc : List β) (step : ∀ a, a ∈ xs → ∃ b, f a = .ok b) :
    ∃ out, List.filterMapM.loop f xs acc = .ok out := by
  induction xs generalizing acc with
  | nil => exact ⟨acc.reverse, by simp [List.filterMapM.loop]⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := step a (by simp)
    have tail := fun a ha => step a (List.mem_cons_of_mem _ ha)
    cases b with
    | none =>
      obtain ⟨out, hout⟩ := ih acc tail
      exact ⟨out, by simp [List.filterMapM.loop, hb, hout]⟩
    | some b =>
      obtain ⟨out, hout⟩ := ih (b :: acc) tail
      exact ⟨out, by simp [List.filterMapM.loop, hb, hout]⟩

/-- Finite successfully decoded source trees make traversal and getters total. -/
def scalarGetterSuccessProperty : Prop :=
  ∀ (g : Graph JF) (root fuel : Nat) (preserve breakSharing : Bool)
    (buffers : Heap (List JF)),
    (∃ tree, g.unfold fuel root = some tree) →
    (∃ nodes, Sampling.traversal g fuel root preserve breakSharing = .ok nodes) ∧
    ∃ address refs buffers', getConstants g root fuel preserve buffers = .ok (address, refs, buffers')
 theorem scalarGetterSuccess_proven : scalarGetterSuccessProperty := by
  intro g root fuel preserve breakSharing buffers decoded
  obtain ⟨nodes, hn, readable⟩ := occurrences_success g fuel root decoded
  refine ⟨?_, ?_⟩
  · exact ⟨if preserve && !breakSharing then nodes.eraseDups else nodes,
      by simp [Sampling.traversal, hn]⟩
  · let selected := if preserve then nodes.eraseDups else nodes
    have ht : Sampling.traversal g fuel root preserve false = .ok selected := by
      simp [Sampling.traversal, hn, selected]
    have ready : ∀ a, a ∈ selected → ReadableConstant g a := by
      intro a ha
      apply readable a
      cases preserve <;> simpa [selected] using ha
    obtain ⟨pairs, hp⟩ := listFilter_success_loop (constantEntry g) selected []
      (fun a ha => constantEntry_success g a (ready a ha))
    have hp' : selected.filterMapM (constantEntry g) = .ok pairs := hp
    refine ⟨buffers.next, pairs.map Prod.snd, (buffers.alloc (pairs.map Prod.fst)).2, ?_⟩
    change (Sampling.traversal g fuel root preserve false >>= fun nodes =>
      nodes.filterMapM (constantEntry g) >>= fun pairs =>
      pure (buffers.next, pairs.map Prod.snd, (buffers.alloc (pairs.map Prod.fst)).2)) = _
    simp [ht, hp']

/-- Full copying succeeds on finite decoded trees with metadata whose
transitively referenced arrays are allocated. -/
def fullCopySuccessProperty : Prop :=
  ∀ (graph : Graph JF) (memory : Memory) (ex : Expression) (fuel : Nat)
    (preserve breakSharing : Bool),
    (∃ tree, graph.unfold fuel ex.contents = some tree) →
    ReachableArraysAllocated memory (arrayIdentities ex.metadata) →
    ∃ out graph' memory', copyExpression graph memory ex fuel preserve breakSharing =
      .ok (out, graph', memory')
 theorem fullCopySuccess_proven : fullCopySuccessProperty := by
  intro graph memory ex fuel preserve breakSharing decoded allocated
  obtain ⟨⟨root, state⟩, hc⟩ := HeapCopy.copyNode_success graph
    (preserve && !breakSharing) fuel ex.contents (graph, []) decoded
  obtain ⟨P, closed, covered⟩ := reachable_closed allocated
  obtain ⟨metadata, memory', hv⟩ := copyValue_success ex.metadata memory P closed covered
  exact ⟨⟨root, metadata⟩, state.1, memory', by simp [copyExpression, hc, hv]⟩


private theorem leaf_endpoint (g : Graph JF) (root : Addr) (cell : Cell JF)
    (hc : g.cells root = some cell) (empty : cell.children = [])
    {path : List Nat} {a : Addr} (h : Graph.Path g root path a) : a = root := by
  cases h with
  | nil => rfl
  | cons hc' hi _ =>
    rw [hc] at hc'
    cases hc'
    simp [empty] at hi

example : ∃ (g : Graph JF) (left right : Expression) (op : Nat),
    Graph.NoAlias g left.contents ∧ Graph.NoAlias g right.contents ∧
    (∀ a, Graph.Reachable g left.contents a → a < g.next) ∧
    (∀ a, Graph.Reachable g right.contents a → a < g.next) ∧
    (∀ a, Graph.Reachable g left.contents a → ¬ Graph.Reachable g right.contents a) ∧
    1 ≤ op ∧ op ≤ 255 := by
  let cell : Cell JF := ⟨0, true, some (.fin 1), 0, 0, []⟩
  let g := ((Heap.empty.alloc cell).2.alloc cell).2
  have hzero : g.cells 0 = some cell := rfl
  have hone : g.cells 1 = some cell := rfl
  refine ⟨g, ⟨0, .tuple []⟩, ⟨1, .tuple []⟩, 1, ?_, ?_, ?_, ?_, ?_, by omega, by omega⟩
  · apply NoAlias.noAlias_leaf
    intro other hc; rw [hzero] at hc; cases hc; rfl
  · apply NoAlias.noAlias_leaf
    intro other hc; rw [hone] at hc; cases hc; rfl
  · intro a ha
    obtain ⟨path, hp⟩ := ha
    have eq := leaf_endpoint g 0 cell hzero rfl hp
    subst a
    exact Nat.zero_lt_succ 1
  · intro a ha
    obtain ⟨path, hp⟩ := ha
    have eq := leaf_endpoint g 1 cell hone rfl hp
    subst a
    exact Nat.lt_succ_self 1
  · intro a ha hb
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    have left := leaf_endpoint g 0 cell hzero rfl hp
    have right := leaf_endpoint g 1 cell hone rfl hq
    have impossible : (0 : Nat) = 1 := left.symm.trans right
    cases impossible

example : FlatArrays flatMemory (arrayIdentities flatExpression.metadata) ∧
    copyMetadata flatMemory flatExpression =
      .ok (⟨7, .tuple [("names", .array 1)]⟩, (flatMemory.alloc [.number 1, .number 2]).2) := by
  constructor
  · intro a ha
    simp [flatExpression, arrayIdentities, fieldIdentities] at ha
    subst a
    exact ⟨[1, 2], rfl⟩
  · simp only [copyMetadata, copyValue, copyFields, flatExpression]; rfl
example :
    (Heap.empty.alloc [("weights", Atom.number 1)]).2.read 0 =
      .ok ([("weights", 1)].map (fun kv => (kv.1, Atom.number kv.2))) ∧
    copyDictionaryField (Heap.empty.alloc [("weights", Atom.number 1)]).2 flatMemory 0 =
      .ok (1, ((Heap.empty.alloc [("weights", Atom.number 1)]).2.alloc [("weights", Atom.number 1)]).2,
        flatMemory) :=
  ⟨rfl, rfl⟩
private theorem flatExpression_flat :
    FlatArrays flatMemory (arrayIdentities flatExpression.metadata) := by
  intro a ha
  simp [flatExpression, arrayIdentities, fieldIdentities] at ha
  subst a
  exact ⟨[1, 2], rfl⟩
example : ReachableArraysAllocated flatMemory (arrayIdentities flatExpression.metadata) :=
  flat_reachable flatExpression_flat
example : operandGraph.unfold 1 0 = some (.const (.fin 1)) := rfl
example : (∃ tree, operandGraph.unfold 1 0 = some tree) ∧
    ReachableArraysAllocated flatMemory (arrayIdentities flatExpression.metadata) :=
  ⟨⟨.const (.fin 1), rfl⟩, flat_reachable flatExpression_flat⟩
example : ReachableArraysAllocated nestedMemory (arrayIdentities nestedExpression.metadata) := by
  intro root hroot a reach
  simp [nestedExpression, arrayIdentities, fieldIdentities] at hroot
  subst root
  have inner : ∀ b, ArrayReach nestedMemory 1 b → b = 1 ∨ b = 0 := by
    intro b hb
    induction hb with
    | root => exact Or.inl rfl
    | step _ hread hmem ih =>
      rcases ih with rfl | rfl
      · have : nestedMemory.read 1 = .ok [.reference 0] := rfl
        rw [this] at hread
        injection hread with hread
        subst hread
        simp at hmem
        exact Or.inr hmem
      · have : nestedMemory.read 0 = .ok [.number 1] := rfl
        rw [this] at hread
        injection hread with hread
        subst hread
        simp at hmem
  rcases inner a reach with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩


/-- Mutations through an allocated field/getter identity always succeed. -/
def heapWriteSuccessProperty : Prop :=
  ∀ (V : Type) (heap : Heap V) (address : Addr) (before after : V),
    heap.read address = .ok before → ∃ written, heap.write address after = .ok written
 theorem heapWriteSuccess_proven : heapWriteSuccessProperty := by
  intro V heap address before after h
  exact heap_write_success heap address before after h
example : (Heap.empty.alloc [JF.fin 1]).2.read 0 = .ok [JF.fin 1] := rfl


mutual
  /-- The Julia field copier retains every directly stored metadata array,
  including arrays in nested NamedTuples, src/Expression.jl:42-49 on origin/master. -/
  theorem copyValue_arrayCount (value : Value) (memory memory' : Memory) (out : Value)
      (h : (copyValue value).run memory = .ok (out, memory')) :
      (arrayIdentities out).length = (arrayIdentities value).length := by
    cases hvalue : value with
    | number n =>
      rw [hvalue] at h
      simp [copyValue, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [arrayIdentities]
    | array source =>
      rw [hvalue, copyValue_array_run] at h
      cases hc : copyArray source memory with
      | error err => simp [hc] at h
      | ok result =>
        simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [arrayIdentities]
    | tuple fields =>
      rw [hvalue] at h
      simp only [copyValue] at h
      change ((copyFields fields).run memory >>= fun result =>
        pure (.tuple result.1, result.2)) = .ok (out, memory') at h
      cases hc : (copyFields fields).run memory with
      | error err => simp [hc] at h
      | ok result =>
        obtain ⟨fields', after⟩ := result
        simp [hc] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [hvalue, arrayIdentities] using copyFields_arrayCount fields memory after fields' hc
  termination_by sizeOf value
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
  theorem copyFields_arrayCount (fields : List (String × Value)) (memory memory' : Memory)
      (out : List (String × Value))
      (h : (copyFields fields).run memory = .ok (out, memory')) :
      (fieldIdentities out).length = (fieldIdentities fields).length := by
    cases hfields : fields with
    | nil =>
      rw [hfields] at h
      simp [copyFields, StateT.run] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [fieldIdentities]
    | cons kv fields =>
      cases hkv : kv with
      | mk key value =>
        rw [hfields, hkv] at h
        simp only [copyFields] at h
        change ((copyValue value).run memory >>= fun head =>
          (copyFields fields).run head.2 >>= fun tail =>
          pure ((key, head.1) :: tail.1, tail.2)) = .ok (out, memory') at h
        cases hv : (copyValue value).run memory with
        | error err => simp [hv] at h
        | ok head =>
          obtain ⟨value', middle⟩ := head
          cases hf : (copyFields fields).run middle with
          | error err => simp [hv, hf] at h
          | ok tail =>
            obtain ⟨fields', after⟩ := tail
            simp [hv, hf] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [fieldIdentities, List.length_append,
              copyValue_arrayCount value memory middle value' hv,
              copyFields_arrayCount fields middle after fields' hf]
  termination_by sizeOf fields
  decreasing_by all_goals simp_all <;> simp_wf <;> omega
end

/-- Actual Metadata.copy execution succeeds and copies every direct mutable
array to fresh independent storage while preserving the complete source heap.
Inner arrays are deep-copied too (expressions-deep-metadata-copy),
src/Expression.jl:42-52 on origin/master. -/
def metadataFieldCopyProperty : Prop := ∀ (memory : Memory) (ex : Expression),
  ReachableArraysAllocated memory (arrayIdentities ex.metadata) →
  ∃ out memory', copyMetadata memory ex = .ok (out, memory') ∧
    MemoryFrame memory memory' ∧
    (arrayIdentities out.metadata).length = (arrayIdentities ex.metadata).length ∧
    (arrayIdentities out.metadata).Nodup ∧
    ∀ a, a ∈ arrayIdentities out.metadata → memory.cells a = none
 theorem metadataFieldCopy_proven : metadataFieldCopyProperty := by
  intro memory ex allocated
  obtain ⟨P, closed, covered⟩ := reachable_closed allocated
  obtain ⟨metadata, memory', copied⟩ := copyValue_success ex.metadata memory P closed covered
  obtain ⟨frame, bounds, independent, _⟩ := copyValue_frame ex.metadata memory memory' metadata copied
  refine ⟨⟨ex.contents, metadata⟩, memory', ?_, frame,
    copyValue_arrayCount ex.metadata memory memory' metadata copied, independent, ?_⟩
  · simp [copyMetadata, copied]
  · intro a ha
    exact memory.fresh a (bounds a ha).1
example : ReachableArraysAllocated flatMemory (arrayIdentities flatExpression.metadata) :=
  flat_reachable flatExpression_flat

end DynExpr.Expressions.Aliasing
