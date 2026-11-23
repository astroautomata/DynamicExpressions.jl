import DynExpr.NodeUtils.Preallocation
import DynExpr.NodeUtils.Operators
import DynExpr.NodeUtils.GraphIndex
import DynExpr.NodeUtils.Success
import DynExpr.NodeUtils.CopySharing

namespace DynExpr.NodeUtils

attribute [local simp] bindOk bindError mapOk mapError

/-- Mutable arrays and operator payloads referenced by Julia objects. Their
identities are separate from node identities, as in src/Utils.jl:87-89 and
src/Node.jl:79. Primitive numeric values stored in these arrays are immutable. -/
abbrev ArrayObjects := Heap (List Nat)

/-- src/Utils.jl:17-21: similar allocates a fresh outer vector, then fills it.
An object-valued fill repeats the supplied object identity in each slot. -/
def filledArrayObject (h : ArrayObjects) (n value : Nat) :=
  h.alloc (List.replicate n value)

private theorem allocatedDifferent (h : Heap T) (a : Addr) (v old : T)
    (ha : h.cells a = some old) : (h.alloc v).1 ≠ a := by
  intro he
  have hf := Heap.alloc_fresh h v
  rw [he,ha] at hf
  cases hf

def FilledArrayFresh : Prop := ∀ (h : ArrayObjects) a xs n v,
  h.cells a = some xs →
  (filledArrayObject h n v).1 ≠ a ∧
  (filledArrayObject h n v).2.read a = h.read a ∧
  (filledArrayObject h n v).2.read (filledArrayObject h n v).1 = .ok (List.replicate n v)

theorem filledArrayFresh_proven : FilledArrayFresh := by
  intro h a xs n v ha
  have hn := allocatedDifferent h a (List.replicate n v) xs ha
  exact ⟨hn, Heap.read_alloc_other h _ a (Ne.symm hn), Heap.read_alloc_same h _⟩

example : (Heap.empty.alloc ([1] : List Nat)).2.cells 0 = some [1] := rfl

/-- src/NodeUtils.jl:99-108: map creates new numeric-vector storage; returned
refs still point to the original node identities, as required by the setter. -/
def getNumericArrayObject (objects : ArrayObjects) (g : Graph Nat) (refs : List Addr) :
    Jl (Addr × ArrayObjects × List Addr) := do
  let values ← readValues g refs
  let (a,h) := objects.alloc values
  return (a,h,refs)

example : getNumericArrayObject Heap.empty (sourcePair 1 2) [0,1] =
    .ok (0,(Heap.empty.alloc [1,2]).2,[0,1]) := rfl

/-- src/NodeUtils.jl:126-130 copies primitive numeric elements from the caller's
array into value fields. The caller's vector object is never stored in a node. -/
def setFromNumericArray (g : Graph Nat) (objects : ArrayObjects) (a : Addr) (refs : List Addr) :
    Jl (Graph Nat) := do
  let values ← objects.read a
  setScalarConstants g values refs

def ReadValuesSuccess : Prop := ∀ (T : Type) (g : Graph T) (refs : List Addr),
  ValidRefs g refs → ∃ values, readValues g refs = .ok values

theorem readValuesSuccess_proven : ReadValuesSuccess := by
  intro T g refs valid
  exact readValues_success g refs valid

private theorem writeAllocated (g h : Heap T) (a b : Addr) (value cell : T)
    (hw : g.write a value = .ok h) (hc : g.cells b = some cell) : ∃ c, h.cells b = some c := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw
    by_cases hb : b = a
    · subst b; exact ⟨value,by simp⟩
    · exact ⟨cell,by simpa [hb] using hc⟩

private theorem writeSuccess (g : Heap T) (a : Addr) (value cell : T)
    (hc : g.cells a = some cell) : ∃ h, g.write a value = .ok h := by
  simp [Heap.write, hc]

private theorem setLoopSuccess (values : List Nat) : ∀ (g : Graph Nat) (refs : List Addr),
    values.length = refs.length → (∀ a ∈ refs, ∃ cell, g.cells a = some cell) →
    ∃ h, setScalarConstantsLoop g values refs = .ok h := by
  induction values with
  | nil =>
      intro g refs hl _
      cases refs with
      | nil => exact ⟨g,rfl⟩
      | cons a refs => simp at hl
  | cons v values ih =>
      intro g refs hl allocated
      cases refs with
      | nil => simp at hl
      | cons a refs =>
          obtain ⟨cell,hc⟩ := allocated a (by simp)
          obtain ⟨k,hk⟩ := writeSuccess g a {cell with val := some v} cell hc
          have hs : setValue g a v = .ok k := by simp [setValue, Heap.read, hc, hk, bindOk]
          have rest : ∀ b ∈ refs, ∃ c, k.cells b = some c := by
            intro b hb
            obtain ⟨old,ho⟩ := allocated b (by simp [hb])
            exact writeAllocated g k a b _ old hk ho
          obtain ⟨h,hh⟩ := ih k refs (Nat.succ.inj hl) rest
          exact ⟨h,by simp [setScalarConstantsLoop, hs, hh, bindOk]⟩

def NumericSetterSuccess : Prop := ∀ (g : Graph Nat) (values : List Nat) (refs : List Addr),
  values.length = refs.length → (∀ a ∈ refs, ∃ cell, g.cells a = some cell) →
  ∃ h, setScalarConstants g values refs = .ok h

theorem numericSetterSuccess_proven : NumericSetterSuccess := by
  intro g values refs hl allocated
  obtain ⟨h,hh⟩ := setLoopSuccess values g refs hl allocated
  exact ⟨h,by rw [setScalarConstants, ite_eq_left hl]; exact hh⟩

example : ∃ values, readValues (sourcePair 1 2) [0,1] = .ok values := ⟨[1,2],rfl⟩

example : ∀ a ∈ ([0,1] : List Addr), ∃ cell, (sourcePair 1 2).cells a = some cell := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

private theorem setLoopFrame (values : List Nat) : ∀ (refs : List Addr) (g h : Graph Nat) b,
    b ∉ refs → setScalarConstantsLoop g values refs = .ok h → h.read b = g.read b := by
  induction values with
  | nil =>
      intro refs g h b hb hw
      cases refs with
      | nil => cases hw; rfl
      | cons a refs => simp [setScalarConstantsLoop] at hw
  | cons v values ih =>
      intro refs g h b hb hw
      cases refs with
      | nil => simp [setScalarConstantsLoop] at hw
      | cons a refs =>
          have hba : b ≠ a := by intro he; exact hb (by simp [he])
          have hbr : b ∉ refs := by intro hm; exact hb (by simp [hm])
          cases hs : setValue g a v with
          | error e => simp [setScalarConstantsLoop, hs, bindError] at hw
          | ok k =>
              simp only [setScalarConstantsLoop, hs, bindOk] at hw
              rw [ih refs k h b hbr hw]
              cases hc : g.read a with
              | error e => simp [setValue, hc, bindError] at hs
              | ok cell =>
                  simp only [setValue, hc, bindOk] at hs
                  exact Heap.read_write_other g k a b _ hs hba

private theorem setLoopRead (values : List Nat) : ∀ (refs : List Addr) (g h : Graph Nat),
    refs.Nodup → setScalarConstantsLoop g values refs = .ok h → readValues h refs = .ok values := by
  induction values with
  | nil =>
      intro refs g h hn hw
      cases refs with
      | nil => rfl
      | cons a refs => simp [setScalarConstantsLoop] at hw
  | cons v values ih =>
      intro refs g h hn hw
      cases refs with
      | nil => simp [setScalarConstantsLoop] at hw
      | cons a refs =>
          have hn' : a ∉ refs ∧ refs.Nodup := List.nodup_cons.mp hn
          cases hs : setValue g a v with
          | error e => simp [setScalarConstantsLoop, hs, bindError] at hw
          | ok k =>
              simp only [setScalarConstantsLoop, hs, bindOk] at hw
              have ht := ih refs k h hn'.2 hw
              have hf := setLoopFrame values refs k h a hn'.1 hw
              cases hc : g.read a with
              | error e => simp [setValue, hc, bindError] at hs
              | ok cell =>
                  simp only [setValue, hc, bindOk] at hs
                  have ha := Heap.read_write_same g k a {cell with val := some v} hs
                  rw [ha] at hf
                  simp [readValues, hf, ht, bindOk]

def NumericSetGet : Prop := ∀ (g : Graph Nat) (values : List Nat) (refs : List Addr),
  refs.Nodup → values.length = refs.length →
  (∀ a ∈ refs, ∃ cell, g.cells a = some cell) →
  ∃ h, setScalarConstants g values refs = .ok h ∧ readValues h refs = .ok values

theorem numericSetGet_proven : NumericSetGet := by
  intro g values refs hn hl allocated
  obtain ⟨h,hw⟩ := numericSetterSuccess_proven g values refs hl allocated
  refine ⟨h,hw,?_⟩
  rw [setScalarConstants, ite_eq_left hl] at hw
  exact setLoopRead values refs g h hn hw

example : ([0,1] : List Addr).Nodup ∧ ([3,4] : List Nat).length = ([0,1] : List Addr).length ∧
    setScalarConstants (sourcePair 1 2) [3,4] [0,1] =
      .ok ((setScalarConstants (sourcePair 1 2) [3,4] [0,1]).toOption.getD (sourcePair 1 2)) := by
  exact ⟨by decide,rfl,rfl⟩

def NumericSetterDetached : Prop := ∀ (g : Graph Nat) (objects : ArrayObjects)
    (buffer : Addr) (refs : List Addr) (values replacement : List Nat),
  refs.Nodup → objects.cells buffer = some values → values.length = refs.length →
  (∀ a ∈ refs, ∃ cell, g.cells a = some cell) →
  ∃ h changed, setFromNumericArray g objects buffer refs = .ok h ∧
    objects.write buffer replacement = .ok changed ∧
    readValues h refs = .ok values ∧ changed.read buffer = .ok replacement

theorem numericSetterDetached_proven : NumericSetterDetached := by
  intro g objects buffer refs values replacement hn hc hl allocated
  obtain ⟨h,hs,hr⟩ := numericSetGet_proven g values refs hn hl allocated
  obtain ⟨changed,hw⟩ := writeSuccess objects buffer replacement values hc
  refine ⟨h,changed,?_,hw,hr,Heap.read_write_same objects changed buffer replacement hw⟩
  simp [setFromNumericArray,Heap.read,hc,hs,bindOk]

example : let objects : ArrayObjects := (Heap.empty.alloc [1,2]).2
    ∃ h changed, ([0,1] : List Addr).Nodup ∧ objects.read 0 = .ok [1,2] ∧
      setFromNumericArray (sourcePair 1 2) objects 0 [0,1] = .ok h ∧
      objects.write 0 [9] = .ok changed := by
  dsimp only
  let objects : ArrayObjects := (Heap.empty.alloc [1,2]).2
  exact ⟨(setFromNumericArray (sourcePair 1 2) objects 0 [0,1]).toOption.getD (sourcePair 1 2),
    (objects.write 0 [9]).toOption.getD objects,by decide,rfl,rfl,rfl⟩

/-- Valid numeric refs produce a fresh value vector and retain the supplied refs. -/
def NumericGetterRefs : Prop := ∀ (objects : ArrayObjects) (g : Graph Nat) (refs : List Addr),
  ValidRefs g refs → ∃ buffer buffers,
    getNumericArrayObject objects g refs = .ok (buffer,buffers,refs) ∧
    buffers.read buffer = readValues g refs ∧
    ∀ a old, objects.cells a = some old → buffer ≠ a ∧ buffers.read a = .ok old

theorem numericGetterRefs_proven : NumericGetterRefs := by
  intro objects g refs valid
  obtain ⟨values,hv⟩ := readValues_success g refs valid
  refine ⟨(objects.alloc values).1,(objects.alloc values).2,
    by simp [getNumericArrayObject,hv],
    by rw [hv]; exact Heap.read_alloc_same objects values,?_⟩
  intro a old hc
  have hfresh := allocatedDifferent objects a values old hc
  refine ⟨hfresh,?_⟩
  rw [Heap.read_alloc_other objects values a (Ne.symm hfresh)]
  simp [Heap.read,hc]

example : getNumericArrayObject Heap.empty (sourcePair 1 2) [0,1] =
    .ok (0,(Heap.empty.alloc [1,2]).2,[0,1]) := rfl

private theorem containerAllocation (n : Nat) : ∀ (g : Graph Nat),
    (allocateContainer g n).1.Nodup ∧
    (∀ a ∈ (allocateContainer g n).1, g.next ≤ a) ∧
    ∀ a, a < g.next → (allocateContainer g n).2.read a = g.read a := by
  induction n with
  | zero => intro g; exact ⟨by simp [allocateContainer],by simp [allocateContainer],by intros; rfl⟩
  | succ n ih =>
      intro g
      let empty : Cell Nat := ⟨0,false,none,0,0,[]⟩
      let first := (g.alloc empty).2
      obtain ⟨hn,hbounds,hframe⟩ := ih first
      have hnot : g.next ∉ (allocateContainer first n).1 := by
        intro hm
        have hb := hbounds g.next hm
        change g.next + 1 ≤ g.next at hb
        omega
      refine ⟨?_,?_,?_⟩
      · change (g.next :: (allocateContainer first n).1).Nodup
        exact List.nodup_cons.mpr ⟨hnot,hn⟩
      · intro a ha
        change a ∈ g.next :: (allocateContainer first n).1 at ha
        rcases List.mem_cons.mp ha with he | hm
        · subst a; exact Nat.le_refl _
        · have hb := hbounds a hm
          change g.next + 1 ≤ a at hb
          omega
      · intro a ha
        change (allocateContainer first n).2.read a = g.read a
        have ha' : a < first.next := by change a < g.next + 1; omega
        rw [hframe a ha']
        exact Heap.read_alloc_other g empty a (by change a ≠ g.next; omega)

/-- Container allocation creates distinct fresh slots and preserves old objects. -/
def ContainerDisjoint : Prop := ∀ (g : Graph Nat) n,
  (allocateContainer g n).1.Nodup ∧
  (∀ a ∈ (allocateContainer g n).1, g.next ≤ a ∧ g.cells a = none) ∧
  ∀ a old, g.cells a = some old → (allocateContainer g n).2.read a = .ok old

theorem containerDisjoint_proven : ContainerDisjoint := by
  intro g n
  obtain ⟨hn,hbounds,hframe⟩ := containerAllocation n g
  refine ⟨hn,fun a ha => ⟨hbounds a ha,g.fresh a (hbounds a ha)⟩,?_⟩
  intro a old hc
  have ha : a < g.next := by
    by_cases ha : a < g.next
    · exact ha
    · have hnone := g.fresh a (by omega)
      rw [hc] at hnone
      cases hnone
  rw [hframe a ha]
  simp [Heap.read,hc]

def nodeAddressAtPath (g : Graph T) : Addr → List Nat → Jl Addr
  | root, [] => .ok root
  | root, i :: path => do
      let cell ← g.read root
      let child ← match cell.children[i]? with
        | none => .error .boundsError | some a => .ok a
      nodeAddressAtPath g child path

private theorem nodeAddressAtPath_correct {g : Graph T} {root node path}
    (hp : Graph.Path g root path node) : nodeAddressAtPath g root path = .ok node := by
  induction hp with
  | nil => rfl
  | cons hc hi hp ih => simp [nodeAddressAtPath,Heap.read,hc,hi,ih,bindOk]

/-- Immutable scalar contents and mutable value-object identities are distinct. -/
inductive StoredValue where
  | scalar (value : Nat)
  | object (address : Addr)

/-- Scalar values are overwritten in copied nodes; mutable payload identities
instead select the shared object heap, as in Julia value assignment. -/
def mutateStoredCopiedValue (source : Graph StoredValue) (objects : Heap Nat)
    (sharing : Bool) (dest : List Addr) (out : Graph StoredValue) (fuel root : Nat)
    (path : List Nat) (replacement : Nat) : Jl (Graph StoredValue × Heap Nat) := do
  let (copied,nodes,_,_) ← copyInto source sharing dest out fuel root
  let selected ← nodeAddressAtPath nodes copied path
  let cell ← nodes.read selected
  if cell.degree = 0 ∧ cell.constant = true then
    match cell.val with
    | some (.scalar _) => return ((← setValue nodes selected (.scalar replacement)),objects)
    | some (.object a) => return (nodes,(← objects.write a replacement))
    | none => .error .undefRefError
  else .error (.argumentError "selected node is not constant")

/-- All reachable constant payloads are immutable scalar contents. -/
def ImmutableConstants (source : Graph StoredValue) (root : Addr) : Prop :=
  ∀ a, Graph.Reachable source root a → ∀ cell,
    source.cells a = some cell → cell.degree = 0 → cell.constant = true →
      ∃ value, cell.val = some (.scalar value)

private theorem cellsOfRead (g : Heap T) (a : Addr) (value : T)
    (hr : g.read a = .ok value) : g.cells a = some value := by
  cases hc : g.cells a with
  | none => simp [Heap.read,hc] at hr
  | some v =>
      have he : v = value := by simpa [Heap.read,hc] using hr
      subst v
      rfl

def CopyIntoImmutableValues : Prop :=
  ∀ (source out : Graph StoredValue) (objects : Heap Nat) (sharing : Bool)
    (dest : List Addr) (fuel root : Nat) (path : List Nat) (node : Addr)
    (cell : Cell StoredValue) (replacement : Nat),
    GraphWF source root → PathFuel source root fuel → (∃ tree, source.unfold fuel root = some tree) →
    (sharing = false → Graph.NoAlias source root) → dest.Nodup →
    (∀ a ∈ dest, (out.cells a).isSome) → CopyCapacity source root dest →
    (∀ a ∈ dest, source.cells a = none) →
    (∀ a c, source.cells a = some c → out.cells a = some c) →
    ImmutableConstants source root → Graph.Path source root path node →
    source.cells node = some cell → cell.degree = 0 → cell.constant = true →
    ∃ changed, mutateStoredCopiedValue source objects sharing dest out fuel root path replacement =
      .ok (changed,objects) ∧ ∀ a c, source.cells a = some c → changed.cells a = some c

theorem copyIntoImmutableValues_proven : CopyIntoImmutableValues := by
  intro source out objects sharing dest fuel root path node cell replacement
    hwf hfuel hunfold hplain hn hinit hcap hfresh hext hi hpath hc hd hconst
  obtain ⟨copied,nodes,cursor,cache,hr,_hu,hforward,_hb,_hid,hcorr,_hl,_hcount,hslots,hframe⟩ :=
    copySharing_proven StoredValue sharing source out dest fuel root hwf hfuel hunfold hplain hn hinit hcap
  obtain ⟨selected,hselected⟩ := hforward path node hpath
  have hcell := (hcorr path node selected cell hpath hselected hc).1 hd
  have haddress := nodeAddressAtPath_correct hselected
  obtain ⟨value,hvalue⟩ := hi node ⟨path,hpath⟩ cell hc hd hconst
  let updated := {cell with val := some (StoredValue.scalar replacement)}
  obtain ⟨changed,hw⟩ := writeSuccess nodes selected updated cell hcell
  have hs : setValue nodes selected (.scalar replacement) = .ok changed := by
    simp [setValue,Heap.read,hcell,updated,hw,bindOk]
  refine ⟨changed,?_,?_⟩
  · simp [mutateStoredCopiedValue,hr,haddress,Heap.read,hcell,hd,hconst,hvalue,hs,bindOk]
  · intro a old hold
    have hnot : a ∉ dest := by
      intro ha
      have hnone := hfresh a ha
      rw [hold] at hnone
      cases hnone
    have hnotTake : a ∉ dest.take cursor := fun ha => hnot (List.mem_of_mem_take ha)
    have hne : a ≠ selected := by
      intro he
      apply hnotTake
      rw [he]
      exact hslots selected ⟨path,hselected⟩
    have hsource : nodes.cells a = some old := by
      rw [hframe a hnotTake]
      exact hext a old hold
    apply cellsOfRead changed a old
    rw [Heap.read_write_other nodes changed selected a updated hw hne]
    simp [Heap.read,hsource]

private theorem leafReachableOnly (g : Graph T) (root : Addr) (cell : Cell T)
    (hc : g.cells root = some cell) (hn : cell.children = []) :
    ∀ a, Graph.Reachable g root a → a = root := by
  intro a ⟨path,hpath⟩
  cases hpath with
  | nil => rfl
  | cons hc' hi hp =>
      rw [hc] at hc'
      cases hc'
      rw [hn] at hi
      simp at hi

example : let source : Graph StoredValue := (Heap.empty.alloc (constantCell (.scalar 1))).2
    let slots := allocateContainer source 1
    ∃ changed, mutateStoredCopiedValue source Heap.empty false slots.1 slots.2 1 0 [] 9 =
      .ok (changed,Heap.empty) ∧ ∀ a c, source.cells a = some c → changed.cells a = some c := by
  dsimp only
  let source : Graph StoredValue := (Heap.empty.alloc (constantCell (.scalar 1))).2
  let slots := allocateContainer source 1
  have hc0 : source.cells 0 = some (constantCell (.scalar 1)) := rfl
  have reachOnly := leafReachableOnly source 0 (constantCell (.scalar 1)) hc0 rfl
  have slotOnly : ∀ a ∈ slots.1, a = 1 := by
    intro a ha
    simpa [slots,allocateContainer,source,Heap.alloc,Heap.empty] using ha
  apply copyIntoImmutableValues_proven source slots.2 Heap.empty false slots.1 1 0 [] 0
    (constantCell (.scalar 1)) 9
  · intro a ha
    have he := reachOnly a ha
    subst a
    exact ⟨constantCell (.scalar 1),rfl,rfl⟩
  · intro path a hp
    cases hp with
    | nil => decide
    | cons hc hi hp =>
        rw [hc0] at hc
        cases hc
        simp [constantCell] at hi
  · exact ⟨.const (.scalar 1),rfl⟩
  · intro _; exact Graph.noAlias_ofTree Heap.empty (.const (StoredValue.scalar 1))
  · change ([1] : List Addr).Nodup; decide
  · intro a ha; have he := slotOnly a ha; subst a; rfl
  · intro nodes hn hr
    cases nodes with
    | nil => simp
    | cons a rest =>
        cases rest with
        | nil => change 1 ≤ 1; decide
        | cons b rest =>
            have ha := reachOnly a (hr a (by simp))
            have hb := reachOnly b (hr b (by simp))
            exact False.elim ((List.nodup_cons.mp hn).1 (by simp [ha,hb]))
  · intro a ha; have he := slotOnly a ha; subst a; rfl
  · intro a cell hc
    have ha : a = 0 := by
      by_cases ha : a = 0
      · exact ha
      · simp [source,Heap.alloc,Heap.empty,ha] at hc
    subst a
    rw [hc0] at hc
    cases hc
    rfl
  · intro a ha cell hc _hd _hv
    have he := reachOnly a ha
    subst a
    rw [hc0] at hc
    cases hc
    exact ⟨1,rfl⟩
  · exact Graph.Path.nil 0
  · exact hc0
  · rfl
  · rfl


/-- src/Utils.jl:99-101 changes the named array object in place. -/
def setInvalidArrayObject (h : Heap (List JF)) (a : Addr) : Jl (Heap (List JF)) := do
  let xs ← h.read a
  h.write a (List.replicate xs.length JF.nan)

private theorem writeNext (h h' : Heap T) (a : Addr) (value : T)
    (hw : h.write a value = .ok h') : h'.next = h.next := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw; rfl

def InvalidArrayFrame : Prop := ∀ (h : Heap (List JF)) (a : Addr) (xs : List JF),
  h.cells a = some xs → ∃ h', setInvalidArrayObject h a = .ok h' ∧
    h'.next = h.next ∧ ∀ b, b ≠ a → h'.read b = h.read b

theorem invalidArrayFrame_proven : InvalidArrayFrame := by
  intro h a xs hc
  obtain ⟨h',hw⟩ := writeSuccess h a (List.replicate xs.length JF.nan) xs hc
  refine ⟨h',?_,writeNext h h' a _ hw,fun b hb => Heap.read_write_other h h' a b _ hw hb⟩
  simp [setInvalidArrayObject,Heap.read,hc,hw,bindOk]

example : (Heap.empty.alloc ([JF.fin 1] : List JF)).2.cells 0 = some [JF.fin 1] := rfl

def FillPayloadExposure : Prop := ∀ (a : Addr) n, (fillSimilar a n).toList = List.replicate n a

theorem fillPayloadExposure_proven : FillPayloadExposure := by
  intro a n
  simp [fillSimilar,JVec.fill]

/-- src/NodeUtils.jl:129 stores the supplied mutable numeric payload identity;
the outer caller vector itself is not stored. This is ordinary setter exposure. -/
def SetterPayloadExposure : Prop := ∀ (g : Graph Addr) (a value : Addr) (cell : Cell Addr),
  g.cells a = some cell → ∃ h, setValue g a value = .ok h ∧
    h.cells a = some {cell with val := some value}

theorem setterPayloadExposure_proven : SetterPayloadExposure := by
  intro g a value cell hc
  obtain ⟨h,hw⟩ := writeSuccess g a {cell with val := some value} cell hc
  refine ⟨h,?_,cellsOfRead h a _ (Heap.read_write_same g h a _ hw)⟩
  simp [setValue,Heap.read,hc,hw,bindOk]

example : (sourceLeaf 0).cells 0 = some (constantCell 0) := rfl

end DynExpr.NodeUtils
