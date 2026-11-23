import DynExpr.ParamStruct.ArrayAliases

namespace DynExpr.ParamStruct

/-- An array write cannot change a scalar that will be read later. -/
def SafeArrayReadOrder : ScalarView → ScalarView → Prop
  | d :: ds, _ :: xs => d ∉ xs ∧ SafeArrayReadOrder ds xs
  | [], _ | _, [] => True

/-- Each member copies its current slice before writing, so only later slices
must be protected from its writes. -/
def SafeStructuredReadOrder : List ScalarView → ScalarView → Prop
  | [], _ => True
  | dest :: members, input =>
    NoOverlap dest (input.drop dest.length) ∧
      SafeStructuredReadOrder members (input.drop dest.length)

private theorem readView_congr (h h' : ScalarMemory) (refs : ScalarView)
    (hr : ∀ a ∈ refs, h'.read a = h.read a) :
    readView h' refs = readView h refs := by
  unfold readView
  induction refs with
  | nil => rfl
  | cons a refs ih =>
    simp only [List.mapM_cons]
    rw [hr a (by simp), ih (by intro b hb; exact hr b (by simp [hb]))]

private theorem readView_append (h : ScalarMemory) (a b : ScalarView) :
    readView h (a ++ b) = (do
      let va ← readView h a
      let vb ← readView h b
      pure (va ++ vb)) := by
  unfold readView
  exact List.mapM_append

private theorem array_frame (h result : ScalarMemory) (dest input : ScalarView)
    (a : Addr) (ha : a ∉ dest) (hw : setArrayView h dest input = .ok result) :
    result.read a = h.read a := by
  induction dest generalizing h input with
  | nil => simp [setArrayView] at hw; subst result; rfl
  | cons d ds ih =>
    cases input with
    | nil => simp [setArrayView] at hw; subst result; rfl
    | cons x xs =>
      cases hx : h.read x with
      | error err => simp [setArrayView, hx] at hw
      | ok v =>
        cases hd : h.write d v with
        | error err => simp [setArrayView, hx, hd] at hw
        | ok h₁ =>
          simp only [setArrayView, hx, hd, jl_bind_ok] at hw
          have had : a ≠ d := by intro he; exact ha (by simp [he])
          have has : a ∉ ds := by intro hm; exact ha (by simp [hm])
          rw [ih h₁ xs has hw, Heap.read_write_other h h₁ d a v hd had]

/-- Successful array updates preserve the original scalar input whenever no
write precedes an overlapping read, including same-slot aliases. -/
theorem safe_array_set (h result : ScalarMemory) (dest input : ScalarView)
    (hn : dest.Nodup) (hlen : dest.length = input.length)
    (hs : SafeArrayReadOrder dest input)
    (hw : setArrayView h dest input = .ok result) :
    readView result dest = readView h input := by
  induction dest generalizing h input with
  | nil =>
    have he : input = [] := by simpa using hlen.symm
    subst input
    rfl
  | cons d ds ih =>
    cases input with
    | nil => simp at hlen
    | cons x xs =>
      have hnodup := List.nodup_cons.mp hn
      have hsafe : d ∉ xs ∧ SafeArrayReadOrder ds xs := hs
      cases hx : h.read x with
      | error err => simp [setArrayView, hx] at hw
      | ok v =>
        cases hd : h.write d v with
        | error err => simp [setArrayView, hx, hd] at hw
        | ok h₁ =>
          simp only [setArrayView, hx, hd, jl_bind_ok] at hw
          have hr : result.read d = .ok v := by
            rw [array_frame h₁ result ds xs d hnodup.1 hw]
            exact Heap.read_write_same h h₁ d v hd
          have ht := ih h₁ xs hnodup.2 (by simpa using hlen) hsafe.2 hw
          have hp : readView h₁ xs = readView h xs := by
            apply readView_congr
            intro a ha
            exact Heap.read_write_other h h₁ d a v hd
              (by intro he; subst a; exact hsafe.1 ha)
          simp only [readView, List.mapM_cons, hr, hx]
          change (do let vs ← readView result ds; pure (v :: vs)) =
            (do let vs ← readView h xs; pure (v :: vs))
          rw [ht, hp]

def ParameterOverlapSafeCompanion : Prop :=
  ∀ (h result : ScalarMemory) (dest input : ScalarView),
    dest.Nodup → dest.length = input.length → SafeArrayReadOrder dest input →
    setArrayView h dest input = .ok result →
    readView result dest = readView h input

theorem parameterOverlapSafeCompanion_proven : ParameterOverlapSafeCompanion :=
  safe_array_set

private theorem constants_frame (h result : ScalarMemory) (dest : ScalarView)
    (values : List JF) (a : Addr) (ha : a ∉ dest)
    (hw : writeConstants h dest values = .ok result) :
    result.read a = h.read a := by
  induction dest generalizing h values with
  | nil =>
    cases values with
    | nil => simp [writeConstants] at hw; subst result; rfl
    | cons v vs => simp [writeConstants] at hw
  | cons d ds ih =>
    cases values with
    | nil => simp [writeConstants] at hw
    | cons v vs =>
      cases hd : h.write d v with
      | error err => simp [writeConstants, hd] at hw
      | ok h₁ =>
        simp only [writeConstants, hd, jl_bind_ok] at hw
        have had : a ≠ d := by intro he; exact ha (by simp [he])
        have has : a ∉ ds := by intro hm; exact ha (by simp [hm])
        rw [ih h₁ vs has hw, Heap.read_write_other h h₁ d a v hd had]

private theorem structured_frame (h result : ScalarMemory)
    (members : List ScalarView) (input : ScalarView) (a : Addr)
    (ha : a ∉ members.flatten)
    (hw : setStructuredViews h members input = .ok result) :
    result.read a = h.read a := by
  induction members generalizing h input with
  | nil => simp [setStructuredViews] at hw; subst result; rfl
  | cons dest members ih =>
    simp only [setStructuredViews] at hw
    split at hw
    · cases hw
    · cases hr : readView h (input.take dest.length) with
      | error err => simp [hr] at hw
      | ok values =>
        cases hd : writeConstants h dest values with
        | error err => simp [hr, hd] at hw
        | ok h₁ =>
          simp only [hr, hd, jl_bind_ok] at hw
          have had : a ∉ dest := by
            intro hm; exact ha (by simp [hm])
          have ham : a ∉ members.flatten := by
            intro hm; exact ha (by simp [hm])
          rw [ih h₁ (input.drop dest.length) ham hw,
            constants_frame h h₁ dest values a had hd]

/-- Member slices may overlap their own destinations because they are copied;
only writes that would change later slices are excluded. -/
theorem safe_structured_set (h result : ScalarMemory)
    (members : List ScalarView) (input : ScalarView)
    (hn : members.flatten.Nodup) (hlen : members.flatten.length = input.length)
    (hs : SafeStructuredReadOrder members input)
    (hw : setStructuredViews h members input = .ok result) :
    readView result members.flatten = readView h input := by
  induction members generalizing h input with
  | nil =>
    have he : input = [] := by simpa using hlen.symm
    subst input
    rfl
  | cons dest members ih =>
    have hn' := List.nodup_append.mp
      (show (dest ++ members.flatten).Nodup from hn)
    have hsafe : NoOverlap dest (input.drop dest.length) ∧
        SafeStructuredReadOrder members (input.drop dest.length) := hs
    have enough : ¬ input.length < dest.length := by
      simp only [List.flatten_cons, List.length_append] at hlen
      omega
    simp only [setStructuredViews, ite_eq_right enough] at hw
    cases hr : readView h (input.take dest.length) with
    | error err => simp [hr] at hw
    | ok values =>
      cases hd : writeConstants h dest values with
      | error err => simp [hr, hd] at hw
      | ok h₁ =>
        simp only [hr, hd, jl_bind_ok] at hw
        have htail := ih h₁ (input.drop dest.length) hn'.2.1
          (by simp only [List.length_drop, List.flatten_cons, List.length_append] at *;
              omega) hsafe.2 hw
        have hhead : readView result dest = .ok values := by
          have hframe : readView result dest = readView h₁ dest := by
            apply readView_congr
            intro a ha
            exact structured_frame h₁ result members (input.drop dest.length) a
              (by intro ham; exact hn'.2.2 a ha a ham rfl) hw
          rw [hframe]
          exact writeConstants_read_values h h₁ dest values hn'.1 hd
        have hinput : readView h₁ (input.drop dest.length) =
            readView h (input.drop dest.length) := by
          apply readView_congr
          intro a ha
          apply constants_frame h h₁ dest values a _ hd
          intro had
          exact hsafe.1 a had ha
        rw [List.flatten_cons, readView_append, hhead, htail, hinput]
        conv => rhs; rw [← List.take_append_drop dest.length input, readView_append]
        rw [hr]

def StructuredOverlapSafeCompanion : Prop :=
  ∀ (h result : ScalarMemory) (members : List ScalarView) (input : ScalarView),
    members.flatten.Nodup → members.flatten.length = input.length →
    SafeStructuredReadOrder members input →
    setStructuredViews h members input = .ok result →
    readView result members.flatten = readView h input

theorem structuredOverlapSafeCompanion_proven : StructuredOverlapSafeCompanion :=
  safe_structured_set

private def aliasMemory : ScalarMemory :=
  ((Heap.empty.alloc (.fin 10)).2.alloc (.fin 20)).2

/-- A scalar read may alias a future destination, and the final read may alias
its own destination, without creating a write-before-read hazard. -/
example : ([0, 1] : ScalarView).Nodup ∧
    ([0, 1] : ScalarView).length = ([1, 1] : ScalarView).length ∧
    SafeArrayReadOrder [0, 1] [1, 1] ∧
    (∃ result, setArrayView aliasMemory [0, 1] [1, 1] = .ok result ∧
      readView result [0, 1] = .ok [.fin 20, .fin 20]) ∧
    ¬ NoOverlap [0, 1] [1, 1] := by
  refine ⟨by decide, rfl, ?_, ⟨_, rfl, rfl⟩, ?_⟩
  · simp [SafeArrayReadOrder]
  · intro ho
    exact ho 1 (by simp) (by simp)

/-- A reversed current member slice is safe because both values are copied
before either write, despite full overlap within that member. -/
example : ([[0, 1]] : List ScalarView).flatten.Nodup ∧
    ([[0, 1]] : List ScalarView).flatten.length = ([1, 0] : ScalarView).length ∧
    SafeStructuredReadOrder [[0, 1]] [1, 0] ∧
    (∃ result, setStructuredViews aliasMemory [[0, 1]] [1, 0] = .ok result) ∧
    ¬ NoOverlap [0, 1] [1, 0] := by
  refine ⟨by decide, rfl, ?_, ?_, ?_⟩
  · simp [SafeStructuredReadOrder, NoOverlap]
  · exact ⟨_, rfl⟩
  · intro ho
    exact ho 0 (by simp) (by simp)

private theorem write_exists (h : ScalarMemory) (a : Addr) (value : JF)
    (ha : ∃ old, h.read a = .ok old) : ∃ result, h.write a value = .ok result := by
  obtain ⟨old, hr⟩ := ha
  cases hc : h.cells a with
  | none => simp [Heap.read, hc] at hr
  | some v => simp [Heap.write, hc]

private theorem write_readable (h result : ScalarMemory) (a b : Addr) (value : JF)
    (hw : h.write a value = .ok result)
    (hb : ∃ old, h.read b = .ok old) : ∃ v, result.read b = .ok v := by
  by_cases he : b = a
  · subst b
    exact ⟨value, Heap.read_write_same h result a value hw⟩
  · obtain ⟨old, hr⟩ := hb
    exact ⟨old, (Heap.read_write_other h result a b value hw he).trans hr⟩

private theorem array_exists (h : ScalarMemory) (dest input : ScalarView)
    (hlen : dest.length = input.length)
    (ha : ∀ a ∈ dest ++ input, ∃ v, h.read a = .ok v) :
    ∃ result, setArrayView h dest input = .ok result := by
  induction dest generalizing h input with
  | nil => exact ⟨h, rfl⟩
  | cons d ds ih =>
    cases input with
    | nil => simp at hlen
    | cons x xs =>
      obtain ⟨v, hx⟩ := ha x (by simp)
      obtain ⟨h₁, hd⟩ := write_exists h d v (ha d (by simp))
      obtain ⟨result, ht⟩ := ih h₁ xs (by simpa using hlen)
        (by intro a ham; apply write_readable h h₁ d a v hd;
            apply ha a
            rcases List.mem_append.mp ham with hm | hi
            · exact List.mem_append_left _ (List.mem_cons_of_mem d hm)
            · exact List.mem_append_right _ (List.mem_cons_of_mem x hi))
      exact ⟨result, by simp [setArrayView, hx, hd, ht]⟩

/-- Initially allocated cells suffice for successful array updates, even with
arbitrary overlapping views. -/
def ParameterSetterSucceedsCompanion : Prop :=
  ∀ (h : ScalarMemory) (dest input : ScalarView),
    dest.length = input.length →
    (∀ a ∈ dest ++ input, ∃ v, h.read a = .ok v) →
    ∃ result, setArrayView h dest input = .ok result

theorem parameterSetterSucceedsCompanion_proven : ParameterSetterSucceedsCompanion :=
  array_exists

private theorem readView_exists (h : ScalarMemory) (refs : ScalarView)
    (ha : ∀ a ∈ refs, ∃ v, h.read a = .ok v) :
    ∃ values, readView h refs = .ok values ∧ values.length = refs.length := by
  induction refs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a refs ih =>
    obtain ⟨v, hr⟩ := ha a (by simp)
    obtain ⟨vs, ht, hl⟩ := ih (by intro b hb; exact ha b (by simp [hb]))
    change refs.mapM h.read = .ok vs at ht
    exact ⟨v :: vs, by simp [readView, List.mapM_cons, hr, ht], by simp [hl]⟩

example : ∀ a ∈ ([0, 1] ++ [1, 1] : ScalarView),
    ∃ v, aliasMemory.read a = .ok v := by
  intro a ha
  simp at ha
  rcases ha with rfl | rfl
  · exact ⟨.fin 10, rfl⟩
  · exact ⟨.fin 20, rfl⟩

private theorem readable_iff_cells (h : ScalarMemory) (a : Addr) :
    (∃ v, h.read a = .ok v) ↔ (∃ v, h.cells a = some v) := by
  cases hc : h.cells a <;> simp [Heap.read, hc]

private theorem structured_exists (h : ScalarMemory)
    (members : List ScalarView) (input : ScalarView)
    (hlen : members.flatten.length = input.length)
    (ha : ∀ a ∈ members.flatten ++ input, ∃ v, h.read a = .ok v) :
    ∃ result, setStructuredViews h members input = .ok result := by
  induction members generalizing h input with
  | nil => exact ⟨h, rfl⟩
  | cons dest members ih =>
    have enough : ¬ input.length < dest.length := by
      simp only [List.flatten_cons, List.length_append] at hlen
      omega
    obtain ⟨values, hr, hv⟩ := readView_exists h (input.take dest.length)
      (by intro a ham; exact ha a (List.mem_append_right _ (List.mem_of_mem_take ham)))
    obtain ⟨h₁, hd⟩ := writeConstants_exists h dest values
      (by intro a ham; apply (readable_iff_cells h a).mp;
          exact ha a (by simp [ham]))
      (by rw [hv, List.length_take]; omega)
    obtain ⟨result, ht⟩ := ih h₁ (input.drop dest.length)
      (by simp only [List.length_drop, List.flatten_cons, List.length_append] at *; omega)
      (by intro a ham; apply (readable_iff_cells h₁ a).mpr;
          apply writeConstants_allocated h h₁ dest values hd a;
          apply (readable_iff_cells h a).mp; apply ha a;
          rcases List.mem_append.mp ham with hm | hi
          · simp [hm]
          · exact List.mem_append_right _ (List.mem_of_mem_drop hi))
    exact ⟨result, by simp [setStructuredViews, enough, hr, hd, ht]⟩

/-- Exact input size and allocated source/destination cells suffice for
structured updates to succeed, with arbitrary aliasing. -/
def StructuredSetterSucceedsCompanion : Prop :=
  ∀ (h : ScalarMemory) (members : List ScalarView) (input : ScalarView),
    members.flatten.length = input.length →
    (∀ a ∈ members.flatten ++ input, ∃ v, h.read a = .ok v) →
    ∃ result, setStructuredViews h members input = .ok result

theorem structuredSetterSucceedsCompanion_proven : StructuredSetterSucceedsCompanion :=
  structured_exists

example : ([[0, 1]] : List ScalarView).flatten.length = ([1, 0] : ScalarView).length ∧
    (∀ a ∈ ([[0, 1]] : List ScalarView).flatten ++ [1, 0],
      ∃ v, aliasMemory.read a = .ok v) := by
  refine ⟨rfl, ?_⟩
  intro a ha
  simp at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨.fin 10, rfl⟩
  · exact ⟨.fin 20, rfl⟩
  · exact ⟨.fin 10, rfl⟩

/-- An input sharing no memory with the destination has no write-before-read hazard. -/
private theorem noOverlap_arrayOrder :
    ∀ (dest input : ScalarView), NoOverlap input dest → SafeArrayReadOrder dest input
  | [], _, _ => by simp [SafeArrayReadOrder]
  | _ :: _, [], _ => by simp [SafeArrayReadOrder]
  | d :: ds, x :: xs, h => by
    unfold SafeArrayReadOrder
    refine ⟨fun hd => h d (by simp [hd]) (by simp), ?_⟩
    exact noOverlap_arrayOrder ds xs
      (fun p hp hpd => h p (by simp [hp]) (by simp [hpd]))

private theorem noOverlap_structuredOrder :
    ∀ (members : List ScalarView) (input : ScalarView),
      NoOverlap input members.flatten → SafeStructuredReadOrder members input
  | [], _, _ => by simp [SafeStructuredReadOrder]
  | dest :: ms, input, h => by
    unfold SafeStructuredReadOrder
    refine ⟨fun p hp hpi => h p (List.mem_of_mem_drop hpi)
      (by rw [List.flatten_cons]; exact List.mem_append_left _ hp), ?_⟩
    exact noOverlap_structuredOrder ms (input.drop dest.length)
      (fun p hp hpf => h p (List.mem_of_mem_drop hp)
        (by rw [List.flatten_cons]; exact List.mem_append_right _ hpf))

theorem parameterOverlappingInput_proven : ParameterOverlappingInputSafe := by
  intro h dest input hn hlen hno ha
  obtain ⟨result, hr⟩ := array_exists h dest input hlen.symm ha
  rw [hr]
  exact safe_array_set h result dest input hn hlen.symm (noOverlap_arrayOrder dest input hno) hr

theorem structuredOverlappingInput_proven : StructuredOverlappingInputSafe := by
  intro h members input hn hlen hno ha
  obtain ⟨result, hr⟩ := structured_exists h members input hlen.symm ha
  rw [hr]
  exact safe_structured_set h result members input hn hlen.symm
    (noOverlap_structuredOrder members input hno) hr

/-- The Julia reproducer's reversed view overlaps the parameters, so it lies
outside the documented precondition. -/
example : ¬ NoOverlap ([1, 0] : ScalarView) [0, 1] := by
  intro ho
  exact ho 1 (by simp) (by simp)

end DynExpr.ParamStruct
