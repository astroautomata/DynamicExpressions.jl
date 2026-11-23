import DynExpr.Runtime.Heap

namespace DynExpr.Expressions.Aliasing

/-- Numeric array elements or references to nested mutable arrays. This models
numeric vectors and arrays-of-arrays stored as arbitrary metadata,
src/Expression.jl:42-49 on origin/master. -/
inductive Atom where
  | number (value : Nat)
  | reference (address : Addr)
  deriving DecidableEq, Repr
abbrev Memory := Heap (List Atom)

/-- Numbers are the model's only isbits array elements: `deepcopy` keeps them
and recurses into references, Julia base/deepcopy.jl:114-116. -/
def Atom.isNumber : Atom → Bool
  | .number _ => true
  | .reference _ => false

theorem no_reference_of_all {values : List Atom} (h : values.all Atom.isNumber = true)
    (r : Addr) : Atom.reference r ∉ values := by
  intro hr
  have := List.all_eq_true.mp h _ hr
  simp [Atom.isNumber] at this

theorem all_isNumber_map (values : List Nat) : (values.map Atom.number).all Atom.isNumber = true := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [Atom.isNumber, ih]

theorem heap_alloc_next {α : Type} (memory : Heap α) (value : α) :
    (memory.alloc value).2.next = memory.next + 1 := rfl
theorem heap_alloc_cells {α : Type} (memory : Heap α) (value : α) (a : Addr) :
    (memory.alloc value).2.cells a = if a = memory.next then some value else memory.cells a := rfl
theorem heap_write_next {α : Type} {memory memory' : Heap α} {a : Addr} {value : α}
    (h : memory.write a value = .ok memory') : memory'.next = memory.next := by
  unfold Heap.write at h
  split at h
  · cases h
  · cases h; rfl
theorem heap_write_cells {α : Type} {memory memory' : Heap α} {a : Addr} {value : α}
    (h : memory.write a value = .ok memory') (b : Addr) :
    memory'.cells b = if b = a then some value else memory.cells b := by
  unfold Heap.write at h
  split at h
  · cases h
  · cases h; rfl
theorem heap_write_of_cells {α : Type} (memory : Heap α) (a : Addr) (value old : α)
    (h : memory.cells a = some old) : ∃ memory', memory.write a value = .ok memory' := by
  simp [Heap.write, h]
theorem heap_read_lt {α : Type} {memory : Heap α} {a : Addr} {value : α}
    (h : memory.read a = .ok value) : a < memory.next := by
  apply Nat.lt_of_not_le
  intro high
  simp [Heap.read, memory.fresh a high] at h

/-- Allocation extends the address space and leaves every old cell unchanged. -/
def MemoryFrame (before after : Memory) : Prop :=
  before.next ≤ after.next ∧ ∀ a, a < before.next → after.cells a = before.cells a

theorem MemoryFrame.refl (memory : Memory) : MemoryFrame memory memory :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩
theorem MemoryFrame.trans {first middle last : Memory}
    (h : MemoryFrame first middle) (k : MemoryFrame middle last) : MemoryFrame first last :=
  ⟨Nat.le_trans h.1 k.1, fun a ha => (k.2 a (Nat.lt_of_lt_of_le ha h.1)).trans (h.2 a ha)⟩
theorem MemoryFrame.alloc (memory : Memory) (values : List Atom) :
    MemoryFrame memory (memory.alloc values).2 := by
  refine ⟨by simp [Heap.alloc], ?_⟩
  intro a ha
  simp [Heap.alloc, Nat.ne_of_lt ha]
theorem MemoryFrame.read {before after : Memory} (frame : MemoryFrame before after)
    {a : Addr} (low : a < before.next) : after.read a = before.read a := by
  unfold Heap.read
  rw [frame.2 a low]

/-- Memory and the identity dictionary of one `deepcopy` call, Julia
base/deepcopy.jl:27-29, restricted to arrays: source identities paired with
their copies, most recently recorded first. -/
abbrev DeepCopyState := Memory × List (Addr × Addr)

/-- The element loop of `_deepcopy_memory_t`, Julia base/deepcopy.jl:110-120:
elements are visited left to right; isbits elements are kept and every reference
is copied by the recursive `deepcopy_internal`, here `copyReference`. -/
def copyAtomsWith (copyReference : Addr → DeepCopyState → Jl (Addr × DeepCopyState)) :
    List Atom → DeepCopyState → Jl (List Atom × DeepCopyState)
  | [], state => .ok ([], state)
  | .number n :: atoms, state =>
    match copyAtomsWith copyReference atoms state with
    | .error e => .error e
    | .ok (rest, state') => .ok (.number n :: rest, state')
  | .reference r :: atoms, state =>
    match copyReference r state with
    | .error e => .error e
    | .ok (r', middle) =>
      match copyAtomsWith copyReference atoms middle with
      | .error e => .error e
      | .ok (rest, state') => .ok (.reference r' :: rest, state')

/-- Allocate the destination and record it before copying any element,
`dest = typeof(x)(undef, length(x)); stackdict[x] = dest`, Julia
base/deepcopy.jl:106-107,127. Its unassigned entries are modelled as an empty
list: nothing reads the destination before it is written. -/
def reserveDestination (state : DeepCopyState) (source : Addr) : DeepCopyState :=
  ((state.1.alloc []).2, (source, state.1.next) :: state.2)

/-- `deepcopy_internal(::Array)` and `_deepcopy_memory_t`, Julia
base/deepcopy.jl:95-131 (the array header and its memory are one object here):
a recorded source returns its recorded copy; an isbits element type gets
`copy(x)`, recorded; otherwise the destination is reserved, every element is
copied with the shared identity dictionary, and the destination is written. The
per-element stores of base/deepcopy.jl:117-118 are one write after the loop,
which is unobservable because the loop never reads the destination. Fuel bounds
the recursion depth; `copyArray` supplies enough (see `deepCopyArray_success`). -/
def deepCopyArray : Nat → Addr → DeepCopyState → Jl (Addr × DeepCopyState)
  | 0, _, _ => .error (.undefinedBehavior "insufficient deepcopy fuel")
  | fuel + 1, source, state =>
    match state.2.find? (fun pair => pair.1 == source) with
    | some pair => .ok (pair.2, state)
    | none =>
      match state.1.read source with
      | .error e => .error e
      | .ok values =>
        if values.all Atom.isNumber then
          .ok (state.1.next, ((state.1.alloc values).2, (source, state.1.next) :: state.2))
        else
          match copyAtomsWith (deepCopyArray fuel) values (reserveDestination state source) with
          | .error e => .error e
          | .ok (values', state') =>
            match state'.1.write state.1.next values' with
            | .error e => .error e
            | .ok written => .ok (state.1.next, (written, state'.2))

/-- `_copy(x::AbstractArray) = _is_static(eltype(x)) ? copy(x) : deepcopy(x)`,
src/Expression.jl:43 and src/Utils.jl:32-55 on origin/master. The model
identifies a static element type with "every element is a number"; this is
observably equivalent because `copy` and `deepcopy` agree on such arrays. Each
call starts a fresh identity dictionary, Julia base/deepcopy.jl:29. -/
def copyArray (source : Addr) (memory : Memory) : Jl (Addr × Memory) :=
  match memory.read source with
  | .error e => .error e
  | .ok values =>
    if values.all Atom.isNumber then .ok (memory.alloc values)
    else
      match deepCopyArray (memory.next + 1) source (memory, []) with
      | .error e => .error e
      | .ok (copied, state) => .ok (copied, state.1)

theorem copyArray_numbers (memory : Memory) (source : Addr) (values : List Nat)
    (h : memory.read source = .ok (values.map Atom.number)) :
    copyArray source memory = .ok (memory.alloc (values.map Atom.number)) := by
  simp only [copyArray, h, if_pos (all_isNumber_map values)]

theorem copyAtomsWith_numbers (copyReference : Addr → DeepCopyState → Jl (Addr × DeepCopyState))
    (atoms : List Atom) (state : DeepCopyState) (h : atoms.all Atom.isNumber = true) :
    copyAtomsWith copyReference atoms state = .ok (atoms, state) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
    cases atom with
    | number n =>
      have tail : atoms.all Atom.isNumber = true := by simpa [Atom.isNumber] using h
      simp [copyAtomsWith, ih tail]
    | reference r => simp [Atom.isNumber] at h

/-- Every array allocated at or above `floor` references only arrays allocated
at or above `floor`. -/
def OwnedAbove (floor : Nat) (memory : Memory) : Prop :=
  ∀ a values, floor ≤ a → memory.cells a = some values →
    ∀ r, Atom.reference r ∈ values → floor ≤ r

/-- Invariant of one deep copy started when the memory ended at `floor`:
recorded copies and every newly allocated array lie at or above `floor`. -/
def DeepInvariant (floor : Nat) (state : DeepCopyState) : Prop :=
  floor ≤ state.1.next ∧
  (∀ pair, pair ∈ state.2 → floor ≤ pair.2 ∧ pair.2 < state.1.next) ∧
  OwnedAbove floor state.1

theorem ownedAbove_next (memory : Memory) : OwnedAbove memory.next memory := by
  intro a values ha hc
  rw [memory.fresh a ha] at hc
  cases hc

theorem deepInvariant_start (memory : Memory) : DeepInvariant memory.next (memory, []) :=
  ⟨Nat.le_refl _, ⟨by intro pair h; simp at h, ownedAbove_next memory⟩⟩

theorem deepInvariant_reserve (floor : Nat) (state : DeepCopyState) (source : Addr)
    (h : DeepInvariant floor state) : DeepInvariant floor (reserveDestination state source) := by
  obtain ⟨low, memo, owned⟩ := h
  refine ⟨Nat.le_trans low (Nat.le_succ _), ?_, ?_⟩
  · intro pair hp
    simp only [reserveDestination, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨low, Nat.lt_succ_self _⟩
    · have bound := memo pair hp
      exact ⟨bound.1, Nat.lt_succ_of_lt bound.2⟩
  · intro a values ha hc r hr
    change (state.1.alloc []).2.cells a = some values at hc
    rw [heap_alloc_cells] at hc
    split at hc
    · cases hc; cases hr
    · exact owned a values ha hc r hr

/-- Every successful loop step preserves an invariant, extends memory, and
returns a reference satisfying `Q`; then so does the whole element loop. -/
theorem copyAtomsWith_preserves (copyReference : Addr → DeepCopyState → Jl (Addr × DeepCopyState))
    (I : DeepCopyState → Prop) (Q : Addr → Prop)
    (step : ∀ a state r state', I state → copyReference a state = .ok (r, state') →
      MemoryFrame state.1 state'.1 ∧ I state' ∧ Q r) :
    ∀ (atoms : List Atom) (state state' : DeepCopyState) (out : List Atom), I state →
      copyAtomsWith copyReference atoms state = .ok (out, state') →
      MemoryFrame state.1 state'.1 ∧ I state' ∧ ∀ r, Atom.reference r ∈ out → Q r := by
  intro atoms
  induction atoms with
  | nil =>
    intro state state' out hi h
    simp only [copyAtomsWith, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨MemoryFrame.refl _, hi, fun _ hr => nomatch hr⟩
  | cons atom atoms ih =>
    intro state state' out hi h
    cases atom with
    | number n =>
      simp only [copyAtomsWith] at h
      cases hc : copyAtomsWith copyReference atoms state with
      | error e => simp [hc] at h
      | ok result =>
        obtain ⟨rest, last⟩ := result
        simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨frame, inv, refs⟩ := ih state last rest hi hc
        refine ⟨frame, inv, ?_⟩
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with hr | hr
        · cases hr
        · exact refs r hr
    | reference a =>
      simp only [copyAtomsWith] at h
      cases hs : copyReference a state with
      | error e => simp [hs] at h
      | ok result =>
        obtain ⟨copied, middle⟩ := result
        simp only [hs] at h
        cases hc : copyAtomsWith copyReference atoms middle with
        | error e => simp [hc] at h
        | ok result =>
          obtain ⟨rest, last⟩ := result
          simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨headFrame, headInv, headQ⟩ := step a state copied middle hi hs
          obtain ⟨frame, inv, refs⟩ := ih middle last rest headInv hc
          refine ⟨headFrame.trans frame, inv, ?_⟩
          intro r hr
          simp only [List.mem_cons] at hr
          rcases hr with hr | hr
          · cases hr; exact headQ
          · exact refs r hr

/-- If every step succeeds from invariant states on references satisfying `P`,
the element loop succeeds. -/
theorem copyAtomsWith_success (copyReference : Addr → DeepCopyState → Jl (Addr × DeepCopyState))
    (I : DeepCopyState → Prop) (P : Addr → Prop)
    (step : ∀ a state, I state → P a →
      ∃ r state', copyReference a state = .ok (r, state') ∧ I state') :
    ∀ (atoms : List Atom) (state : DeepCopyState), I state →
      (∀ r, Atom.reference r ∈ atoms → P r) →
      ∃ out state', copyAtomsWith copyReference atoms state = .ok (out, state') ∧ I state' := by
  intro atoms
  induction atoms with
  | nil => intro state hi _; exact ⟨[], state, rfl, hi⟩
  | cons atom atoms ih =>
    intro state hi refs
    have tail : ∀ r, Atom.reference r ∈ atoms → P r :=
      fun r hr => refs r (List.mem_cons_of_mem _ hr)
    cases atom with
    | number n =>
      obtain ⟨out, last, hc, inv⟩ := ih state hi tail
      exact ⟨.number n :: out, last, by simp [copyAtomsWith, hc], inv⟩
    | reference a =>
      obtain ⟨copied, middle, hs, headInv⟩ := step a state hi (refs a List.mem_cons_self)
      obtain ⟨out, last, hc, inv⟩ := ih middle headInv tail
      exact ⟨.reference copied :: out, last, by simp [copyAtomsWith, hs, hc], inv⟩

/-- Every successful deep copy extends memory, records only copies at or above
`floor`, and allocates only arrays that reference arrays at or above `floor`. -/
theorem deepCopyArray_invariant (floor : Nat) :
    ∀ (fuel : Nat) (source : Addr) (state state' : DeepCopyState) (copied : Addr),
      DeepInvariant floor state → deepCopyArray fuel source state = .ok (copied, state') →
      MemoryFrame state.1 state'.1 ∧ DeepInvariant floor state' ∧
        floor ≤ copied ∧ copied < state'.1.next := by
  intro fuel
  induction fuel with
  | zero => intro source state state' copied _ h; simp [deepCopyArray] at h
  | succ fuel ih =>
    intro source state state' copied hi h
    simp only [deepCopyArray] at h
    cases hf : state.2.find? (fun pair => pair.1 == source) with
    | some pair =>
      simp only [hf, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨low, high⟩ := hi.2.1 pair (List.mem_of_find?_eq_some hf)
      exact ⟨MemoryFrame.refl _, hi, low, high⟩
    | none =>
      simp only [hf] at h
      cases hr : state.1.read source with
      | error e => simp [hr] at h
      | ok values =>
        simp only [hr] at h
        obtain ⟨low, memo, owned⟩ := hi
        by_cases hall : values.all Atom.isNumber = true
        · rw [if_pos hall] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨MemoryFrame.alloc _ _, ⟨Nat.le_trans low (Nat.le_succ _), ?_, ?_⟩,
            low, Nat.lt_succ_self _⟩
          · intro pair hp
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact ⟨low, Nat.lt_succ_self _⟩
            · have bound := memo pair hp
              exact ⟨bound.1, Nat.lt_succ_of_lt bound.2⟩
          · intro a vs ha hc r hrv
            change (state.1.alloc values).2.cells a = some vs at hc
            rw [heap_alloc_cells] at hc
            split at hc
            · cases hc; exact absurd hrv (no_reference_of_all hall r)
            · exact owned a vs ha hc r hrv
        · rw [if_neg hall] at h
          cases hc : copyAtomsWith (deepCopyArray fuel) values (reserveDestination state source) with
          | error e => simp [hc] at h
          | ok result =>
            obtain ⟨values', middle⟩ := result
            simp only [hc] at h
            cases hw : middle.1.write state.1.next values' with
            | error e => simp [hw] at h
            | ok written =>
              simp only [hw, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨loopFrame, ⟨_, memo2, owned2⟩, loopRefs⟩ :=
                copyAtomsWith_preserves (deepCopyArray fuel) (DeepInvariant floor) (fun r => floor ≤ r)
                  (fun a s r s' hs hrun =>
                    let ⟨f, i, l, _⟩ := ih a s s' r hs hrun
                    ⟨f, i, l⟩)
                  values _ middle values' (deepInvariant_reserve floor state source ⟨low, memo, owned⟩) hc
              have hnext := heap_write_next hw
              have grow : state.1.next + 1 ≤ middle.1.next := loopFrame.1
              refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, low, ?_⟩
              · show state.1.next ≤ written.next
                omega
              · intro a ha
                show written.cells a = state.1.cells a
                rw [heap_write_cells hw, if_neg (Nat.ne_of_lt ha), loopFrame.2 a (Nat.lt_succ_of_lt ha)]
                change (state.1.alloc []).2.cells a = state.1.cells a
                rw [heap_alloc_cells, if_neg (Nat.ne_of_lt ha)]
              · show floor ≤ written.next
                omega
              · intro pair hp
                have bound := memo2 pair hp
                show floor ≤ pair.2 ∧ pair.2 < written.next
                exact ⟨bound.1, by rw [hnext]; exact bound.2⟩
              · intro a vs ha hcell r hrv
                change written.cells a = some vs at hcell
                rw [heap_write_cells hw] at hcell
                split at hcell
                · cases hcell; exact loopRefs r hrv
                · exact owned2 a vs ha hcell r hrv
              · show state.1.next < written.next
                omega

/-- Number of addresses below the bound that are not yet recorded sources. -/
def missingKeys (keys : List Addr) : Nat → Nat
  | 0 => 0
  | n + 1 => missingKeys keys n + if n ∈ keys then 0 else 1

theorem missingKeys_le (keys : List Addr) : ∀ n, missingKeys keys n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have ih := missingKeys_le keys n
    simp only [missingKeys]
    split <;> omega

theorem missingKeys_mono {keys keys' : List Addr} (h : ∀ k, k ∈ keys → k ∈ keys') :
    ∀ n, missingKeys keys' n ≤ missingKeys keys n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have ih := missingKeys_mono h n
    simp only [missingKeys]
    by_cases hk : n ∈ keys
    · rw [if_pos hk, if_pos (h n hk)]; omega
    · rw [if_neg hk]; split <;> omega

theorem missingKeys_insert_low (a : Nat) (keys : List Nat) :
    ∀ n : Nat, n ≤ a → missingKeys (a :: keys) n = missingKeys keys n
  | 0, _ => rfl
  | n + 1, h => by
    have ih := missingKeys_insert_low a keys n (Nat.le_of_succ_le h)
    have iff : n ∈ a :: keys ↔ n ∈ keys := by
      have hne : n ≠ a := Nat.ne_of_lt (Nat.lt_of_succ_le h)
      simp [hne]
    simp only [missingKeys, ih]
    by_cases hk : n ∈ keys
    · rw [if_pos (iff.mpr hk), if_pos hk]
    · rw [if_neg (fun h' => hk (iff.mp h')), if_neg hk]

theorem missingKeys_insert (a : Nat) (keys : List Nat) (hnot : a ∉ keys) :
    ∀ n : Nat, a < n → missingKeys (a :: keys) n + 1 = missingKeys keys n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [missingKeys]
    by_cases ha : a = n
    · subst ha
      rw [missingKeys_insert_low a keys a (Nat.le_refl _), if_pos List.mem_cons_self, if_neg hnot]
    · have ih := missingKeys_insert a keys hnot n (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) ha)
      have iff : n ∈ a :: keys ↔ n ∈ keys := by
        have hne : n ≠ a := fun e => ha e.symm
        simp [hne]
      by_cases hk : n ∈ keys
      · rw [if_pos (iff.mpr hk), if_pos hk]; omega
      · rw [if_neg (fun h' => hk (iff.mp h')), if_neg hk]; omega

/-- All arrays satisfying `P` are allocated and reference only arrays
satisfying `P`. -/
def ClosedAllocated (memory : Memory) (P : Addr → Prop) : Prop :=
  ∀ a, P a → ∃ values, memory.read a = .ok values ∧ ∀ r, Atom.reference r ∈ values → P r

theorem closedAllocated_frame {memory memory' : Memory} {P : Addr → Prop}
    (closed : ClosedAllocated memory P) (frame : MemoryFrame memory memory') :
    ClosedAllocated memory' P := by
  intro a ha
  obtain ⟨values, hr, refs⟩ := closed a ha
  exact ⟨values, by rw [frame.read (heap_read_lt hr)]; exact hr, refs⟩

/-- Fuel sufficiency: a call with fuel `f` that misses the identity dictionary
records its source, which is allocated in `source` and hence below
`source.next`, so every nested call sees one fewer unrecorded address below
`source.next`. Fuel exceeding that count therefore never runs out. -/
theorem deepCopyArray_success (source : Memory) (P : Addr → Prop)
    (closed : ClosedAllocated source P) :
    ∀ (fuel : Nat) (a : Addr) (state : DeepCopyState),
      DeepInvariant source.next state → MemoryFrame source state.1 → P a →
      missingKeys (state.2.map Prod.fst) source.next + 1 ≤ fuel →
      ∃ copied state', deepCopyArray fuel a state = .ok (copied, state') ∧
        DeepInvariant source.next state' ∧ MemoryFrame source state'.1 ∧
        ∀ k, k ∈ state.2.map Prod.fst → k ∈ state'.2.map Prod.fst := by
  intro fuel
  induction fuel with
  | zero => intro a state _ _ _ h; omega
  | succ fuel ih =>
    intro a state hi frame ha budget
    cases hf : state.2.find? (fun pair => pair.1 == a) with
    | some pair =>
      exact ⟨pair.2, state, by simp only [deepCopyArray, hf], hi, frame, fun _ hk => hk⟩
    | none =>
      obtain ⟨values, hsrc, refs⟩ := closed a ha
      have low := heap_read_lt hsrc
      have hr : state.1.read a = .ok values := by rw [frame.read low]; exact hsrc
      have hnot : a ∉ state.2.map Prod.fst := by
        intro hmem
        obtain ⟨pair, hp, heq⟩ := List.mem_map.mp hmem
        have := List.find?_eq_none.mp hf pair hp
        simp [heq] at this
      have shrink := missingKeys_insert a _ hnot source.next low
      by_cases hall : values.all Atom.isNumber = true
      · have run : deepCopyArray (fuel + 1) a state =
            .ok (state.1.next, ((state.1.alloc values).2, (a, state.1.next) :: state.2)) := by
          simp only [deepCopyArray, hf, hr, if_pos hall]
        obtain ⟨frame', inv', _, _⟩ := deepCopyArray_invariant _ _ _ _ _ _ hi run
        exact ⟨_, _, run, inv', frame.trans frame', fun k hk => List.mem_cons_of_mem _ hk⟩
      · have reservedInv := deepInvariant_reserve source.next state a hi
        have reservedFrame : MemoryFrame source (reserveDestination state a).1 :=
          frame.trans (MemoryFrame.alloc _ _)
        have reservedKeys : (reserveDestination state a).2.map Prod.fst = a :: state.2.map Prod.fst := rfl
        obtain ⟨out, middle, hc, _, _, middleKeys⟩ :=
          copyAtomsWith_success (deepCopyArray fuel)
            (fun s => DeepInvariant source.next s ∧ MemoryFrame source s.1 ∧
              ∀ k, k ∈ (reserveDestination state a).2.map Prod.fst → k ∈ s.2.map Prod.fst) P
            (fun b s hs hb => by
              obtain ⟨sInv, sFrame, sKeys⟩ := hs
              have mono := missingKeys_mono sKeys source.next
              rw [reservedKeys] at mono
              obtain ⟨r, s', run, inv', frame', keys'⟩ := ih b s sInv sFrame hb (by omega)
              exact ⟨r, s', run, inv', frame', fun k hk => keys' k (sKeys k hk)⟩)
            values (reserveDestination state a) ⟨reservedInv, reservedFrame, fun _ hk => hk⟩ refs
        have loopFrame : MemoryFrame (reserveDestination state a).1 middle.1 :=
          (copyAtomsWith_preserves (deepCopyArray fuel) (DeepInvariant source.next) (fun _ => True)
            (fun b s r s' hs hrun =>
              let ⟨f, i, _, _⟩ := deepCopyArray_invariant _ _ _ _ _ _ hs hrun
              ⟨f, i, trivial⟩)
            values _ middle out reservedInv hc).1
        have hcell : middle.1.cells state.1.next = some [] := by
          rw [loopFrame.2 _ (Nat.lt_succ_self _)]
          change (state.1.alloc []).2.cells state.1.next = some []
          rw [heap_alloc_cells, if_pos rfl]
        obtain ⟨written, hw⟩ := heap_write_of_cells middle.1 state.1.next out [] hcell
        have run : deepCopyArray (fuel + 1) a state = .ok (state.1.next, (written, middle.2)) := by
          simp only [deepCopyArray, hf, hr, if_neg hall, hc, hw]
        obtain ⟨frame', inv', _, _⟩ := deepCopyArray_invariant _ _ _ _ _ _ hi run
        refine ⟨_, _, run, inv', frame.trans frame', fun k hk => middleKeys k ?_⟩
        rw [reservedKeys]
        exact List.mem_cons_of_mem _ hk

theorem copyArray_frame (source : Addr) (memory memory' : Memory) (copied : Addr)
    (h : copyArray source memory = .ok (copied, memory')) :
    MemoryFrame memory memory' ∧ memory.next ≤ copied ∧ copied < memory'.next ∧
      OwnedAbove memory.next memory' := by
  unfold copyArray at h
  cases hr : memory.read source with
  | error e => simp [hr] at h
  | ok values =>
    simp only [hr] at h
    by_cases hall : values.all Atom.isNumber = true
    · rw [if_pos hall] at h
      simp only [Except.ok.injEq] at h
      have e1 : copied = memory.next := (congrArg Prod.fst h).symm
      have e2 : memory' = (memory.alloc values).2 := (congrArg Prod.snd h).symm
      subst e1 e2
      refine ⟨MemoryFrame.alloc _ _, Nat.le_refl _, Nat.lt_succ_self _, ?_⟩
      intro a vs ha hc r hrv
      rw [heap_alloc_cells] at hc
      split at hc
      · cases hc; exact absurd hrv (no_reference_of_all hall r)
      · rw [memory.fresh a ha] at hc; cases hc
    · rw [if_neg hall] at h
      cases hd : deepCopyArray (memory.next + 1) source (memory, []) with
      | error e => simp [hd] at h
      | ok result =>
        obtain ⟨c, state⟩ := result
        simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨frame, ⟨_, _, owned⟩, low, high⟩ :=
          deepCopyArray_invariant _ _ _ _ _ _ (deepInvariant_start memory) hd
        exact ⟨frame, low, high, owned⟩

theorem copyArray_success (source : Addr) (memory : Memory) (P : Addr → Prop)
    (closed : ClosedAllocated memory P) (hp : P source) :
    ∃ copied memory', copyArray source memory = .ok (copied, memory') := by
  obtain ⟨values, hr, _⟩ := closed source hp
  by_cases hall : values.all Atom.isNumber = true
  · exact ⟨(memory.alloc values).1, (memory.alloc values).2,
      by simp only [copyArray, hr, if_pos hall]⟩
  · obtain ⟨c, state, run, _⟩ := deepCopyArray_success memory P closed (memory.next + 1) source
      (memory, []) (deepInvariant_start memory) (MemoryFrame.refl _) hp
      (Nat.succ_le_succ (missingKeys_le _ _))
    exact ⟨c, state.1, by simp only [copyArray, hr, if_neg hall, run]⟩

/-- `b` is reachable from `root` through reference-valued array elements. -/
inductive ArrayReach (memory : Memory) (root : Addr) : Addr → Prop
  | root : ArrayReach memory root root
  | step {a b : Addr} {values : List Atom} : ArrayReach memory root a →
      memory.read a = .ok values → Atom.reference b ∈ values → ArrayReach memory root b

/-- Every array transitively referenced from the given identities is allocated. -/
def ReachableArraysAllocated (memory : Memory) (ids : List Addr) : Prop :=
  ∀ root, root ∈ ids → ∀ a, ArrayReach memory root a → ∃ values, memory.read a = .ok values

theorem reachable_closed {memory : Memory} {ids : List Addr}
    (h : ReachableArraysAllocated memory ids) :
    ∃ P, ClosedAllocated memory P ∧ ∀ a, a ∈ ids → P a := by
  refine ⟨fun b => ∃ root, root ∈ ids ∧ ArrayReach memory root b, ?_,
    fun a ha => ⟨a, ha, .root⟩⟩
  intro b ⟨root, hroot, reach⟩
  obtain ⟨values, hread⟩ := h root hroot b reach
  exact ⟨values, hread, fun r hr => ⟨root, hroot, .step reach hread hr⟩⟩

theorem reach_flat {memory : Memory} {root : Addr} {values : List Nat}
    (h : memory.read root = .ok (values.map Atom.number)) {a : Addr}
    (reach : ArrayReach memory root a) : a = root := by
  induction reach with
  | root => rfl
  | step _ hread hb ih =>
    subst ih
    rw [h] at hread
    injection hread with hread
    subst hread
    simp at hb

end DynExpr.Expressions.Aliasing
