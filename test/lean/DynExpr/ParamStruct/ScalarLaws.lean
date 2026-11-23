import DynExpr.ParamStruct.Mirror

namespace DynExpr.ParamStruct

private theorem writeConstants_read_other (h h' : Heap JF) (refs : List Addr)
    (vs : List JF) (a : Addr) (ha : a ∉ refs)
    (hw : writeConstants h refs vs = .ok h') : h'.read a = h.read a := by
  induction refs generalizing h vs with
  | nil =>
    cases vs with
    | nil => simp [writeConstants] at hw; subst h'; rfl
    | cons v vs => simp [writeConstants] at hw
  | cons b bs ih =>
    cases vs with
    | nil => simp [writeConstants] at hw
    | cons v vs =>
      cases hb : h.write b v with
      | error err => simp [writeConstants, hb] at hw
      | ok h₁ =>
        simp only [writeConstants, hb, jl_bind_ok] at hw
        have hab : a ≠ b := by intro he; exact ha (by simp [he])
        have hat : a ∉ bs := by intro hm; exact ha (by simp [hm])
        rw [ih h₁ vs hat hw, Heap.read_write_other h h₁ b a v hb hab]

/-- Distinct mutable references read back their individually supplied values. -/
theorem writeConstants_read_values (h h' : Heap JF) (refs : List Addr)
    (vs : List JF) (hn : refs.Nodup) (hw : writeConstants h refs vs = .ok h') :
    refs.mapM h'.read = .ok vs := by
  induction refs generalizing h vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons v vs => simp [writeConstants] at hw
  | cons a as ih =>
    cases vs with
    | nil => simp [writeConstants] at hw
    | cons v vs =>
      cases ha : h.write a v with
      | error err => simp [writeConstants, ha] at hw
      | ok h₁ =>
        simp only [writeConstants, ha, jl_bind_ok] at hw
        have hnodup := List.nodup_cons.mp hn
        have hr : h'.read a = .ok v := by
          rw [writeConstants_read_other h₁ h' as vs a hnodup.1 hw]
          exact Heap.read_write_same h h₁ a v ha
        simp [List.mapM_cons, hr, ih h₁ vs hnodup.2 hw]

private theorem mapM_length {α β : Type} (xs : List α) (f : α → Jl β)
    (ys : List β) (hm : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simp at hm; subst ys; rfl
  | cons x xs ih =>
    cases hx : f x with
    | error err => simp [List.mapM_cons, hx] at hm
    | ok y =>
      cases ht : xs.mapM f with
      | error err => simp [List.mapM_cons, hx, ht] at hm
      | ok zs =>
        simp [List.mapM_cons, hx, ht] at hm
        subst ys
        simp [ih zs ht]

/-- The scalar count includes every node reference and every parameter entry. -/
theorem getConstants_length (s : ConstantState) (vs : List JF)
    (hg : getConstants s = .ok vs) :
    vs.length = s.refs.length + s.params.length := by
  cases hm : s.refs.mapM s.heap.read with
  | error err => simp [getConstants, hm] at hg
  | ok cs =>
    simp [getConstants, hm] at hg
    subst vs
    simp [mapM_length s.refs s.heap.read cs hm]

private theorem setArray_exact_length (old vs : List JF)
    (hlen : vs.length = old.length) : setArray old vs = vs := by
  induction old generalizing vs with
  | nil =>
    have he : vs = [] := by simpa using hlen
    subst vs; rfl
  | cons a old ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.length_cons] at hlen
      simp [setArray, ih vs (by omega)]

/-- An exact-size update is visible through the scalar getter. -/
theorem setConstants_read_values (s s' : ConstantState) (vs : List JF)
    (hn : s.refs.Nodup) (hlen : vs.length = s.refs.length + s.params.length)
    (hw : setConstants s vs = .ok s') : getConstants s' = .ok vs := by
  have enough : ¬ vs.length ≠ s.refs.length + s.params.length := fun h => h hlen
  rw [setConstants, if_neg enough] at hw
  cases hm : writeConstants s.heap s.refs (vs.take s.refs.length) with
  | error err => simp [hm] at hw
  | ok h' =>
    simp only [hm, jl_bind_ok, jl_pure, Except.ok.injEq] at hw
    subst s'
    have hp : (vs.drop s.refs.length).length = s.params.length := by
      simp only [List.length_drop]
      omega
    have hr := writeConstants_read_values s.heap h' s.refs
      (vs.take s.refs.length) hn hm
    simp only [getConstants, hr, jl_bind_ok, jl_pure]
    rw [setArray_exact_length s.params (vs.drop s.refs.length) hp,
      List.take_append_drop]

/-- Independent member heaps preserve all scalar values in member order. -/
private theorem setMembers_read_values (states result : List ConstantState)
    (oldGroups : List (List JF)) (vs : List JF)
    (hn : ∀ s ∈ states, s.refs.Nodup)
    (hg : states.mapM getConstants = .ok oldGroups)
    (hlen : vs.length = oldGroups.flatten.length)
    (hw : setMembers states vs = .ok result) :
    (result.mapM getConstants).map List.flatten = .ok vs := by
  induction states generalizing result oldGroups vs with
  | nil =>
    simp at hg
    subst oldGroups
    have he : vs = [] := by simpa using hlen
    subst vs
    simp [setMembers] at hw
    subst result
    rfl
  | cons s ss ih =>
    cases hs : getConstants s with
    | error err => simp [List.mapM_cons, hs] at hg
    | ok old =>
      cases ht : ss.mapM getConstants with
      | error err => simp [List.mapM_cons, hs, ht] at hg
      | ok olds =>
        simp [List.mapM_cons, hs, ht] at hg
        subst oldGroups
        have enough : ¬ vs.length < old.length := by
          simp only [List.flatten_cons, List.length_append] at hlen
          omega
        simp only [setMembers, hs, jl_bind_ok, ite_eq_right enough] at hw
        cases hu : setConstants s (vs.take old.length) with
        | error err => simp [hu] at hw
        | ok t =>
          cases hv : setMembers ss (vs.drop old.length) with
          | error err => simp [hu, hv] at hw
          | ok ts =>
            simp only [hu, hv, jl_bind_ok, jl_pure, Except.ok.injEq] at hw
            subst result
            have htake : (vs.take old.length).length =
                s.refs.length + s.params.length := by
              have hol := getConstants_length s old hs
              simp only [List.length_take]
              omega
            have hread := setConstants_read_values s t (vs.take old.length)
              (hn s (by simp)) htake hu
            have hdrop : (vs.drop old.length).length = olds.flatten.length := by
              simp only [List.length_drop, List.flatten_cons, List.length_append] at *
              omega
            have htail := ih ts olds (vs.drop old.length)
              (by intro q hq; exact hn q (by simp [hq])) ht hdrop hv
            cases hm : ts.mapM getConstants with
            | error err => simp [hm, Except.map] at htail
            | ok groups =>
              simp only [hm, Except.map, Except.ok.injEq] at htail
              simp [List.mapM_cons, hread, hm, Except.map,
                List.flatten_cons, htail, List.take_append_drop]

/-- The checked structured setter delegates to the member loop on exact input. -/
theorem setS_read_values (states result : List ConstantState)
    (oldGroups : List (List JF)) (vs : List JF)
    (hn : ∀ s ∈ states, s.refs.Nodup)
    (hg : states.mapM getConstants = .ok oldGroups)
    (hlen : vs.length = oldGroups.flatten.length)
    (hw : setS states vs = .ok result) :
    (result.mapM getConstants).map List.flatten = .ok vs := by
  have hsum : vs.length = (oldGroups.map List.length).sum := by
    rw [hlen, List.length_flatten]
  simp only [setS, hg, jl_bind_ok] at hw
  rw [if_neg (fun h => h hsum)] at hw
  exact setMembers_read_values states result oldGroups vs hn hg hlen hw

/-- Flattening retains the scalar order of arbitrary members. -/
theorem flattenS_eq (members : List (List JF)) :
    flattenS members = members.flatten := rfl

theorem flattenS_append (left right : List (List JF)) :
    flattenS (left ++ right) = flattenS left ++ flattenS right := by
  simp [flattenS]

private theorem write_preserves_allocated (h h' : Heap JF) (a b : Addr) (v : JF)
    (hw : h.write a v = .ok h') (hb : ∃ w, h.cells b = some w) :
    ∃ w, h'.cells b = some w := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw
    by_cases he : b = a
    · exact ⟨v, by simp [he]⟩
    · rcases hb with ⟨w, hb⟩
      exact ⟨w, by simp [he, hb]⟩

/-- Scalar writes retain allocation at every initially allocated address. -/
theorem writeConstants_allocated (h h' : Heap JF) (refs : List Addr) (vs : List JF)
    (hw : writeConstants h refs vs = .ok h') (a : Addr)
    (ha : ∃ v, h.cells a = some v) : ∃ v, h'.cells a = some v := by
  induction refs generalizing h vs with
  | nil =>
    cases vs with
    | nil => simp [writeConstants] at hw; subst h'; exact ha
    | cons v vs => simp [writeConstants] at hw
  | cons b refs ih =>
    cases vs with
    | nil => simp [writeConstants] at hw
    | cons v vs =>
      cases hb : h.write b v with
      | error err => simp [writeConstants, hb] at hw
      | ok h₁ =>
        simp only [writeConstants, hb, jl_bind_ok] at hw
        exact ih h₁ vs hw (write_preserves_allocated h h₁ b a v hb ha)

/-- Allocated references accept every exact-size scalar sequence, including aliases. -/
theorem writeConstants_exists (h : Heap JF) (refs : List Addr) (vs : List JF)
    (ha : ∀ a ∈ refs, ∃ v, h.cells a = some v)
    (hlen : vs.length = refs.length) :
    ∃ h', writeConstants h refs vs = .ok h' := by
  induction refs generalizing h vs with
  | nil =>
    have he : vs = [] := by simpa using hlen
    subst vs
    exact ⟨h, rfl⟩
  | cons a refs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      rcases ha a (by simp) with ⟨old, ha₀⟩
      have hex : ∃ h₁, h.write a v = .ok h₁ := by
        unfold Heap.write
        simp only [ha₀, reduceCtorEq, dite_false]
        exact ⟨_, rfl⟩
      rcases hex with ⟨h₁, hw⟩
      have halloc : ∀ b ∈ refs, ∃ w, h₁.cells b = some w := by
        intro b hb
        exact write_preserves_allocated h h₁ a b v hw (ha b (by simp [hb]))
      rcases ih h₁ vs halloc (by simpa using hlen) with ⟨h', ht⟩
      exact ⟨h', by simp [writeConstants, hw, ht]⟩

private theorem mapM_exists {α β : Type} (xs : List α) (f : α → Jl β)
    (hf : ∀ x ∈ xs, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    rcases hf x (by simp) with ⟨y, hy⟩
    rcases ih (by intro z hz; exact hf z (by simp [hz])) with ⟨ys, hys⟩
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Reading allocated references always yields their values and the parameters. -/
theorem getConstants_exists (s : ConstantState)
    (ha : ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v) :
    ∃ vs, getConstants s = .ok vs := by
  have hf : ∀ a ∈ s.refs, ∃ v, s.heap.read a = .ok v := by
    intro a hm
    rcases ha a hm with ⟨v, hv⟩
    exact ⟨v, by simp [Heap.read, hv]⟩
  rcases mapM_exists s.refs s.heap.read hf with ⟨cs, hc⟩
  exact ⟨cs ++ s.params, by simp [getConstants, hc]⟩

/-- Exact-size updates succeed whenever the initial references are allocated. -/
theorem setConstants_exists (s : ConstantState) (vs : List JF)
    (ha : ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v)
    (hlen : vs.length = s.refs.length + s.params.length) :
    ∃ result, setConstants s vs = .ok result := by
  have enough : ¬ vs.length ≠ s.refs.length + s.params.length := fun h => h hlen
  have ht : (vs.take s.refs.length).length = s.refs.length := by
    simp only [List.length_take]
    omega
  rcases writeConstants_exists s.heap s.refs (vs.take s.refs.length) ha ht with ⟨h', hw⟩
  exact ⟨{s with heap := h', params := setArray s.params (vs.drop s.refs.length)},
    by rw [setConstants, if_neg enough, hw]; rfl⟩

/-- Every independent member can be read when its initial references are allocated. -/
theorem getConstants_members_exists (states : List ConstantState)
    (ha : ∀ s ∈ states, ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v) :
    ∃ groups, states.mapM getConstants = .ok groups := by
  exact mapM_exists states getConstants (by intro s hs; exact getConstants_exists s (ha s hs))

/-- The getter's per-member counts sum to the members' reference and parameter counts. -/
private theorem members_count (states : List ConstantState) (olds : List (List JF))
    (hg : states.mapM getConstants = .ok olds) :
    (olds.map List.length).sum = (states.map fun s => s.refs.length + s.params.length).sum := by
  induction states generalizing olds with
  | nil => simp at hg; subst olds; rfl
  | cons s ss ih =>
    cases hs : getConstants s with
    | error err => simp [List.mapM_cons, hs] at hg
    | ok old =>
      cases ht : ss.mapM getConstants with
      | error err => simp [List.mapM_cons, hs, ht] at hg
      | ok rest =>
        simp [List.mapM_cons, hs, ht] at hg
        subst olds
        simp only [List.map_cons, List.sum_cons, getConstants_length s old hs, ih rest ht]

/-- Independent member updates succeed for the sum of their initial scalar counts. -/
private theorem setMembers_exists (states : List ConstantState) (vs : List JF)
    (ha : ∀ s ∈ states, ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v)
    (hlen : vs.length = (states.map fun s => s.refs.length + s.params.length).sum) :
    ∃ result, setMembers states vs = .ok result := by
  induction states generalizing vs with
  | nil => exact ⟨[], rfl⟩
  | cons s ss ih =>
    rcases getConstants_exists s (ha s (by simp)) with ⟨old, hg⟩
    have hol := getConstants_length s old hg
    have hcount : vs.length = s.refs.length + s.params.length +
        (ss.map fun s => s.refs.length + s.params.length).sum := by
      simpa only [List.map_cons, List.sum_cons] using hlen
    have enough : ¬ vs.length < old.length := by omega
    have htake : (vs.take old.length).length = s.refs.length + s.params.length := by
      simp only [List.length_take]
      omega
    rcases setConstants_exists s (vs.take old.length) (ha s (by simp)) htake with ⟨t, ht⟩
    have hdrop : (vs.drop old.length).length =
        (ss.map fun s => s.refs.length + s.params.length).sum := by
      simp only [List.length_drop]
      omega
    rcases ih (vs.drop old.length) (by intro q hq; exact ha q (by simp [hq])) hdrop
      with ⟨ts, hts⟩
    exact ⟨t :: ts, by simp [setMembers, hg, enough, ht, hts]⟩

/-- The checked structured setter succeeds for the sum of the initial scalar counts. -/
theorem setS_exists (states : List ConstantState) (vs : List JF)
    (ha : ∀ s ∈ states, ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v)
    (hlen : vs.length = (states.map fun s => s.refs.length + s.params.length).sum) :
    ∃ result, setS states vs = .ok result := by
  obtain ⟨olds, hg⟩ := getConstants_members_exists states ha
  have hsum : vs.length = (olds.map List.length).sum :=
    hlen.trans (members_count states olds hg).symm
  obtain ⟨result, hr⟩ := setMembers_exists states vs ha hlen
  refine ⟨result, ?_⟩
  simp only [setS, hg, jl_bind_ok]
  rw [if_neg (fun h => h hsum)]
  exact hr

private def sampleHeap : Heap JF :=
  ((Heap.empty.alloc (.fin 10)).2.alloc (.fin 20)).2

private def sampleState : ConstantState := ⟨sampleHeap, [0, 1], [.fin 30]⟩

example : ([0, 1] : List Addr).Nodup := by decide

example : writeConstants sampleHeap [0, 1] [.fin 2, .fin 3] =
    .ok ((sampleHeap.write 0 (.fin 2)).toOption.getD sampleHeap |>.write 1 (.fin 3)
      |>.toOption.getD sampleHeap) := by rfl

example : getConstants sampleState = .ok [.fin 10, .fin 20, .fin 30] := by decide

example : ([.fin 2, .fin 3, .fin 4] : List JF).length =
    sampleState.refs.length + sampleState.params.length := rfl

example : ∃ result, setConstants sampleState [.fin 2, .fin 3, .fin 4] = .ok result := by
  exact ⟨⟨((sampleHeap.write 0 (.fin 2)).toOption.getD sampleHeap |>.write 1 (.fin 3)
    |>.toOption.getD sampleHeap), [0, 1], [.fin 4]⟩, by rfl⟩

example : ∀ s ∈ [sampleState, sampleState], s.refs.Nodup := by
  intro s hs
  have he : s = sampleState := by simpa using hs
  subst s
  decide

example : ([sampleState, sampleState].mapM getConstants) =
    .ok [[.fin 10, .fin 20, .fin 30], [.fin 10, .fin 20, .fin 30]] := by decide

example : ([.fin 1, .fin 2, .fin 3, .fin 4, .fin 5, .fin 6] : List JF).length =
    ([[.fin 10, .fin 20, .fin 30], [.fin 10, .fin 20, .fin 30]] : List (List JF)).flatten.length := rfl

example : ∃ result, setS [sampleState, sampleState]
    [.fin 1, .fin 2, .fin 3, .fin 4, .fin 5, .fin 6] = .ok result := by
  exact ⟨[⟨((sampleHeap.write 0 (.fin 1)).toOption.getD sampleHeap |>.write 1 (.fin 2)
      |>.toOption.getD sampleHeap), [0, 1], [.fin 3]⟩,
    ⟨((sampleHeap.write 0 (.fin 4)).toOption.getD sampleHeap |>.write 1 (.fin 5)
      |>.toOption.getD sampleHeap), [0, 1], [.fin 6]⟩], by rfl⟩

private theorem sample_allocated : ∀ a ∈ sampleState.refs,
    ∃ v, sampleState.heap.cells a = some v := by
  intro a ha
  have he : a = 0 ∨ a = 1 := by simpa [sampleState] using ha
  rcases he with rfl | rfl
  · exact ⟨.fin 10, rfl⟩
  · exact ⟨.fin 20, rfl⟩

example : ([.fin 2, .fin 3] : List JF).length = sampleState.refs.length := rfl

example : ∃ h', writeConstants sampleState.heap sampleState.refs [.fin 2, .fin 3] = .ok h' :=
  writeConstants_exists _ _ _ sample_allocated rfl

example : ∃ vs, getConstants sampleState = .ok vs :=
  getConstants_exists _ sample_allocated

example : ∃ result, setConstants sampleState [.fin 2, .fin 3, .fin 4] = .ok result :=
  setConstants_exists _ _ sample_allocated rfl

private theorem sample_members_allocated : ∀ s ∈ [sampleState, sampleState],
    ∀ a ∈ s.refs, ∃ v, s.heap.cells a = some v := by
  intro s hs
  have he : s = sampleState := by simpa using hs
  subst s
  exact sample_allocated

example : ∃ groups, [sampleState, sampleState].mapM getConstants = .ok groups :=
  getConstants_members_exists _ sample_members_allocated

example : ([.fin 1, .fin 2, .fin 3, .fin 4, .fin 5, .fin 6] : List JF).length =
    ([sampleState, sampleState].map fun s => s.refs.length + s.params.length).sum := rfl

example : ∃ result, setS [sampleState, sampleState]
    [.fin 1, .fin 2, .fin 3, .fin 4, .fin 5, .fin 6] = .ok result :=
  setS_exists _ _ sample_members_allocated rfl

end DynExpr.ParamStruct
