import DynExpr.Expressions.Sampling
import Init.Data.Rat.Lemmas

namespace DynExpr.Expressions.ValidWeights

open Sampling

attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- Exact finite total for the cumsum in src/Random.jl:90. -/
def total (weights : List Rat) : Rat := weights.foldl (· + ·) 0

private theorem finite_add (a b : Rat) : JF.fin a + JF.fin b = .fin (a + b) := rfl
private theorem finite_mul (a b : Rat) : JF.fin a * JF.fin b = .fin (a * b) := rfl

/-- Finite nonnegative weights pass the src/Random.jl:88-89 check. -/
private theorem valid_weights (weights : List Rat) (hw : ∀ w ∈ weights, 0 ≤ w.num) :
    (weights.map JF.fin).any invalidWeight = false := by
  rw [List.any_eq_false]
  intro x hx
  obtain ⟨w, hm, rfl⟩ := List.mem_map.mp hx
  simp only [invalidWeight, decide_eq_true_eq]
  exact Rat.not_lt.mpr (Rat.num_nonneg.mp (hw w hm))

private theorem last_cumulative (weights : List Rat) (sum : Rat) (hn : weights ≠ []) :
    (cumulativeAux (.fin sum) (weights.map JF.fin)).getLast? =
      some (.fin (weights.foldl (· + ·) sum)) := by
  induction weights generalizing sum with
  | nil => exact False.elim (hn rfl)
  | cons w ws ih =>
    cases ws with
    | nil => rfl
    | cons v vs =>
      simpa [List.map_cons, cumulativeAux, List.foldl_cons, finite_add] using
        ih (sum + w) (by simp)

private theorem cumulative_length (weights : List JF) (sum : JF) :
    (cumulativeAux sum weights).length = weights.length := by
  induction weights generalizing sum with
  | nil => rfl
  | cons w ws ih => simp [cumulativeAux, ih]

private theorem cumulative_nonnegative (weights : List Rat) (sum : Rat)
    (hw : ∀ w ∈ weights, 0 ≤ w.num) (hs : 0 ≤ sum) :
    ∀ value ∈ cumulativeAux (.fin sum) (weights.map JF.fin),
      ∃ q : Rat, value = .fin q ∧ 0 ≤ q := by
  induction weights generalizing sum with
  | nil => simp [cumulativeAux]
  | cons w ws ih =>
    have hsum : 0 ≤ sum + w := Rat.add_nonneg hs (Rat.num_nonneg.mp (hw w (by simp)))
    have htail : ∀ v ∈ ws, 0 ≤ v.num := fun v hv => hw v (by simp [hv])
    intro value hv
    change value ∈ JF.fin (sum + w) :: cumulativeAux (.fin (sum + w)) (ws.map JF.fin) at hv
    rcases List.mem_cons.mp hv with hhead | hrest
    · exact ⟨sum + w, hhead, hsum⟩
    · exact ih (sum + w) htail hsum value hrest

private theorem firstGreater_exists (r : JF) (values : List JF)
    (hex : ∃ value ∈ values, greater value r = true) :
    ∃ idx, firstGreater r values = some idx ∧ 1 ≤ idx ∧ idx ≤ values.length := by
  induction values with
  | nil => simp at hex
  | cons c cs ih =>
    by_cases hc : greater c r = true
    · exact ⟨1, by simp [firstGreater, hc], by omega, by simp⟩
    · obtain ⟨value, hv, hg⟩ := hex
      have htail : value ∈ cs := by
        rcases List.mem_cons.mp hv with he | ht
        · subst value; exact False.elim (hc hg)
        · exact ht
      obtain ⟨idx, hi, hlo, hhi⟩ := ih ⟨value, htail, hg⟩
      exact ⟨idx + 1, by simp [firstGreater, hc, hi], by omega, by simp only [List.length_cons]; omega⟩

/-- For arbitrary finite nonnegative weights with positive total, every draw in
[0,1) succeeds in src/Random.jl:87-96 and selects its cumulative interval. -/
def validWeightsProperty : Prop := ∀ (weights : List Rat) (u : Rat),
  (∀ w ∈ weights, 0 ≤ w.num) → 0 < (total weights).num →
  0 ≤ u.num → u.num < (u.den : Int) →
  ∃ (idx : Nat) (selected : Rat),
    sampleIdx (weights.map JF.fin) u = .ok idx ∧
    1 ≤ idx ∧ idx ≤ weights.length ∧
    (cumulative (weights.map JF.fin))[idx - 1]? = some (.fin selected) ∧
    0 ≤ u * total weights ∧ u * total weights < selected ∧
    (∀ k q, k < idx - 1 →
      (cumulative (weights.map JF.fin))[k]? = some (.fin q) → q ≤ u * total weights) ∧
    (∀ value ∈ cumulative (weights.map JF.fin),
      ∃ q : Rat, value = .fin q ∧ 0 ≤ q)

theorem validWeights_proven : validWeightsProperty := by
  intro weights u hw ht hu0 hu1
  have hn : weights ≠ [] := by
    intro he
    simp [total, he] at ht
  have htotal : 0 < total weights := by
    rw [Rat.lt_iff]
    simpa using ht
  have hdraw : u < 1 := by
    rw [Rat.lt_iff]
    simpa using hu1
  have hthreshold : u * total weights < total weights := by
    simpa using Rat.mul_lt_mul_of_pos_right hdraw htotal
  have hlast : (cumulative (weights.map JF.fin)).getLast? = some (.fin (total weights)) :=
    last_cumulative weights 0 hn
  have hgreater : greater (.fin (total weights)) (.fin u * .fin (total weights)) = true := by
    change decide (u * total weights < total weights) = true
    exact decide_eq_true hthreshold
  obtain ⟨idx, hi, hlo, hhi⟩ := firstGreater_exists
    (.fin u * .fin (total weights)) (cumulative (weights.map JF.fin))
    ⟨.fin (total weights), List.mem_of_getLast? hlast, hgreater⟩
  have hz : JF.fin (total weights) ≠ .fin 0 := by
    intro he
    exact Rat.ne_of_gt htotal (JF.fin.inj he)
  have hsample : sampleIdx (weights.map JF.fin) u = .ok idx := by
    simp [sampleIdx, sampleCore, valid_weights weights hw, hlast, hz, hi]
  have hbound : idx ≤ weights.length := by
    simpa [cumulative, cumulative_length] using hhi
  have hfinite := cumulative_nonnegative weights 0 hw (Rat.le_refl)
  obtain ⟨value, hget, hg⟩ := cumulative_proven (weights.map JF.fin) u idx hsample
  obtain ⟨q, hq, _⟩ := hfinite value (List.mem_of_getElem? hget)
  subst value
  have hselected : u * total weights < q := by
    simpa [hlast, finite_mul, greater] using hg
  refine ⟨idx, q, hsample, hlo, hbound, hget,
    Rat.mul_nonneg (Rat.num_nonneg.mp hu0) (Rat.le_of_lt htotal), hselected, ?_, hfinite⟩
  intro k q hk hq
  have hp := intervals_proven (weights.map JF.fin) u idx hsample k (.fin q) hk hq
  have hnot : ¬ u * total weights < q := by
    simpa [hlast, finite_mul, greater] using hp
  exact Rat.not_lt.mp hnot

example : ∃ (weights : List Rat) (u : Rat),
    (∀ w ∈ weights, 0 ≤ w.num) ∧ 0 < (total weights).num ∧
    0 ≤ u.num ∧ u.num < (u.den : Int) := by
  refine ⟨[0, 1, 2], 1 / 2, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> decide
  · decide
  · decide
  · decide

/-- The public weighted NodeSampler succeeds and preserves its filter on the
same valid input-weight domain, src/Random.jl:61-71. -/
def weightedSuccessProperty : Prop := ∀ (s : NodeSampler JF) (rng : RNG)
    (nodes : List Addr) (weighting : Addr → Rat),
  matching s = .ok nodes →
  s.weighting = some (fun a => .fin (weighting a)) →
  (∀ a ∈ nodes, 0 ≤ (weighting a).num) →
  0 < (total (nodes.map weighting)).num →
  0 ≤ (rng.draws rng.cursor).num →
  (rng.draws rng.cursor).num < ((rng.draws rng.cursor).den : Int) →
  ∃ a rng', rand s rng = (.ok a, rng') ∧ s.filter a = true ∧
    rng'.cursor = rng.cursor + 1

theorem weightedSuccess_proven : weightedSuccessProperty := by
  intro s rng nodes weighting hm hw hn ht hu0 hu1
  have hweights : ∀ w ∈ nodes.map weighting, 0 ≤ w.num := by
    intro w hmem
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
    subst w
    exact hn a ha
  obtain ⟨idx, selected, hs, _⟩ := validWeights_proven (nodes.map weighting)
    (rng.draws rng.cursor) hweights ht hu0 hu1
  have hnonempty : nodes ≠ [] := by
    intro he
    simp [total, he] at ht
  have hlast : (cumulative (nodes.map (fun a => JF.fin (weighting a)))).getLast? =
      some (.fin (total (nodes.map weighting))) := by
    simpa only [List.map_map, Function.comp_def, cumulative, total] using
      last_cumulative (nodes.map weighting) 0 (by simpa using hnonempty)
  have hzero : (cumulative (nodes.map (fun a => JF.fin (weighting a)))).getLast? ≠ some (.fin 0) := by
    rw [hlast]
    intro he
    have hz : total (nodes.map weighting) = 0 := JF.fin.inj (Option.some.inj he)
    simp [hz] at ht
  have hsample : sampleIdx (nodes.map (fun a => JF.fin (weighting a)))
      (rng.draws rng.cursor) = .ok idx := by
    simpa only [List.map_map, Function.comp_def] using hs
  have hvalid : (nodes.map (fun a => JF.fin (weighting a))).any invalidWeight = false := by
    simpa only [List.map_map, Function.comp_def] using valid_weights (nodes.map weighting) hweights
  let a := getNode s.root nodes idx
  let rng' := { rng with cursor := rng.cursor + 1 }
  have hresult : rand s rng = (.ok a, rng') := by
    cases nodes with
    | nil => exact False.elim (hnonempty rfl)
    | cons node nodes =>
      simp only [List.map_cons] at hzero hsample hvalid
      simp [rand, hm, hw, hvalid, hzero, draw, hsample, Except.map, a, rng']
  exact ⟨a, rng', hresult, returnedFilter_proven s rng rng' a hresult, rfl⟩

example : ∃ (s : NodeSampler JF) (rng : RNG) (nodes : List Addr) (w : Addr → Rat),
    matching s = .ok nodes ∧ s.weighting = some (fun a => .fin (w a)) ∧
    (∀ a ∈ nodes, 0 ≤ (w a).num) ∧ 0 < (total (nodes.map w)).num ∧
    0 ≤ (rng.draws rng.cursor).num ∧
    (rng.draws rng.cursor).num < ((rng.draws rng.cursor).den : Int) := by
  let graph : Graph JF := (Heap.empty.alloc (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF)).2
  refine ⟨{ graph := graph, root := 0, fuel := 1, weighting := some (fun _ => .fin 1) },
    { draws := fun _ => 0 }, [0], (fun _ => 1), ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro a _; change 0 ≤ (1 : Rat).num; decide
  · decide
  · decide
  · decide

end DynExpr.Expressions.ValidWeights
