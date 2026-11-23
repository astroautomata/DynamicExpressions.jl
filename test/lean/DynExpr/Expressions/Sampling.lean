import DynExpr.Expressions.Wrapper

namespace DynExpr.Expressions.Sampling

deriving instance DecidableEq for Except
attribute [local semireducible] Rat.add Rat.mul Rat.inv

/-- Abstract uniform real and range-indexed integer draw streams,
src/Random.jl:58,92. Both streams share the cursor; generator internals are absent. -/
structure RNG where
  draws : Nat → Rat
  cursor : Nat := 0
  indexDraws : (n : Nat) → Nat → Fin (n + 1) := fun n _ => ⟨0, Nat.zero_lt_succ n⟩
/-- src/Random.jl:58,92. -/
def draw (rng : RNG) : Rat × RNG :=
  (rng.draws rng.cursor, { rng with cursor := rng.cursor + 1 })
/-- All occurrences in preorder, src/base.jl:123-158,287-297 and
src/Random.jl:73-84. Fuel bounds finite acyclic graph depth. -/
def occurrences (g : Graph T) : Nat → Addr → Jl (List Addr)
  | 0, _ => .error (.undefinedBehavior "insufficient traversal fuel")
  | n + 1, a => do
    let cell ← g.read a
    let children ← cell.children.mapM (occurrences g n)
    pure (a :: children.flatten)
/-- GraphNode caching visits each identity once; regular Node and
break_sharing=true retain occurrences, src/Random.jl:16-29,54,64,78. -/
def traversal (g : Graph T) (fuel : Nat) (root : Addr)
    (preserveSharing breakSharing : Bool) : Jl (List Addr) := do
  let xs ← occurrences g fuel root
  pure (if preserveSharing && !breakSharing then xs.eraseDups else xs)

/-- src/Random.jl:31-38. A heap root allows filters and weights to inspect
actual node identity and mutable contents. Expressions first forward get_tree. -/
structure NodeSampler (T : Type) where
  graph : Graph T
  root : Addr
  fuel : Nat
  filter : Addr → Bool := fun _ => true
  weighting : Option (Addr → JF) := none
  preserveSharing : Bool := false
  breakSharing : Bool := false
/-- src/Random.jl:54,63-65. Filter precedes weighting in both branches. -/
def matching (s : NodeSampler T) : Jl (List Addr) := do
  pure ((← traversal s.graph s.fuel s.root s.preserveSharing s.breakSharing).filter s.filter)
/-- src/Random.jl:73-85. The root is the fallback if a supplied index is zero
or out of range; public sampling only supplies a valid one-based index. -/
def getNode (root : Addr) (nodes : List Addr) (idx : Nat) : Addr :=
  if idx = 0 then root else (nodes[idx - 1]?).getD root
/-- IEEE greater-than for src/Random.jl:93. NaN compares false. -/
def greater : JF → JF → Bool
  | .nan, _ | _, .nan => false
  | .fin a, .fin b => decide (b < a)
  | .posInf, .posInf | .negInf, .negInf => false
  | .posInf, _ | _, .negInf => true
  | _, .posInf | .negInf, _ => false
/-- src/Random.jl:88. Finite arithmetic uses the shared JF model; counterexample
values below are exactly representable Float64 values with no rounding. -/
def cumulativeAux (sum : JF) : List JF → List JF
  | [] => []
  | w :: ws => let sum' := sum + w; sum' :: cumulativeAux sum' ws
def cumulative (weights : List JF) := cumulativeAux (.fin 0) weights
/-- src/Random.jl:93, one-based findfirst. -/
def firstGreater (r : JF) : List JF → Option Nat
  | [] => none
  | c :: cs => if greater c r then some 1 else (firstGreater r cs).map (· + 1)
/-- src/Random.jl:88-89, `!isfinite(w) || w < 0`. -/
def invalidWeight : JF → Bool
  | .fin q => decide (q < 0)
  | _ => true
def invalidWeightsError : JlError := .argumentError "Node weights must be finite and nonnegative."
/-- src/Random.jl:90-95 after the weight check. Error strings identify the Julia
exception class where the common JlError runtime has no dedicated TypeError
constructor. -/
def sampleCore (weights : List JF) (u : Rat) : Jl Nat :=
  let sums := cumulative weights
  match sums.getLast? with
  | none => .error .boundsError
  | some total =>
    if total = .fin 0 then .error (.errorException "Cumulative weighting of nodes in tree is zero.")
    else match firstGreater (.fin u * total) sums with
      | some idx => .ok idx
      | none => .error (.userError "TypeError: findfirst result is not Int")
/-- src/Random.jl:87-96. -/
def sampleIdx (weights : List JF) (u : Rat) : Jl Nat :=
  if weights.any invalidWeight then .error invalidWeightsError else sampleCore weights u
theorem sampleIdx_ok {weights : List JF} {u : Rat} {idx : Nat}
    (h : sampleIdx weights u = .ok idx) : sampleCore weights u = .ok idx := by
  unfold sampleIdx at h
  split at h
  · cases h
  · exact h
/-- A uniform integer draw in 1:n, src/Random.jl:58. This uses the inverse-CDF
partition of [0,1); every interval has width 1/n. -/
def uniformIdx (n : Nat) (u : Rat) :=
  let q := u * (n : Rat)
  q.num.toNat / q.den + 1
/-- src/Random.jl:53-71. Empty filters, invalid weights and zero totals fail
before consuming a draw (src/Random.jl:88-93 run before the draw at line 94). -/
def rand (s : NodeSampler T) (rng : RNG) : Jl Addr × RNG :=
  match matching s with
  | .error e => (.error e, rng)
  | .ok [] => (.error (.errorException "No nodes matching filter were found."), rng)
  | .ok (a :: as) =>
    let nodes := a :: as
    match s.weighting with
    | none =>
      let idx := (rng.indexDraws as.length rng.cursor).val + 1
      (.ok (getNode s.root nodes idx), { rng with cursor := rng.cursor + 1 })
    | some weighting =>
      let weights := nodes.map weighting
      if weights.any invalidWeight then (.error invalidWeightsError, rng)
      else if (cumulative weights).getLast? = some (.fin 0) then
        (.error (.errorException "Cumulative weighting of nodes in tree is zero."), rng)
      else
        let (u, rng') := draw rng
        ((sampleIdx weights u).map (getNode s.root nodes), rng')

private theorem firstGreaterBounds (r : JF) (xs : List JF) (idx : Nat)
    (h : firstGreater r xs = some idx) : 1 ≤ idx ∧ idx ≤ xs.length := by
  induction xs generalizing idx with
  | nil => simp [firstGreater] at h
  | cons c cs ih =>
    simp only [firstGreater] at h
    split at h
    · cases h; simp
    · cases hh : firstGreater r cs with
      | none => simp [hh] at h
      | some i =>
        simp [hh] at h
        subst idx
        have hb := ih i hh
        simp only [List.length_cons]
        omega

private theorem selectedGreater (r : JF) (xs : List JF) (idx : Nat)
    (h : firstGreater r xs = some idx) :
    ∃ c, xs[idx - 1]? = some c ∧ greater c r = true := by
  induction xs generalizing idx with
  | nil => simp [firstGreater] at h
  | cons c cs ih =>
    simp only [firstGreater] at h
    split at h
    · cases h
      exact ⟨c, rfl, by assumption⟩
    · cases hh : firstGreater r cs with
      | none => simp [hh] at h
      | some i =>
        simp [hh] at h
        subst idx
        obtain ⟨v, hv, hg⟩ := ih i hh
        have hi := (firstGreaterBounds r cs i hh).1
        have hin : i = i - 1 + 1 := by omega
        have hv' : (c :: cs)[i]? = some v := by
          rw [hin, List.getElem?_cons_succ]
          exact hv
        exact ⟨v, by simpa only [Nat.add_sub_cancel] using hv', hg⟩

/-- A returned filtered traversal address passes the same pure filter. -/
def filterProperty : Prop := ∀ (s : NodeSampler JF) (xs : List Addr) (idx a : Nat),
  matching s = .ok xs → xs[idx]? = some a → s.filter a = true
 theorem filter_proven : filterProperty := by
  intro s xs idx a hm ha
  unfold matching at hm
  cases ht : traversal s.graph s.fuel s.root s.preserveSharing s.breakSharing with
  | error e => simp [ht, bind, Except.bind] at hm
  | ok ns =>
    simp [ht, bind, Except.bind, pure, Except.pure] at hm
    subst xs
    have hmem : a ∈ ns.filter s.filter := List.mem_of_getElem? ha
    exact (List.mem_filter.mp hmem).2
example : ([] : List Nat)[0]? = none := rfl

def cumulativeProperty : Prop := ∀ weights u idx,
  sampleIdx weights u = .ok idx →
  ∃ c, (cumulative weights)[idx - 1]? = some c ∧
    greater c (.fin u * (cumulative weights).getLast?.getD (.fin 0)) = true
 theorem cumulative_proven : cumulativeProperty := by
  intro weights u idx h
  have h := sampleIdx_ok h
  unfold sampleCore at h
  cases ht : (cumulative weights).getLast? with
  | none => simp [ht] at h
  | some total =>
    simp only [ht] at h
    split at h
    · cases h
    · cases hs : firstGreater (.fin u * total) (cumulative weights) with
      | none => simp [hs] at h
      | some i =>
        simp [hs] at h
        subst idx
        simpa [ht] using selectedGreater (.fin u * total) (cumulative weights) i hs

private theorem cumulative_length (weights : List JF) :
    ∀ sum, (cumulativeAux sum weights).length = weights.length := by
  induction weights with
  | nil => intro sum; rfl
  | cons w ws ih => intro sum; simp [cumulativeAux, ih]

private theorem sampleBounds (weights : List JF) (u : Rat) (idx : Nat)
    (h : sampleIdx weights u = .ok idx) : 1 ≤ idx ∧ idx ≤ weights.length := by
  have h := sampleIdx_ok h
  unfold sampleCore at h
  cases ht : (cumulative weights).getLast? with
  | none => simp [ht] at h
  | some total =>
    simp only [ht] at h
    split at h
    · cases h
    · cases hs : firstGreater (.fin u * total) (cumulative weights) with
      | none => simp [hs] at h
      | some i =>
        simp [hs] at h
        subst idx
        simpa [cumulative, cumulative_length] using firstGreaterBounds (.fin u * total) (cumulative weights) i hs

private theorem getNode_selected (root : Addr) (xs : List Addr) (idx : Nat)
    (hb : 1 ≤ idx ∧ idx ≤ xs.length) :
    ∃ a, xs[idx - 1]? = some a ∧ getNode root xs idx = a := by
  have hi : idx - 1 < xs.length := by omega
  let a := xs[idx - 1]'hi
  have hget : xs[idx - 1]? = some a := by simp [a, hi]
  exact ⟨a, hget, by simp [getNode, show idx ≠ 0 by omega, hget]⟩

/-- Public rand always returns an address that passes its filter when it returns
successfully. This includes zero, negative and nonfinite weights: a successful
weighted search still selects a matching address. -/
def returnedFilterProperty : Prop := ∀ (s : NodeSampler JF) (rng rng' : RNG) a,
  rand s rng = (.ok a, rng') → s.filter a = true
 theorem returnedFilter_proven : returnedFilterProperty := by
  intro s rng rng' a h
  unfold rand at h
  cases hm : matching s with
  | error e => simp [hm] at h
  | ok xs =>
    cases xs with
    | nil => simp [hm] at h
    | cons node nodes =>
      simp only [hm] at h
      cases hw : s.weighting with
      | none =>
        simp only [hw] at h
        let idx := (rng.indexDraws nodes.length rng.cursor).val + 1
        have hb : 1 ≤ idx ∧ idx ≤ (node :: nodes).length := by
          have := (rng.indexDraws nodes.length rng.cursor).isLt
          simp only [List.length_cons]
          dsimp [idx]
          omega
        obtain ⟨selected, hs, hg⟩ := getNode_selected s.root (node :: nodes) idx hb
        have he : getNode s.root (node :: nodes) idx = a := by
          exact Except.ok.inj (Prod.mk.inj h).1
        have hsa : selected = a := hg.symm.trans he
        exact filter_proven s (node :: nodes) (idx - 1) a hm (hs.trans (congrArg some hsa))
      | some w =>
        simp only [hw] at h
        split at h
        · cases h
        split at h
        · cases h
        · cases hi : sampleIdx ((node :: nodes).map w) (draw rng).1 with
          | error e => simp only [List.map_cons] at hi; simp [List.map_cons, hi, Except.map] at h
          | ok idx =>
            simp only [List.map_cons] at hi
            simp only [List.map_cons, hi, Except.map] at h
            have hb := sampleBounds ((node :: nodes).map w) (draw rng).1 idx hi
            have hb' : 1 ≤ idx ∧ idx ≤ (node :: nodes).length := by simpa using hb
            obtain ⟨selected, hs, hg⟩ := getNode_selected s.root (node :: nodes) idx hb'
            have he : getNode s.root (node :: nodes) idx = a :=
              Except.ok.inj (Prod.mk.inj h).1
            have hsa : selected = a := hg.symm.trans he
            exact filter_proven s (node :: nodes) (idx - 1) a hm (hs.trans (congrArg some hsa))


private theorem precedingGreater (r : JF) (values : List JF) (idx : Nat)
    (h : firstGreater r values = some idx) :
    ∀ k value, k < idx - 1 → values[k]? = some value → greater value r = false := by
  induction values generalizing idx with
  | nil => simp [firstGreater] at h
  | cons value values ih =>
    simp only [firstGreater] at h
    split at h
    · cases h
      intro k value hk _
      omega
    · rename_i notGreater
      cases ht : firstGreater r values with
      | none => simp [ht] at h
      | some i =>
        simp [ht] at h
        subst idx
        intro k selected hk hs
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
          subst selected
          cases hg : greater value r with
          | false => rfl
          | true => exact False.elim (notGreater hg)
        | succ k =>
          apply ih i ht k selected (by omega)
          simpa only [List.getElem?_cons_succ] using hs

/-- Every successful weighted draw picks the first cumulative value strictly
above its threshold, for arbitrary weight vectors and draws. -/
def intervalsProperty : Prop := ∀ (weights : List JF) (u : Rat) idx,
  sampleIdx weights u = .ok idx →
  ∀ k value, k < idx - 1 → (cumulative weights)[k]? = some value →
    greater value (.fin u * (cumulative weights).getLast?.getD (.fin 0)) = false
 theorem intervals_proven : intervalsProperty := by
  intro weights u idx h
  have h := sampleIdx_ok h
  unfold sampleCore at h
  cases ht : (cumulative weights).getLast? with
  | none => simp [ht] at h
  | some total =>
    simp only [ht] at h
    split at h
    · cases h
    · cases hs : firstGreater (.fin u * total) (cumulative weights) with
      | none => simp [hs] at h
      | some i =>
        simp [hs] at h
        subst idx
        simpa [ht] using precedingGreater (.fin u * total) (cumulative weights) i hs

private theorem lastCumulative (weights : List JF) : ∀ sum,
    weights ≠ [] → (cumulativeAux sum weights).getLast? =
      some (weights.foldl (fun sum value => sum + value) sum) := by
  induction weights with
  | nil => intro sum hn; exact False.elim (hn rfl)
  | cons w ws ih =>
    intro sum _
    cases ws with
    | nil => rfl
    | cons v vs =>
      simpa [cumulativeAux, List.foldl_cons] using ih (sum + w) (by simp)

/-- Zero total weight is rejected for every nonempty finite nonnegative vector
and every draw. -/
def zeroProperty : Prop := ∀ (weights : List JF) (u : Rat),
  weights ≠ [] → weights.any invalidWeight = false →
  weights.foldl (fun sum value => sum + value) (.fin 0) = .fin 0 →
  sampleIdx weights u = .error (.errorException "Cumulative weighting of nodes in tree is zero.")
 theorem zero_proven : zeroProperty := by
  intro weights u hn hv hz
  have ht := lastCumulative weights (.fin 0) hn
  simp [sampleIdx, sampleCore, hv, cumulative, ht, hz]
example : ([JF.fin 0, JF.fin 0] : List JF) ≠ [] ∧
    [JF.fin 0, JF.fin 0].any invalidWeight = false ∧
    [JF.fin 0, JF.fin 0].foldl (fun sum value => sum + value) (.fin 0) = .fin 0 := by decide

private theorem invalid_any {weights : List JF} {value : JF}
    (hm : value ∈ weights) (hv : invalidWeight value = true) : weights.any invalidWeight = true :=
  List.any_eq_true.mpr ⟨value, hm, hv⟩

/-- Invalid negative weights are rejected for all uniform draws (fixed in PR #259). -/
def negativeProperty : Prop := ∀ (weights : List JF) (u : Rat),
  0 ≤ u.num → u.num < (u.den : Int) →
  (∃ value : Rat, .fin value ∈ weights ∧ value.num < 0) →
  ∃ err, sampleIdx weights u = .error err
 theorem negative_proven : negativeProperty := by
  intro weights u _ _ ⟨value, hm, hneg⟩
  have hv : invalidWeight (.fin value) = true := by
    simp only [invalidWeight, decide_eq_true_eq]
    exact Rat.not_le.mp (fun h => by have := Rat.num_nonneg.mpr h; omega)
  exact ⟨invalidWeightsError, by simp [sampleIdx, invalid_any hm hv]⟩
example : (0 : Rat).num ≥ 0 ∧ (0 : Rat).num < ((0 : Rat).den : Int) ∧
    JF.fin (-1) ∈ [JF.fin (-1), .fin 2, .fin 1] ∧ (-1 : Rat).num < 0 := by decide

/-- Every nonfinite weight vector is rejected for valid uniform draws (fixed in PR #259). -/
def nonfiniteProperty : Prop := ∀ (weights : List JF) (u : Rat),
  0 ≤ u.num → u.num < (u.den : Int) →
  (∃ value ∈ weights, value.valid = false) →
  ∃ err, sampleIdx weights u = .error err
 theorem nonfinite_proven : nonfiniteProperty := by
  intro weights u _ _ ⟨value, hm, hval⟩
  have hv : invalidWeight value = true := by
    cases value <;> simp_all [invalidWeight, JF.valid]
  exact ⟨invalidWeightsError, by simp [sampleIdx, invalid_any hm hv]⟩
example : (1/2 : Rat).num ≥ 0 ∧ (1/2 : Rat).num < ((1/2 : Rat).den : Int) ∧
    JF.negInf ∈ [JF.fin 1, .negInf, .fin 1] ∧ JF.negInf.valid = false := by decide

example : sampleIdx [.nan, .fin 1] (1/2) = .error invalidWeightsError := by decide
example : sampleIdx [.posInf, .fin 1] (1/2) = .error invalidWeightsError := by decide
example : sampleIdx [.fin 1, .negInf, .fin 1] (1/2) = .error invalidWeightsError := by decide

def emptyProperty : Prop := ∀ (s : NodeSampler JF) (rng : RNG),
  matching s = .ok [] → rand s rng =
    (.error (.errorException "No nodes matching filter were found."), rng)
 theorem empty_proven : emptyProperty := by intro s rng h; simp [rand, h]
example : matching (⟨Heap.empty, 0, 1, fun _ => false, none, false, false⟩ : NodeSampler JF) =
    .error .undefRefError := rfl

/-- Shared child identity yields two unique nodes or three occurrences. -/
private def sharedGraph : Graph JF :=
  let (a, g) := Heap.empty.alloc (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF)
  (g.alloc ⟨2, false, none, 0, 1, [a, a]⟩).2

def sharingProperty : Prop := ∀ (g : Graph JF) (fuel root : Nat)
    (preserveSharing breakSharing : Bool),
  traversal g fuel root preserveSharing breakSharing =
    (occurrences g fuel root).map (fun addresses =>
      if preserveSharing && !breakSharing then addresses.eraseDups else addresses)
 theorem sharing_proven : sharingProperty := by
  intro g fuel root preserveSharing breakSharing
  cases ho : occurrences g fuel root with
  | error err => simp [traversal, ho, bind, Except.bind, Except.map]
  | ok addresses => simp [traversal, ho, bind, Except.bind, Except.map] <;> rfl
example : traversal sharedGraph 2 1 true false = .ok [1, 0] ∧
    traversal sharedGraph 2 1 true true = .ok [1, 0, 0] := ⟨rfl, rfl⟩

def streamProperty : Prop := ∀ (rng : RNG),
  (draw rng).1 = rng.draws rng.cursor ∧ (draw rng).2.cursor = rng.cursor + 1
 theorem stream_proven : streamProperty := by intro rng; exact ⟨rfl,rfl⟩


/-- A nonempty filter set always gives a successful unweighted draw; the
integer stream is the abstract result of rand(rng,1:n). -/
def uniformSuccessProperty : Prop := ∀ (s : NodeSampler JF) (rng : RNG) node nodes,
  matching s = .ok (node :: nodes) → s.weighting = none →
  ∃ a rng', rand s rng = (.ok a, rng') ∧ s.filter a = true ∧ rng'.cursor = rng.cursor + 1
 theorem uniformSuccess_proven : uniformSuccessProperty := by
  intro s rng node nodes hm hw
  let a := getNode s.root (node :: nodes) ((rng.indexDraws nodes.length rng.cursor).val + 1)
  let rng' := { rng with cursor := rng.cursor + 1 }
  have h : rand s rng = (.ok a, rng') := by simp [rand, hm, hw, a, rng']
  exact ⟨a, rng', h, returnedFilter_proven s rng rng' a h, rfl⟩

example : matching (⟨sharedGraph, 1, 2, fun _ => false, none, true, false⟩ : NodeSampler JF) =
    .ok [] := rfl
example : matching (⟨sharedGraph, 1, 2, fun a => a == 0, none, true, false⟩ : NodeSampler JF) =
    .ok [0] := rfl
example : rand (⟨sharedGraph, 1, 2, fun a => a == 0, none, true, false⟩ : NodeSampler JF)
    ({ draws := fun _ => 0 } : RNG) = (.ok 0, { draws := fun _ => 0, cursor := 1 }) := rfl
example : sampleIdx [.fin 1] 0 = .ok 1 := by decide

end DynExpr.Expressions.Sampling
