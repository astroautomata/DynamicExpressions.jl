import DynExpr.StringsParse.Ownership

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 400000
set_option maxRecDepth 3000

/-- Every literal array object is stored by reference, src/Parse.jl:596-597. -/
def LiteralArrayExposed : Prop := ∀ cfg globals state a,
  arrayReference (parseLeafObjects cfg globals state (.value (.array a))) = some a

theorem literalArrayExposed : LiteralArrayExposed := by
  intro cfg globals state a
  simp [arrayReference, parseLeafObjects, Graph.ofTree, Heap.alloc, pure, Except.pure,
    Except.toOption, bind] <;> rfl
example : arrayReference (parseLeafObjects parseCfg (fun _ => none) arrayState
  (.value (.array ownedArray.1))) = some ownedArray.1 := by decide +kernel

/-- Every module-global array survives parsing by identity, src/Parse.jl:578-583. -/
def ModuleArrayExposed : Prop := ∀ cfg globals state name a,
  variableIndex name cfg.names = none → globals name = some (.array a) →
  arrayReference (parseLeafObjects cfg globals state (.symbol name)) = some a

theorem moduleArrayExposed : ModuleArrayExposed := by
  intro cfg globals state name a hn hg
  simp only [parseLeafObjects, hn]
  rw [hg]
  simp [arrayReference, Graph.ofTree, Heap.alloc, pure, Except.pure,
    Except.toOption, bind] <;> rfl
example : variableIndex "data" parseCfg.names = none := rfl
example : (fun name => if name == "data" then some (ObjectValue.array 0) else none) "data" =
  some (.array 0) := rfl

/-- Every module-returned mutable array is retained by the constructor, src/Parse.jl:403-405. -/
def ModuleResultExposed : Prop := ∀ state valueResult a,
  valueResult = .ok (.array a) → arrayReference (parseModuleObject state valueResult) = some a

theorem moduleResultExposed : ModuleResultExposed := by
  intro state valueResult a hr
  rw [hr]
  simp [arrayReference, parseModuleObject, Graph.ofTree, Heap.alloc, pure, Except.pure,
    Except.toOption, bind, Except.bind] <;> rfl
example : (Except.ok (ObjectValue.array 0) : Jl ObjectValue) = .ok (.array 0) := rfl

/-- All enabled external callbacks retain their returned node identity and heap,
not only identity callbacks, src/Parse.jl:506-522. -/
def ExternalNodeExposed : Prop := ∀ args state callback a result,
  callback args state = .ok (a, result) →
  parseExternalObject true args state callback = .ok (a, result)

theorem externalNodeExposed : ExternalNodeExposed := by
  intro args state callback a result h
  exact h
example : (fun (args : List Addr) (s : ObjectState) =>
    (Except.ok (args.headD 0, s) : Jl (Addr × ObjectState))) [ownedNode.1] nodeState =
  .ok (ownedNode.1, nodeState) := rfl

/-- Allocation-only heap growth: existing cells stay and `next` does not shrink. -/
def Grows (g g' : Graph ObjectValue) : Prop :=
  (∀ x c, g.cells x = some c → g'.cells x = some c) ∧ g.next ≤ g'.next

theorem grows_refl (g : Graph ObjectValue) : Grows g g := ⟨fun _ _ h => h, Nat.le_refl _⟩

theorem grows_trans {g h k : Graph ObjectValue} (a : Grows g h) (b : Grows h k) : Grows g k :=
  ⟨fun x c hc => b.1 x c (a.1 x c hc), Nat.le_trans a.2 b.2⟩

theorem grows_alloc (g : Graph ObjectValue) (v : Cell ObjectValue) : Grows g (g.alloc v).2 := by
  refine ⟨fun x c hc => ?_, by simp [Heap.alloc]⟩
  have hx : x ≠ g.next := by
    intro h
    subst h
    rw [g.fresh g.next (Nat.le_refl _)] at hc
    cases hc
  simp [Heap.alloc, hx, hc]

theorem foldlM_grows (L : Nat)
    (f : List Addr × Graph ObjectValue × List (Addr × Addr) → Addr →
      Jl (List Addr × Graph ObjectValue × List (Addr × Addr)))
    (hf : ∀ x child res, f x child = .ok res → L ≤ x.2.1.next → (∀ p ∈ x.2.2, L ≤ p.2) →
      Grows x.2.1 res.2.1 ∧ ∀ p ∈ res.2.2, L ≤ p.2) :
    ∀ (cs : List Addr) x res, cs.foldlM f x = .ok res → L ≤ x.2.1.next →
      (∀ p ∈ x.2.2, L ≤ p.2) → Grows x.2.1 res.2.1 ∧ ∀ p ∈ res.2.2, L ≤ p.2 := by
  intro cs
  induction cs with
  | nil =>
    intro x res h _ hm
    simp only [List.foldlM_nil, pure, Except.pure] at h
    cases h
    exact ⟨grows_refl _, hm⟩
  | cons c cs ih =>
    intro x res h hL hm
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i y hy
      obtain ⟨g1, m1⟩ := hf x c y hy hL hm
      obtain ⟨g2, m2⟩ := ih y res h (Nat.le_trans hL g1.2) m1
      exact ⟨grows_trans g1 g2, m2⟩

/-- Converting cells only allocates, and every result and memo target lies at
or above a bound that the heap's next identity and the memo satisfied before. -/
theorem convertCells_grows (share : Bool) (L : Nat) : ∀ (fuel : Nat) (a : Addr)
    (g : Graph ObjectValue) (memo : List (Addr × Addr))
    (res : Addr × Graph ObjectValue × List (Addr × Addr)),
    convertCells share fuel a (g, memo) = .ok res → L ≤ g.next → (∀ p ∈ memo, L ≤ p.2) →
    Grows g res.2.1 ∧ L ≤ res.1 ∧ ∀ p ∈ res.2.2, L ≤ p.2 := by
  intro fuel
  induction fuel with
  | zero => intro a g memo res h; simp [convertCells] at h
  | succ fuel ih =>
    intro a g memo res h hL hm
    unfold convertCells at h
    split at h
    · rename_i p hp
      have hpm : p ∈ memo := by
        split at hp
        · exact List.mem_of_find?_eq_some hp
        · cases hp
      cases h
      exact ⟨grows_refl _, hm p hpm, hm⟩
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i c _
        split at h
        · cases h
        · rename_i y hy
          have hf := foldlM_grows L _ (fun x child r hx hxL hxm => by
            simp only [bind, Except.bind, pure, Except.pure] at hx
            split at hx
            · cases hx
            · rename_i r' hr'
              cases hx
              obtain ⟨g1, _, m1⟩ := ih child x.2.1 x.2.2 r' hr' hxL hxm
              exact ⟨g1, m1⟩) c.children _ y hy hL hm
          obtain ⟨children, g1, m1⟩ := y
          simp only [Heap.alloc, pure, Except.pure] at h
          cases h
          refine ⟨grows_trans hf.1 (grows_alloc g1 {c with children}),
            Nat.le_trans hL hf.1.2, ?_⟩
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Nat.le_trans hL hf.1.2
          · exact hf.2 p hp

/-- A converted node of another family is a fresh identity, and conversion leaves
every existing node and every array unchanged. -/
theorem convertNodeObject_fresh (family target : String) (state : ObjectState) (a b : Addr)
    (state' : ObjectState) (hne : family ≠ target)
    (h : convertNodeObject family target state a = .ok (b, state')) :
    state.nodes.cells b = none ∧ state'.arrays = state.arrays ∧
      ∀ x c, state.nodes.cells x = some c → state'.nodes.cells x = some c := by
  unfold convertNodeObject at h
  have hb : (family == target) = false := by simpa using hne
  simp only [hb, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain ⟨b0, nodes, m⟩ := r
    simp only [pure, Except.pure] at h
    cases h
    obtain ⟨hg, hl, _⟩ := convertCells_grows (preservesSharing target) state.nodes.next _ _
      state.nodes [] _ hr (Nat.le_refl _) (by simp)
    exact ⟨state.nodes.fresh _ hl, rfl, hg.1⟩

/-- A prebuilt node of the requested family keeps its caller-owned identity and
heaps; a node of another family is converted to a freshly allocated identity,
leaving every existing node and array unchanged (PR #232), src/Parse.jl:594-595
and src/base.jl:535-552. -/
def ParsedNodeExposed : Prop := ∀ cfg globals state a,
  parseLeafObjects cfg globals state (.node cfg.nodeType a) = .ok (a, state) ∧
  ∀ family b state', family ≠ cfg.nodeType →
    parseLeafObjects cfg globals state (.node family a) = .ok (b, state') →
    state.nodes.cells b = none ∧ state'.arrays = state.arrays ∧
      ∀ x c, state.nodes.cells x = some c → state'.nodes.cells x = some c

theorem parsedNodeExposed : ParsedNodeExposed := by
  intro cfg globals state a
  refine ⟨?_, fun family b state' hne h =>
    convertNodeObject_fresh family cfg.nodeType state a b state' hne h⟩
  simp [parseLeafObjects, convertNodeObject, pure, Except.pure]

example : "GraphNode" ≠ parseCfg.nodeType ∧
    (parseLeafObjects parseCfg (fun _ => none) nodeState (.node "GraphNode" ownedNode.1)).toOption.map
      Prod.fst = some 1 := by
  decide +kernel

end DynExpr.StringsParse.General
