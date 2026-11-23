import DynExpr.Expressions.Wrapper
import DynExpr.NoAlias.Core

namespace DynExpr.Expressions.HeapCopy

/-- Object cache of copied GraphNode identities, src/base.jl:440-510. -/
abbrev CopyState := Graph JF × List (Addr × Addr)
/-- Heap copy with optional preservation of shared identities,
src/base.jl:440-510. Leaf/branch copies allocate fresh objects; the cache maps
source identities to copied identities and is populated after child traversal. -/
def copyNode (source : Graph JF) (cacheEnabled : Bool) : Nat → Addr → StateT CopyState Jl Addr
  | 0, _ => throw (.undefinedBehavior "insufficient copy fuel")
  | fuel + 1, root => do
    let state ← get
    match if cacheEnabled then (state.2.find? (fun kv => kv.1 == root)).map Prod.snd else none with
    | some copied => pure copied
    | none =>
      let cell ← liftM (source.read root)
      let children ← cell.children.mapM (copyNode source cacheEnabled fuel)
      let state ← get
      let (copied, graph) := state.1.alloc { cell with children := children }
      set (graph, (root, copied) :: state.2)
      pure copied

/-- Heap-backed expression contents and immutable metadata,
src/Expression.jl:93-98. -/
structure Expression where
  root : Addr
  metadata : Nat
/-- src/Expression.jl:275-277. The break_sharing keyword reaches tree copying. -/
def copyExpression (source : Graph JF) (ex : Expression) (fuel : Nat)
    (preserveSharing breakSharing : Bool) : Jl (Expression × Graph JF) := do
  let (root, state) ← (copyNode source (preserveSharing && !breakSharing) fuel ex.root).run (source, [])
  pure (⟨root, ex.metadata⟩, state.1)
/-- src/Expression.jl:292. The wrapper forwards its keywords to copy(ex; kws...). -/
def copyNodeExpression (source : Graph JF) (ex : Expression) (fuel : Nat)
    (preserveSharing breakSharing : Bool) :=
  copyExpression source ex fuel preserveSharing breakSharing

private def graph : Graph JF :=
  let (child, g) := Heap.empty.alloc (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF)
  (g.alloc ⟨2, false, none, 0, 1, [child, child]⟩).2
private def ex : Expression := ⟨1, 7⟩
/-- Observe whether the returned root has two equal active child addresses. -/
def childrenShared (result : Jl (Expression × Graph JF)) : Option Bool := do
  let (out, g) ← result.toOption
  let cell ← g.cells out.root
  let left ← cell.children[0]?
  let right ← cell.children[1]?
  pure (left == right)

/-- copy_node forwards the caller's sharing keyword for every decodable finite
heap expression, including errors produced by the tree copier (fixed in PR #255). -/
def copyKeywordProperty : Prop := ∀ (source : Graph JF) (input : Expression)
    (fuel : Nat) (preserveSharing breakSharing : Bool),
  (∃ tree, source.unfold fuel input.root = some tree) →
  copyNodeExpression source input fuel preserveSharing breakSharing =
    copyExpression source input fuel preserveSharing breakSharing
 theorem copyKeyword_proven : copyKeywordProperty := fun _ _ _ _ _ _ => rfl
example : ∃ tree, graph.unfold 2 ex.root = some tree :=
  ⟨.branch 1 [.const (.fin 1), .const (.fin 1)], rfl⟩
example : childrenShared (copyNodeExpression graph ex 2 true true) = some false := rfl

/-- Direct wrapper copy passes every tree, option and metadata value to the
raw heap copier with exactly its resolved sharing policy. -/
def directCopyProperty : Prop := ∀ (source : Graph JF) (input : Expression)
    (fuel : Nat) (preserveSharing breakSharing : Bool),
  copyExpression source input fuel preserveSharing breakSharing =
    ((copyNode source (preserveSharing && !breakSharing) fuel input.root).run (source, [])).map
      (fun result => (⟨result.1, input.metadata⟩, result.2.1))
 theorem directCopy_proven : directCopyProperty := by
  intro source input fuel preserveSharing breakSharing
  cases hc : (copyNode source (preserveSharing && !breakSharing) fuel input.root).run (source, []) with
  | error err => simp [copyExpression, hc, bind, Except.bind, Except.map]
  | ok result =>
    obtain ⟨root, state⟩ := result
    simp [copyExpression, hc, bind, Except.bind, Except.map] <;> rfl

example : childrenShared (copyExpression graph ex 2 true false) = some true ∧
    childrenShared (copyExpression graph ex 2 true true) = some false := ⟨rfl, rfl⟩

private theorem state_bind {σ α β : Type} (m : StateT σ Jl α)
    (f : α → StateT σ Jl β) (s : σ) :
    (m >>= f) s = (m s >>= fun pair => f pair.1 pair.2) := rfl
private theorem state_get {σ : Type} (s : σ) :
    (get : StateT σ Jl σ) s = .ok (s, s) := rfl
private theorem state_set {σ : Type} (s s' : σ) :
    (set s' : StateT σ Jl PUnit) s = .ok (PUnit.unit, s') := rfl
private theorem state_lift {σ α : Type} (s : σ) (m : Jl α) :
    (liftM m : StateT σ Jl α) s = ((fun a => (a, s)) <$> m) := rfl
private theorem state_pure {σ α : Type} (s : σ) (a : α) :
    (pure a : StateT σ Jl α) s = .ok (a, s) := rfl
private theorem jl_ok_bind {α β : Type} (a : α) (f : α → Jl β) :
    ((.ok a : Jl α) >>= f) = f a := rfl
private theorem mapM_step {α β : Type} (f : α → StateT CopyState Jl β)
    (x : α) (xs : List α) (s : CopyState) :
    ((x :: xs).mapM f).run s =
      (f x).run s >>= fun head => (xs.mapM f).run head.2 >>= fun tail =>
        .ok (head.1 :: tail.1, tail.2) := by
  simp only [List.mapM_cons, StateT.run, state_bind, state_pure]

private theorem copyNode_step (source : Graph JF) (enabled : Bool)
    (fuel : Nat) (root : Addr) (state : CopyState)
    (miss : (if enabled then (state.2.find? (fun kv => kv.1 == root)).map Prod.snd
      else none) = none) :
    (copyNode source enabled (fuel + 1) root).run state =
      (source.read root >>= fun cell =>
        (cell.children.mapM (copyNode source enabled fuel)).run state >>= fun result =>
          let allocated := result.2.1.alloc { cell with children := result.1 }
          pure (allocated.1, (allocated.2, (root, allocated.1) :: result.2.2))) := by
  simp only [copyNode, StateT.run, state_bind, state_get, jl_ok_bind, miss]
  simp only [state_lift, state_set, state_pure]
  cases source.read root <;> rfl


private def CacheAway (source : Graph JF) (root : Addr) (cache : List (Addr × Addr)) : Prop :=
  ∀ kv ∈ cache, ¬ Graph.Reachable source root kv.1

private def CacheGrowth (source : Graph JF) (roots : List Addr)
    (before after : List (Addr × Addr)) : Prop :=
  ∀ kv ∈ after, kv ∈ before ∨ ∃ root ∈ roots, Graph.Reachable source root kv.1

private theorem cache_miss {source : Graph JF} {root : Addr} {cache : List (Addr × Addr)}
    (ha : CacheAway source root cache) :
    (cache.find? (fun kv => kv.1 == root)).map Prod.snd = none := by
  have hn : cache.find? (fun kv => kv.1 == root) = none := by
    apply List.find?_eq_none.mpr
    intro kv hk
    simp only [beq_iff_eq]
    intro heq
    exact ha kv hk (heq ▸ DynExpr.NoAlias.reach_refl source root)
  rw [hn]
  rfl

private theorem copyNode_noAlias_aux (source : Graph JF) (fuel : Nat) :
    ∀ root state, Graph.NoAlias source root → CacheAway source root state.2 →
      (copyNode source true fuel root).run state = (copyNode source false fuel root).run state ∧
      (∀ result, (copyNode source false fuel root).run state = .ok result →
        CacheGrowth source [root] state.2 result.2.2) := by
  induction fuel with
  | zero =>
    intro root state _ _
    exact ⟨rfl, by intro result h; cases h⟩
  | succ fuel ih =>
    have forest : ∀ roots state,
        (∀ root ∈ roots, Graph.NoAlias source root) →
        roots.Pairwise (DynExpr.NoAlias.Disjoint source) →
        (∀ root ∈ roots, CacheAway source root state.2) →
        (roots.mapM (copyNode source true fuel)).run state =
          (roots.mapM (copyNode source false fuel)).run state ∧
        (∀ result, (roots.mapM (copyNode source false fuel)).run state = .ok result →
          CacheGrowth source roots state.2 result.2.2) := by
      intro roots
      induction roots with
      | nil =>
        intro state _ _ _
        refine ⟨rfl, ?_⟩
        intro result h
        change Except.ok ([], state) = .ok result at h
        cases h
        intro kv hk
        exact Or.inl hk
      | cons root roots iht =>
        intro state hna hdis haway
        obtain ⟨heq, hgrowth⟩ := ih root state (hna root (by simp)) (haway root (by simp))
        obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdis
        cases hr : (copyNode source false fuel root).run state with
        | error err =>
          refine ⟨?_, ?_⟩
          · simp only [mapM_step, heq, hr, bind, Except.bind]
          · intro result h
            simp only [mapM_step, hr, bind, Except.bind] at h
            cases h
        | ok result =>
          have htaway : ∀ other ∈ roots, CacheAway source other result.2.2 := by
            intro other ho kv hk hreach
            rcases hgrowth result hr kv hk with hold | ⟨x, hx, hnew⟩
            · exact haway other (by simp [ho]) kv hold hreach
            · simp only [List.mem_singleton] at hx
              subst x
              exact hhead other ho kv.1 hnew hreach
          obtain ⟨ht, htgrowth⟩ := iht result.2 (fun x hx => hna x (by simp [hx])) htail htaway
          refine ⟨?_, ?_⟩
          · simp only [mapM_step, heq, hr, bind, Except.bind, ht]
          · intro out hout
            cases htRun : (roots.mapM (copyNode source false fuel)).run result.2 with
            | error err =>
              simp only [mapM_step, hr, htRun, bind, Except.bind] at hout
              cases hout
            | ok tailResult =>
              have hout' : .ok (result.1 :: tailResult.1, tailResult.2) = (Except.ok out : Jl _) := by
                simpa only [mapM_step, hr, htRun, bind, Except.bind] using hout
              cases hout'
              intro kv hk
              rcases htgrowth tailResult htRun kv hk with hmid | ⟨x, hx, hreach⟩
              · rcases hgrowth result hr kv hmid with hold | ⟨x, hx, hreach⟩
                · exact Or.inl hold
                · exact Or.inr ⟨x, by simp_all, hreach⟩
              · exact Or.inr ⟨x, by simp [hx], hreach⟩
    intro root state hna haway
    rw [copyNode_step source true fuel root state (by simpa using cache_miss haway),
      copyNode_step source false fuel root state rfl]
    cases hc : source.cells root with
    | none =>
      simp [Heap.read, hc, bind, Except.bind]
    | some cell =>
      have hchildren : ∀ child ∈ cell.children, Graph.NoAlias source child :=
        fun child hm => DynExpr.NoAlias.noAlias_child hna hc hm
      have hdis : cell.children.Pairwise (DynExpr.NoAlias.Disjoint source) := by
        apply (DynExpr.NoAlias.noAlias_kids_nodup hna hc).imp_of_mem
        intro a b ha hb hne
        exact DynExpr.NoAlias.noAlias_mem_disjoint hna hc ha hb hne
      have hchildrenAway : ∀ child ∈ cell.children, CacheAway source child state.2 := by
        intro child hm kv hk hreach
        exact haway kv hk (DynExpr.NoAlias.reach_trans (DynExpr.NoAlias.reach_mem hc hm) hreach)
      obtain ⟨heq, hgrowth⟩ := forest cell.children state hchildren hdis hchildrenAway
      refine ⟨by simp [Heap.read, hc, bind, Except.bind, heq], ?_⟩
      intro out hout
      cases hr : (cell.children.mapM (copyNode source false fuel)).run state with
      | error err => simp [Heap.read, hc, hr, bind, Except.bind] at hout
      | ok result =>
        have hout' : Except.ok ((result.2.1.alloc { cell with children := result.1 }).1,
            ((result.2.1.alloc { cell with children := result.1 }).2,
              (root, (result.2.1.alloc { cell with children := result.1 }).1) :: result.2.2)) =
            (Except.ok out : Jl _) := by
          simpa [Heap.read, hc, hr, bind, Except.bind, pure, Except.pure] using hout
        cases hout'
        intro kv hk
        rcases List.mem_cons.mp hk with he | hm
        · subst kv
          exact Or.inr ⟨root, by simp, DynExpr.NoAlias.reach_refl source root⟩
        · rcases hgrowth result hr kv hm with hold | ⟨child, hm, hreach⟩
          · exact Or.inl hold
          · exact Or.inr ⟨root, by simp,
              DynExpr.NoAlias.reach_trans (DynExpr.NoAlias.reach_mem hc hm) hreach⟩

/-- On an unshared source, identity caching never changes recursive copying,
including the returned fresh addresses, heap, cache and explicit errors. -/
theorem copyNode_noAlias (source : Graph JF) (root : Addr) (fuel : Nat)
    (heap : Graph JF) (hna : Graph.NoAlias source root) :
    (copyNode source true fuel root).run (heap, []) =
      (copyNode source false fuel root).run (heap, []) :=
  (copyNode_noAlias_aux source fuel root (heap, []) hna
    (by intro kv hk; cases hk)).1

/-- Successful list decoding supplies a decoded value at every input position. -/
theorem mapM_some_member {α β : Type} (f : α → Option β) (xs : List α) {ys : List β}
    (h : xs.mapM f = some ys) : ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hx, ht] at h
      | some tail =>
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨y, hx⟩
        · exact ih ht a ha

/-- A finite decoded heap node is allocated and all its children decode with
one fewer unit of fuel, including the empty child list of a leaf. -/
theorem decoded_children {source : Graph JF} {fuel root : Nat}
    (decoded : ∃ tree, source.unfold (fuel + 1) root = some tree) :
    ∃ cell, source.cells root = some cell ∧
      ∀ child ∈ cell.children, ∃ tree, source.unfold fuel child = some tree := by
  obtain ⟨tree, hu⟩ := decoded
  cases hc : source.cells root with
  | none => simp [Graph.unfold, hc] at hu
  | some cell =>
    refine ⟨cell, rfl, ?_⟩
    by_cases hlen : cell.children.length ≠ cell.degree
    · simp [Graph.unfold, hc, hlen] at hu
    · by_cases hd : cell.degree = 0
      · have hempty : cell.children = [] := by
          cases he : cell.children <;> simp_all
        simp [hempty]
      · cases hm : cell.children.mapM (source.unfold fuel) with
        | none => simp [Graph.unfold, hc, hd, hm] at hu
        | some trees => exact mapM_some_member _ _ hm

/-- Finite heap decoding provides sufficient fuel for copying, with either
sharing policy and any existing copy state. -/
theorem copyNode_success (source : Graph JF) (enabled : Bool) (fuel root : Nat)
    (state : CopyState) (decoded : ∃ tree, source.unfold fuel root = some tree) :
    ∃ result, (copyNode source enabled fuel root).run state = .ok result := by
  induction fuel generalizing root state with
  | zero => obtain ⟨tree, hu⟩ := decoded; cases hu
  | succ fuel ih =>
    obtain ⟨cell, hc, hchildren⟩ := decoded_children decoded
    have forest : ∀ (roots : List Addr) (state : CopyState),
        (∀ root ∈ roots, ∃ tree, source.unfold fuel root = some tree) →
        ∃ result, (roots.mapM (copyNode source enabled fuel)).run state = .ok result := by
      intro roots
      induction roots with
      | nil => intro state _; exact ⟨([], state), rfl⟩
      | cons root roots iht =>
        intro state hdecode
        obtain ⟨head, hh⟩ := ih root state (hdecode root (by simp))
        obtain ⟨tail, ht⟩ := iht head.2 (fun x hx => hdecode x (by simp [hx]))
        exact ⟨(head.1 :: tail.1, tail.2), by simp only [mapM_step, hh, ht, jl_ok_bind]⟩
    cases hcache : (if enabled then (state.2.find? (fun kv => kv.1 == root)).map Prod.snd
      else none) with
    | some copied =>
      refine ⟨(copied, state), ?_⟩
      simp only [copyNode, StateT.run, state_bind, state_get, jl_ok_bind, hcache, state_pure]
    | none =>
      obtain ⟨children, hm⟩ := forest cell.children state hchildren
      rw [copyNode_step source enabled fuel root state hcache]
      refine ⟨((children.2.1.alloc { cell with children := children.1 }).1,
        ((children.2.1.alloc { cell with children := children.1 }).2,
          (root, (children.2.1.alloc { cell with children := children.1 }).1) :: children.2.2)), ?_⟩
      simp [Heap.read, hc, hm, bind, Except.bind, pure, Except.pure]

/-- Direct expression copying succeeds on every finite decodable input. -/
theorem copyExpression_success (source : Graph JF) (input : Expression) (fuel : Nat)
    (preserveSharing breakSharing : Bool)
    (decoded : ∃ tree, source.unfold fuel input.root = some tree) :
    ∃ result, copyExpression source input fuel preserveSharing breakSharing = .ok result := by
  obtain ⟨result, hr⟩ := copyNode_success source (preserveSharing && !breakSharing)
    fuel input.root (source, []) decoded
  exact ⟨(⟨result.1, input.metadata⟩, result.2.1), by
    simp [copyExpression, hr, bind, Except.bind, pure, Except.pure]⟩

/-- The raw wrapper always returns a copied expression and heap when the
source decodes with the supplied finite fuel. -/
def copySuccessProperty : Prop := ∀ (source : Graph JF) (input : Expression)
    (fuel : Nat) (preserveSharing breakSharing : Bool),
  (∃ tree, source.unfold fuel input.root = some tree) →
  ∃ result, copyExpression source input fuel preserveSharing breakSharing = .ok result

theorem copySuccess_proven : copySuccessProperty := copyExpression_success

/-- The keyword wrapper and requested copy return the same fresh expression
and exact heap on the safe flag and alias domain. -/
def copyKeywordSafeProperty : Prop := ∀ (source : Graph JF) (input : Expression)
    (fuel : Nat) (preserveSharing breakSharing : Bool),
  (∃ tree, source.unfold fuel input.root = some tree) →
  (breakSharing = false ∨ preserveSharing = false ∨ Graph.NoAlias source input.root) →
  ∃ result,
    copyNodeExpression source input fuel preserveSharing breakSharing = .ok result ∧
    copyExpression source input fuel preserveSharing breakSharing = .ok result

theorem copyKeywordSafe_proven : copyKeywordSafeProperty := by
  intro source input fuel preserveSharing breakSharing decoded _
  have equal : copyNodeExpression source input fuel preserveSharing breakSharing =
      copyExpression source input fuel preserveSharing breakSharing := rfl
  obtain ⟨result, hr⟩ := copyExpression_success source input fuel preserveSharing breakSharing decoded
  exact ⟨result, equal.trans hr, hr⟩

example : ∃ (source : Graph JF) (input : Expression) (fuel : Nat),
    (∃ tree, source.unfold fuel input.root = some tree) ∧
    Graph.NoAlias source input.root := by
  let tree : Tree JF := .branch 1 [.const (.fin 1), .feature 2]
  let built := Graph.ofTree (Heap.empty : Graph JF) tree
  refine ⟨built.2, ⟨built.1, 7⟩, 2, ⟨tree, ?_⟩, Graph.noAlias_ofTree _ tree⟩
  exact Graph.unfold_ofTree _ tree (by simp [tree, Tree.Representable]) 2
    (by simp [tree, Tree.depth])

end DynExpr.Expressions.HeapCopy
