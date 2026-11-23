import DynExpr.StringsParse.Roundtrip.Main

/-! Rendering of unshared `GraphNode` graphs (`src/Strings.jl:188-195`,
`src/base.jl:77-121`): without aliasing the shared-marker cache never hits, so
the graph renders exactly as its unfolded tree. -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-- The child step of `rawGraph`'s left fold. -/
def graphStep (cfg : RenderConfig) (g : Graph Scalar) (fuel : Nat) :
    List String × List (Addr × String) → Addr → Jl (List String × List (Addr × String)) :=
  fun (args, cache) child => do
    let (s, cache) ← rawGraph cfg g fuel child cache
    return (args ++ [s], cache)

theorem rawGraph_succ (cfg : RenderConfig) (g : Graph Scalar) (fuel : Nat) (a : Addr)
    (cache : List (Addr × String)) :
    rawGraph cfg g (fuel + 1) a cache = (do
      if let some p := cache.find? (fun p => p.1 == a) then
        return ("{" ++ p.2 ++ "}", cache)
      let c ← g.read a
      let (text, cache) ← if c.degree = 0 then
          if c.constant then
            match c.val with
            | some v => .ok (cfg.fConstant v, cache)
            | none => .error .undefRefError
          else .ok (cfg.fVariable c.feature cfg.names, cache)
        else do
          let op ← dispatchOpName cfg.operators c.degree c.op (resolvePretty cfg.pretty cfg.raw)
          let (args, cache) ← c.children.foldlM (graphStep cfg g fuel) ([], cache)
          let text ← combineOpWithInputs op args
          pure (text, cache)
      return (text, (a, text) :: cache)) := by
  rw [rawGraph]
  rfl

theorem find?_none_append {l₁ l₂ : List (Addr × String)} {b : Addr}
    (h1 : ∀ e ∈ l₁, e.1 ≠ b) (h2 : l₂.find? (fun q => q.1 == b) = none) :
    (l₁ ++ l₂).find? (fun q => q.1 == b) = none := by
  rw [List.find?_eq_none] at h2 ⊢
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simpa using h1 x hx
  · exact h2 x hx

theorem mapM_some_length {f : Addr → Option (Tree Scalar)} :
    ∀ (l : List Addr) (ts : List (Tree Scalar)), l.mapM f = some ts → ts.length = l.length := by
  intro l
  induction l with
  | nil => intro ts h; simp at h; subst h; rfl
  | cons x l ih =>
    intro ts h
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some tx =>
      cases hl : l.mapM f with
      | none => simp [hx, hl] at h
      | some ts' =>
        simp [hx, hl] at h
        subst h
        simp [ih ts' hl]

/-- The child fold renders each child as its unfolded tree, given the
fuel-indexed result for the children. -/
theorem fold_children (cfg : RenderConfig) (g : Graph Scalar) (root : Addr)
    (hna : Graph.NoAlias g root) (f : Nat)
    (IH : ∀ a p t cache s, Graph.Path g root p a → Graph.unfold g f a = some t →
      rawTree cfg t = .ok s →
      (∀ b, Graph.Reachable g a b → cache.find? (fun q => q.1 == b) = none) →
      ∃ added : List (Addr × String), (∀ e ∈ added, Graph.Reachable g a e.1) ∧
        rawGraph cfg g f a cache = .ok (s, added ++ cache))
    {a : Addr} {p : List Nat} {c : Cell Scalar} {cache : List (Addr × String)}
    (hp : Graph.Path g root p a) (hca : g.cells a = some c)
    (hc : ∀ b, Graph.Reachable g a b → cache.find? (fun q => q.1 == b) = none) :
    ∀ (cs pre : List Addr) (ts : List (Tree Scalar)) (texts args : List String)
      (acc : List (Addr × String)),
      c.children = pre ++ cs → cs.mapM (Graph.unfold g f) = some ts → rawForest cfg ts = .ok texts →
      (∀ e ∈ acc, ∃ j < pre.length, ∃ b, pre[j]? = some b ∧ Graph.Reachable g b e.1) →
      ∃ added : List (Addr × String),
        (∀ e ∈ added, ∃ j : Nat, ∃ b : Addr, c.children[j]? = some b ∧ Graph.Reachable g b e.1) ∧
        cs.foldlM (graphStep cfg g f) (args, acc ++ cache) = .ok (args ++ texts, added ++ cache) := by
  intro cs
  induction cs with
  | nil =>
    intro pre ts texts args acc hsplit hm hf hacc
    simp at hm
    subst hm
    simp [rawForest] at hf
    subst hf
    refine ⟨acc, ?_, by simp only [List.foldlM_nil, List.append_nil]; rfl⟩
    intro e he
    obtain ⟨j, _, b, hb, hr⟩ := hacc e he
    exact ⟨j, b, by rw [hsplit, List.append_nil]; exact hb, hr⟩
  | cons x cs ih =>
    intro pre ts texts args acc hsplit hm hf hacc
    simp only [List.mapM_cons] at hm
    cases hx : Graph.unfold g f x with
    | none => simp [hx] at hm
    | some tx =>
      cases hl : cs.mapM (Graph.unfold g f) with
      | none => simp [hx, hl] at hm
      | some ts' =>
        simp [hx, hl] at hm
        subst hm
        simp only [rawForest, bind, Except.bind, pure, Except.pure] at hf
        cases hrx : rawTree cfg tx with
        | error e => simp [hrx] at hf
        | ok sx =>
          cases hrf : rawForest cfg ts' with
          | error e => simp [hrx, hrf] at hf
          | ok texts' =>
            simp [hrx, hrf] at hf
            subst hf
            have hix : c.children[pre.length]? = some x := by
              rw [hsplit]; simp
            have hpx : Graph.Path g root (p ++ [pre.length]) x :=
              hp.append (.cons hca hix (.nil x))
            have hdisj : ∀ b, Graph.Reachable g x b →
                (acc ++ cache).find? (fun q => q.1 == b) = none := by
              intro b ⟨q, hq⟩
              apply find?_none_append
              · intro e he heq
                obtain ⟨j, hj, y, hy, ⟨q', hq'⟩⟩ := hacc e he
                rw [heq] at hq'
                have hjy : c.children[j]? = some y := by
                  rw [hsplit, List.getElem?_append_left hj]; exact hy
                have h1 := hp.append (.cons hca hjy hq')
                have h2 := hp.append (.cons hca hix hq)
                have := hna _ _ _ h1 h2
                simp at this
                omega
              · exact hc b ⟨pre.length :: q, .cons hca hix hq⟩
            obtain ⟨addx, haddx, hgx⟩ := IH x _ tx (acc ++ cache) sx hpx hx hrx hdisj
            have hstep : graphStep cfg g f (args, acc ++ cache) x =
                .ok (args ++ [sx], (addx ++ acc) ++ cache) := by
              simp only [graphStep, hgx, bind, Except.bind, pure, Except.pure, List.append_assoc]
            have hacc' : ∀ e ∈ addx ++ acc, ∃ j < (pre ++ [x]).length, ∃ b,
                (pre ++ [x])[j]? = some b ∧ Graph.Reachable g b e.1 := by
              intro e he
              rcases List.mem_append.mp he with he | he
              · exact ⟨pre.length, by simp, x, by simp, haddx e he⟩
              · obtain ⟨j, hj, b, hb, hr⟩ := hacc e he
                exact ⟨j, by simp; omega, b, by rw [List.getElem?_append_left hj]; exact hb, hr⟩
            obtain ⟨added, hadded, hfold⟩ := ih (pre ++ [x]) ts' texts' (args ++ [sx]) (addx ++ acc)
              (by rw [hsplit]; simp) hl hrf hacc'
            refine ⟨added, hadded, ?_⟩
            rw [List.foldlM_cons, hstep]
            simp only [bind, Except.bind]
            rw [hfold]
            simp

/-- Without aliasing, rendering a graph agrees with rendering its unfolded tree;
the cache only gains entries for addresses below the visited node. -/
theorem rawGraph_tree (cfg : RenderConfig) (g : Graph Scalar) (root : Addr)
    (hna : Graph.NoAlias g root) (fuel : Nat) :
    ∀ a p t cache s, Graph.Path g root p a → Graph.unfold g fuel a = some t →
      rawTree cfg t = .ok s →
      (∀ b, Graph.Reachable g a b → cache.find? (fun q => q.1 == b) = none) →
      ∃ added : List (Addr × String), (∀ e ∈ added, Graph.Reachable g a e.1) ∧
        rawGraph cfg g fuel a cache = .ok (s, added ++ cache) := by
  induction fuel with
  | zero => intro a p t cache s _ hu; simp [Graph.unfold] at hu
  | succ f ih =>
    intro a p t cache s hp hu hr hc
    have hfa : cache.find? (fun q => q.1 == a) = none := hc a ⟨[], .nil a⟩
    cases hca : g.cells a with
    | none => simp [Graph.unfold, hca] at hu
    | some c =>
      have hread : g.read a = .ok c := by simp [Heap.read, hca]
      rw [Graph.unfold, hca] at hu
      change (if c.children.length ≠ c.degree then none
          else if c.degree = 0 then
            if c.constant then (do return Tree.const (← c.val)) else (return Tree.feature c.feature)
          else (do return Tree.branch c.op (← c.children.mapM (Graph.unfold g f)))) = some t at hu
      by_cases hlen : c.children.length = c.degree
      · rw [if_neg (fun h => h hlen)] at hu
        rw [rawGraph_succ]
        simp only [hfa, hread, bind, Except.bind, pure, Except.pure]
        by_cases hd : c.degree = 0
        · rw [if_pos hd] at hu
          simp only [hd, ↓reduceIte]
          by_cases hk : c.constant = true
          · rw [if_pos hk] at hu
            simp only [hk, ↓reduceIte]
            cases hv : c.val with
            | none => simp [hv] at hu
            | some v =>
              simp [hv] at hu
              subst hu
              simp [rawTree] at hr
              subst hr
              exact ⟨[(a, cfg.fConstant v)], by simp; exact ⟨[], .nil a⟩, rfl⟩
          · rw [if_neg hk] at hu
            simp only [hk, Bool.false_eq_true, ↓reduceIte]
            simp at hu
            subst hu
            simp [rawTree] at hr
            subst hr
            exact ⟨[(a, cfg.fVariable c.feature cfg.names)], by simp; exact ⟨[], .nil a⟩, rfl⟩
        · rw [if_neg hd] at hu
          simp only [hd, ↓reduceIte]
          cases hm : c.children.mapM (Graph.unfold g f) with
          | none => simp [hm] at hu
          | some ts =>
            simp [hm] at hu
            subst hu
            have hts : ts.length = c.degree := by
              rw [mapM_some_length _ _ hm, hlen]
            rw [rawTree, hts] at hr
            simp only [bind, Except.bind] at hr
            cases hop : dispatchOpName cfg.operators c.degree c.op (resolvePretty cfg.pretty cfg.raw) with
            | error e => simp [hop] at hr
            | ok op =>
              simp only [hop] at hr
              cases hrf : rawForest cfg ts with
              | error e => simp [hrf] at hr
              | ok texts =>
                simp only [hrf] at hr
                obtain ⟨added, hadded, hfold⟩ := fold_children cfg g root hna f ih hp hca hc
                  c.children [] ts texts [] [] (by simp) hm hrf (by simp)
                simp only [List.nil_append] at hfold
                rw [hfold]
                simp only [hr]
                refine ⟨(a, s) :: added, ?_, rfl⟩
                intro e he
                rcases List.mem_cons.mp he with he | he
                · subst he; exact ⟨[], .nil a⟩
                · obtain ⟨j, b, hb, q, hq⟩ := hadded e he
                  exact ⟨j :: q, .cons hca hb hq⟩
      · rw [if_pos (by simpa using hlen)] at hu
        cases hu

/-- An unshared graph renders exactly as its unfolded tree. -/
theorem stringGraph_tree (ops : Operators) (names : List String) (g : Graph Scalar) (root : Addr)
    (hna : Graph.NoAlias g root) {fuel : Nat} {t : Tree Scalar} (hu : Graph.unfold g fuel root = some t)
    {s : String} (hs : stringTree (rcfg ops names) t = .ok s) :
    stringGraph (rcfg ops names) g fuel root = .ok s := by
  unfold stringTree at hs
  unfold stringGraph
  simp only [rcfg, resolveNames, bind, Except.bind] at hs ⊢
  split at hs
  · cases hs
  · rename_i r hr
    obtain ⟨added, _, hg⟩ := rawGraph_tree _ g root hna fuel root [] t [] r (.nil root) hu hr
      (by intro b _; rfl)
    rw [hg]
    exact hs

end DynExpr.StringsParse.Roundtrip
