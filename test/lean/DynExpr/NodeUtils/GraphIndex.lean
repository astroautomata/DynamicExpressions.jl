import DynExpr.NodeUtils.Nodes

namespace DynExpr.NodeUtils

variable {T : Type}

/-- Left-to-right child calls of the generated `@ncall` in src/base.jl:134-143.
Each child sees the counter and identity cache left by its left sibling. -/
def indexChildren (walk : Addr → Nat → List (Addr × NodeIndex) → Jl (NodeIndex × Nat × List (Addr × NodeIndex))) :
    List Addr → List NodeIndex → Nat → List (Addr × NodeIndex) →
      Jl (List NodeIndex × Nat × List (Addr × NodeIndex))
  | [], ns, j, m => .ok (ns, j, m)
  | a :: as, ns, j, m =>
      match walk a j m with
      | .ok (n, k, m') => indexChildren walk as (ns ++ [n]) k m'
      | .error e => .error e

/-- src/NodeUtils.jl:186-202 with the src/base.jl:87-155 identity cache.
`f_leaf` reads `t.constant` and advances the counter only on leaves; `f_branch`
is `t -> nothing`, so operator nodes never read their inactive constant field.
Cache hits return the stored index tree without evaluating `f_leaf`. Index
trees unfold cache reuse structurally. The modulus models the selected unsigned
index type; 65536 is UInt16. -/
def indexGraphWalk (g : Graph T) (sharing : Bool) (modulus : Nat) :
    Nat → Addr → Nat → List (Addr × NodeIndex) → Jl (NodeIndex × Nat × List (Addr × NodeIndex))
  | 0, _, _, _ => .error (.errorException "traversal fuel exhausted")
  | fuel + 1, root, i, cache =>
      match (if sharing then cache.lookup root else none) with
      | some n => .ok (n, i, cache)
      | none =>
          match g.read root with
          | .error e => .error e
          | .ok c =>
              let visited : Jl (NodeIndex × Nat × List (Addr × NodeIndex)) :=
                if c.degree = 0 then
                  if c.constant then .ok (.leaf ((i + 1) % modulus), (i + 1) % modulus, cache)
                  else .ok (.leaf 0, i, cache)
                else
                  match indexChildren (indexGraphWalk g sharing modulus fuel) c.children [] i cache with
                  | .ok (ns, j, m) => .ok (.branch ns, j, m)
                  | .error e => .error e
              match visited with
              | .ok (n, j, m) => .ok (n, j, if sharing then (root, n) :: m else m)
              | .error e => .error e

/-- src/NodeUtils.jl:191 initializes the counter to the selected type's zero. -/
def indexGraph (g : Graph T) (sharing : Bool) (fuel root : Nat) :=
  indexGraphWalk g sharing 65536 fuel root 0 []

/-- Cache-hit step of src/base.jl:126-129: a cached identity reuses its index
tree without advancing the counter or changing the cache. -/
theorem indexGraphWalk_cacheHit (g : Graph T) (modulus fuel root counter : Nat)
    (cache : List (Addr × NodeIndex)) (cached : NodeIndex)
    (hc : cache.lookup root = some cached) :
    indexGraphWalk g true modulus (fuel + 1) root counter cache = .ok (cached, counter, cache) := by
  simp [indexGraphWalk, hc]

/-! ### Independent specification -/

/-- Child-path accessor for index trees (`NodeIndex` children, src/NodeUtils.jl:150-169). -/
def indexAt : NodeIndex → List Nat → Option NodeIndex
  | n, [] => some n
  | .leaf _, _ :: _ => none
  | .branch cs, i :: p =>
      match cs[i]? with
      | some c => indexAt c p
      | none => none

/-- Preorder inventory of the fully unfolded source: every constant-leaf
occurrence, left to right, repeats included (no identity cache). -/
def constLeafOccurrences (g : Graph T) : Nat → Addr → Option (List Addr)
  | 0, _ => none
  | fuel + 1, a =>
      match g.cells a with
      | none => none
      | some c =>
          if c.degree = 0 then some (if c.constant then [a] else [])
          else (c.children.mapM (constLeafOccurrences g fuel)).map List.flatten

/-- Keep the first occurrence of each identity, in order. -/
def firstVisits : List Addr → List Addr → List Addr
  | seen, [] => seen
  | seen, a :: l => firstVisits (if a ∈ seen then seen else seen ++ [a]) l

/-- First-visit order of distinct constant-leaf identities in a depth-first
left-to-right traversal of the source. -/
def firstVisitOrder (g : Graph T) (fuel root : Nat) : List Addr :=
  firstVisits [] ((constLeafOccurrences g fuel root).getD [])

/-- Zero-based position of the first occurrence of an identity. -/
def posOf (a : Addr) : List Addr → Nat
  | [] => 0
  | b :: l => if b = a then 0 else posOf a l + 1

/-- `a` is a constant leaf object reachable from `root`. -/
def ConstLeafAt (g : Graph T) (root a : Addr) : Prop :=
  ∃ p c, Graph.Path g root p a ∧ g.cells a = some c ∧ c.degree = 0 ∧ c.constant = true

/-- At most 65535 distinct constant leaf objects are reachable from `root`. -/
def ConstCapacity (g : Graph T) (root : Addr) : Prop :=
  ∀ l : List Addr, l.Nodup → (∀ a ∈ l, ConstLeafAt g root a) → l.length ≤ 65535

/-- `n` is the index tree of `root` with constant objects numbered by `order`:
paths of `n` are exactly source paths, operator nodes keep their arity,
nonconstant leaves get 0, and every occurrence of a constant object gets its
one-based position in `order`. -/
def IndexSpec (g : Graph T) (root : Addr) (order : List Addr) (n : NodeIndex) : Prop :=
  order.Nodup ∧
  (∀ a ∈ order, ConstLeafAt g root a) ∧
  (∀ p a c, Graph.Path g root p a → g.cells a = some c → c.degree = 0 → c.constant = true →
    ∃ x, indexAt n p = some (.leaf x) ∧ 1 ≤ x ∧ x ≤ order.length ∧ order[x - 1]? = some a) ∧
  (∀ p a c, Graph.Path g root p a → g.cells a = some c → c.degree = 0 → c.constant = false →
    indexAt n p = some (.leaf 0)) ∧
  (∀ x, 1 ≤ x → x ≤ order.length → ∃ p a, Graph.Path g root p a ∧ indexAt n p = some (.leaf x)) ∧
  (∀ p q a b ca cb x y, Graph.Path g root p a → Graph.Path g root q b →
    g.cells a = some ca → g.cells b = some cb → ca.degree = 0 → cb.degree = 0 →
    ca.constant = true → cb.constant = true →
    indexAt n p = some (.leaf x) → indexAt n q = some (.leaf y) → (x = y ↔ a = b)) ∧
  (∀ p a c, Graph.Path g root p a → g.cells a = some c → c.degree ≠ 0 →
    ∃ ms, indexAt n p = some (.branch ms) ∧ ms.length = c.children.length) ∧
  (∀ p m, indexAt n p = some m → ∃ a, Graph.Path g root p a)

/-- src/NodeUtils.jl:186-202 on GraphNode (src/base.jl:87-155): for every
finite acyclic initialized source graph (unfolding within `fuel`) holding at
most 65535 distinct constant objects, indexing succeeds, returns the number of
distinct constant objects, and numbers them 1..k in depth-first first-visit
order; two constant occurrences share an index iff they are the same object. -/
def GraphIndexConsistency : Prop :=
  ∀ (T : Type) (g : Graph T) (fuel root : Nat),
    Graph.Acyclic g root →
    (∃ t, Graph.unfold g fuel root = some t) →
    ConstCapacity g root →
    ∃ n count cache, indexGraph g true fuel root = .ok (n, count, cache) ∧
      count = (firstVisitOrder g fuel root).length ∧
      IndexSpec g root (firstVisitOrder g fuel root) n

/-! ### Generic list and path lemmas -/

private theorem gi_getElem_mem {α : Type} : ∀ {l : List α} {i : Nat} {x : α}, l[i]? = some x → x ∈ l
  | [], i, x, h => by simp at h
  | a :: l, 0, x, h => by simp at h; simp [h]
  | a :: l, i + 1, x, h => by
      simp at h
      exact List.mem_cons_of_mem _ (gi_getElem_mem h)

private theorem gi_mem_getElem {α : Type} : ∀ {l : List α} {x : α}, x ∈ l → ∃ i : Nat, l[i]? = some x
  | [], x, h => by simp at h
  | a :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, rfl⟩
      · obtain ⟨i, hi⟩ := gi_mem_getElem h
        exact ⟨i + 1, by simpa using hi⟩

private theorem gi_getElem_lt {α : Type} : ∀ {l : List α} {i : Nat} {x : α}, l[i]? = some x → i < l.length
  | [], i, x, h => by simp at h
  | a :: l, 0, x, _ => by simp
  | a :: l, i + 1, x, h => by
      simp at h
      have := gi_getElem_lt h
      simp only [List.length_cons]
      omega

private theorem gi_exists_getElem {α : Type} : ∀ {l : List α} {i : Nat}, i < l.length → ∃ x, l[i]? = some x
  | [], i, h => by simp at h
  | a :: l, 0, _ => ⟨a, rfl⟩
  | a :: l, i + 1, h => by
      obtain ⟨x, hx⟩ := gi_exists_getElem (l := l) (i := i) (by simp at h; omega)
      exact ⟨x, by simpa using hx⟩

private theorem gi_mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y
  | [], ys, h, x, hx => by simp at hx
  | a :: l, ys, h, x, hx => by
      cases ha : f a with
      | none => simp [List.mapM_cons, ha] at h
      | some b =>
          cases hl : l.mapM f with
          | none => simp [List.mapM_cons, ha, hl] at h
          | some bs =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨b, ha⟩
              · exact gi_mapM_some_mem hl x hx

private theorem gi_mapM_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β} {i : Nat} {y : β}, l.mapM f = some ys → ys[i]? = some y →
      ∃ x, l[i]? = some x ∧ f x = some y
  | [], ys, i, y, h, hy => by
      simp at h
      subst h
      simp at hy
  | a :: l, ys, i, y, h, hy => by
      cases ha : f a with
      | none => simp [List.mapM_cons, ha] at h
      | some b =>
          cases hl : l.mapM f with
          | none => simp [List.mapM_cons, ha, hl] at h
          | some bs =>
              simp [List.mapM_cons, ha, hl] at h
              subst h
              cases i with
              | zero =>
                  simp at hy
                  subst hy
                  exact ⟨a, rfl, ha⟩
              | succ i =>
                  simp at hy
                  obtain ⟨x, hx, hfx⟩ := gi_mapM_get hl hy
                  exact ⟨x, by simpa using hx, hfx⟩

private theorem gi_mapM_some_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, f x = some y) → ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], by simp⟩
  | a :: l, h => by
      obtain ⟨b, hb⟩ := h a (by simp)
      obtain ⟨bs, hbs⟩ := gi_mapM_some_of (l := l) (fun x hx => h x (by simp [hx]))
      exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]⟩

private theorem gi_nodup_snoc : ∀ {O : List Addr} {a : Addr}, O.Nodup → a ∉ O → (O ++ [a]).Nodup
  | [], a, _, _ => by simp
  | b :: O, a, h, ha => by
      rw [List.nodup_cons] at h
      rw [List.cons_append, List.nodup_cons]
      refine ⟨fun hm => ?_, gi_nodup_snoc h.2 (fun hm => ha (List.mem_cons_of_mem _ hm))⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact h.1 hm
      · simp at hm
        subst hm
        exact ha (by simp)

private theorem gi_leaf_path {g : Graph T} {a : Addr} {c : Cell T} {p : List Nat} {z : Addr}
    (hc : g.cells a = some c) (hn : c.children = []) (hp : Graph.Path g a p z) : p = [] ∧ z = a := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hcell hget _ =>
      rw [hc] at hcell
      cases hcell
      rw [hn] at hget
      simp at hget

private theorem gi_lookup_self (k : Addr) (v : NodeIndex) (m : List (Addr × NodeIndex)) :
    ((k, v) :: m).lookup k = some v := by
  simp [List.lookup]

private theorem gi_lookup_ne {k a : Addr} (h : a ≠ k) (v : NodeIndex) (m : List (Addr × NodeIndex)) :
    ((k, v) :: m).lookup a = m.lookup a := by
  have hb : (a == k) = false := by simpa using h
  simp [List.lookup, hb]

/-! ### Positions and first visits -/

private theorem gi_posOf_append_mem : ∀ (O E : List Addr) (a : Addr), a ∈ O → posOf a (O ++ E) = posOf a O
  | [], E, a, h => by simp at h
  | b :: O, E, a, h => by
      simp only [List.cons_append, posOf]
      by_cases hb : b = a
      · simp [hb]
      · have h' : a ∈ O := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hb
          · exact h
        simp [hb, gi_posOf_append_mem O E a h']

private theorem gi_posOf_snoc : ∀ (O : List Addr) (a : Addr), a ∉ O → posOf a (O ++ [a]) = O.length
  | [], a, _ => by simp [posOf]
  | b :: O, a, h => by
      have hb : b ≠ a := fun e => h (by simp [e])
      have h' : a ∉ O := fun m => h (List.mem_cons_of_mem _ m)
      simp [posOf, hb, gi_posOf_snoc O a h']

private theorem gi_getElem_posOf : ∀ {O : List Addr} {a : Addr}, a ∈ O → O[posOf a O]? = some a
  | [], a, h => by simp at h
  | b :: O, a, h => by
      by_cases hb : b = a
      · simp [posOf, hb]
      · have h' : a ∈ O := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hb
          · exact h
        simp [posOf, hb, gi_getElem_posOf h']

private theorem gi_posOf_lt {O : List Addr} {a : Addr} (h : a ∈ O) : posOf a O < O.length :=
  gi_getElem_lt (gi_getElem_posOf h)

private theorem gi_posOf_of_getElem : ∀ {O : List Addr} {j : Nat} {a : Addr},
    O.Nodup → O[j]? = some a → posOf a O = j
  | [], j, a, _, h => by simp at h
  | b :: O, 0, a, _, h => by
      simp at h
      simp [posOf, h]
  | b :: O, j + 1, a, hn, h => by
      simp at h
      rw [List.nodup_cons] at hn
      have ha : a ∈ O := gi_getElem_mem h
      have hb : b ≠ a := fun e => hn.1 (by subst e; exact ha)
      simp [posOf, hb, gi_posOf_of_getElem hn.2 h]

theorem firstVisits_append : ∀ (O l₁ l₂ : List Addr),
    firstVisits O (l₁ ++ l₂) = firstVisits (firstVisits O l₁) l₂
  | O, [], l₂ => rfl
  | O, a :: l₁, l₂ => by
      simp only [List.cons_append, firstVisits]
      exact firstVisits_append _ l₁ l₂

theorem firstVisits_prefix : ∀ (O l : List Addr), ∃ E, firstVisits O l = O ++ E
  | O, [] => ⟨[], by simp [firstVisits]⟩
  | O, a :: l => by
      obtain ⟨E, hE⟩ := firstVisits_prefix (if a ∈ O then O else O ++ [a]) l
      by_cases ha : a ∈ O
      · refine ⟨E, ?_⟩
        show firstVisits (if a ∈ O then O else O ++ [a]) l = O ++ E
        rw [hE, ite_eq_left ha]
      · refine ⟨a :: E, ?_⟩
        show firstVisits (if a ∈ O then O else O ++ [a]) l = O ++ a :: E
        rw [hE, ite_eq_right ha]
        simp

theorem firstVisits_nodup : ∀ (O l : List Addr), O.Nodup → (firstVisits O l).Nodup
  | O, [], h => h
  | O, a :: l, h => by
      show (firstVisits (if a ∈ O then O else O ++ [a]) l).Nodup
      apply firstVisits_nodup
      by_cases ha : a ∈ O
      · rw [ite_eq_left ha]; exact h
      · rw [ite_eq_right ha]; exact gi_nodup_snoc h ha

theorem mem_firstVisits : ∀ {O l : List Addr} {x : Addr}, x ∈ firstVisits O l → x ∈ O ∨ x ∈ l
  | O, [], x, h => .inl h
  | O, a :: l, x, h => by
      have h' : x ∈ firstVisits (if a ∈ O then O else O ++ [a]) l := h
      rcases mem_firstVisits h' with h | h
      · by_cases ha : a ∈ O
        · rw [ite_eq_left ha] at h
          exact .inl h
        · rw [ite_eq_right ha] at h
          rcases List.mem_append.mp h with h | h
          · exact .inl h
          · simp at h
            subst h
            exact .inr (by simp)
      · exact .inr (List.mem_cons_of_mem _ h)

private theorem gi_firstVisits_of_subset : ∀ {O l : List Addr}, (∀ x ∈ l, x ∈ O) → firstVisits O l = O
  | O, [], _ => rfl
  | O, a :: l, h => by
      show firstVisits (if a ∈ O then O else O ++ [a]) l = O
      rw [ite_eq_left (h a (by simp))]
      exact gi_firstVisits_of_subset (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ### Traversal definedness from the unfolding input predicate -/

/-- One successful unfolding level exposes an existing cell whose active child
count equals its degree, and every active child unfolds with one less fuel. -/
theorem unfold_succ_cell {g : Graph T} {f : Nat} {b : Addr} {t : Tree T}
    (h : Graph.unfold g (f + 1) b = some t) :
    ∃ c, g.cells b = some c ∧ c.children.length = c.degree ∧
      (c.degree ≠ 0 → ∀ x ∈ c.children, ∃ u, Graph.unfold g f x = some u) := by
  cases hc : g.cells b with
  | none => simp [Graph.unfold, hc] at h
  | some c =>
      have hlen : c.children.length = c.degree := by
        by_cases hne : c.children.length = c.degree
        · exact hne
        · simp [Graph.unfold, hc, hne] at h
      refine ⟨c, rfl, hlen, ?_⟩
      intro hd x hx
      cases hm : c.children.mapM (Graph.unfold g f) with
      | none => simp [Graph.unfold, hc, hlen, hd, hm] at h
      | some ts => exact gi_mapM_some_mem hm x hx

/-- The preorder inventory is defined whenever the source unfolds. -/
theorem constLeafOccurrences_exists {g : Graph T} :
    ∀ (f : Nat) (b : Addr), (∃ t, Graph.unfold g f b = some t) →
      ∃ l, constLeafOccurrences g f b = some l
  | 0, b, ⟨t, ht⟩ => by simp [Graph.unfold] at ht
  | f + 1, b, ⟨t, ht⟩ => by
      obtain ⟨c, hc, _, hch⟩ := unfold_succ_cell ht
      by_cases hd : c.degree = 0
      · exact ⟨if c.constant then [b] else [], by simp [constLeafOccurrences, hc, hd]⟩
      · obtain ⟨ls, hls⟩ := gi_mapM_some_of (f := constLeafOccurrences g f) (l := c.children)
          (fun x hx => constLeafOccurrences_exists f x (hch hd x hx))
        exact ⟨ls.flatten, by simp [constLeafOccurrences, hc, hd, hls]⟩

/-- Every inventory entry is a constant leaf object reachable from the start. -/
theorem constLeafOccurrences_mem {g : Graph T} :
    ∀ (f : Nat) (b : Addr) (l : List Addr) (x : Addr),
      constLeafOccurrences g f b = some l → x ∈ l → ConstLeafAt g b x
  | 0, b, l, x, h, _ => by simp [constLeafOccurrences] at h
  | f + 1, b, l, x, h, hx => by
      cases hc : g.cells b with
      | none => simp [constLeafOccurrences, hc] at h
      | some c =>
          by_cases hd : c.degree = 0
          · cases hk : c.constant
            · simp [constLeafOccurrences, hc, hd, hk] at h
              subst h
              simp at hx
            · simp [constLeafOccurrences, hc, hd, hk] at h
              subst h
              simp at hx
              subst hx
              exact ⟨[], c, .nil _, hc, hd, hk⟩
          · cases hm : c.children.mapM (constLeafOccurrences g f) with
            | none => simp [constLeafOccurrences, hc, hd, hm] at h
            | some ls =>
                simp [constLeafOccurrences, hc, hd, hm] at h
                subst h
                obtain ⟨l', hl', hxl'⟩ := List.mem_flatten.mp hx
                obtain ⟨i, hi⟩ := gi_mem_getElem hl'
                obtain ⟨y, hy, hocc⟩ := gi_mapM_get hm hi
                obtain ⟨p, c', hp, hc', hd', hk'⟩ := constLeafOccurrences_mem f y l' x hocc hxl'
                exact ⟨i :: p, c', .cons hc hy hp, hc', hd', hk'⟩

private theorem gi_constLeafAt_trans {g : Graph T} {R x y : Addr} {q : List Nat}
    (hq : Graph.Path g R q x) (h : ConstLeafAt g x y) : ConstLeafAt g R y := by
  obtain ⟨p, c, hp, hc, hd, hk⟩ := h
  exact ⟨q ++ p, c, Graph.Path.append hq hp, hc, hd, hk⟩

/-! ### Walk invariants -/

/-- `m` is the index tree of the source object `b` under the numbering `O`. -/
def IndexLabels (g : Graph T) (O : List Addr) (b : Addr) (m : NodeIndex) : Prop :=
  (∀ p a c, Graph.Path g b p a → g.cells a = some c → c.degree = 0 →
    indexAt m p = some (.leaf (if c.constant then posOf a O + 1 else 0))) ∧
  (∀ p a c, Graph.Path g b p a → g.cells a = some c → c.degree ≠ 0 →
    ∃ ms, indexAt m p = some (.branch ms) ∧ ms.length = c.children.length) ∧
  (∀ p m', indexAt m p = some m' → ∃ a, Graph.Path g b p a)

/-- Every constant leaf object below `b` is already numbered by `O`. -/
def IndexCovered (g : Graph T) (O : List Addr) (b : Addr) : Prop :=
  ∀ p a c, Graph.Path g b p a → g.cells a = some c → c.degree = 0 → c.constant = true → a ∈ O

/-- Cached index trees agree with `O`, and every numbered object is cached. -/
def IndexCacheInv (g : Graph T) (O : List Addr) (cache : List (Addr × NodeIndex)) : Prop :=
  (∀ b m, cache.lookup b = some m → IndexLabels g O b m ∧ IndexCovered g O b) ∧
  (∀ a ∈ O, ∃ m, cache.lookup a = some m)

private theorem gi_labels_mono {g : Graph T} {O : List Addr} {b : Addr} {m : NodeIndex} (E : List Addr)
    (hl : IndexLabels g O b m) (hc : IndexCovered g O b) : IndexLabels g (O ++ E) b m := by
  obtain ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, h2, h3⟩
  intro p a c hp hca hd
  rw [h1 p a c hp hca hd]
  cases hk : c.constant
  · simp
  · simp [gi_posOf_append_mem O E a (hc p a c hp hca hd hk)]

private theorem gi_covered_mono {g : Graph T} {O : List Addr} {b : Addr} (E : List Addr)
    (hc : IndexCovered g O b) : IndexCovered g (O ++ E) b :=
  fun p a c hp hca hd hk => List.mem_append_left E (hc p a c hp hca hd hk)

private theorem gi_cacheInv_insert {g : Graph T} {O E : List Addr} {cache : List (Addr × NodeIndex)}
    {b : Addr} {n : NodeIndex}
    (hinv : IndexCacheInv g O cache) (hE : ∀ a ∈ E, a = b)
    (hl : IndexLabels g (O ++ E) b n) (hc : IndexCovered g (O ++ E) b) :
    IndexCacheInv g (O ++ E) ((b, n) :: cache) := by
  constructor
  · intro x m hx
    by_cases hxb : x = b
    · subst hxb
      rw [gi_lookup_self] at hx
      cases hx
      exact ⟨hl, hc⟩
    · rw [gi_lookup_ne hxb] at hx
      obtain ⟨hlx, hcx⟩ := hinv.1 x m hx
      exact ⟨gi_labels_mono E hlx hcx, gi_covered_mono E hcx⟩
  · intro a ha
    by_cases hab : a = b
    · subst hab
      exact ⟨n, gi_lookup_self _ _ _⟩
    · rw [gi_lookup_ne hab]
      rcases List.mem_append.mp ha with ha | ha
      · exact hinv.2 a ha
      · exact absurd (hE a ha) hab

private theorem gi_labels_leaf {g : Graph T} {O : List Addr} {b : Addr} {c : Cell T} {v : Nat}
    (hc : g.cells b = some c) (hn : c.children = []) (hd : c.degree = 0)
    (hv : v = if c.constant then posOf b O + 1 else 0) : IndexLabels g O b (.leaf v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p a c' hp hc' _
    obtain ⟨rfl, rfl⟩ := gi_leaf_path hc hn hp
    rw [hc] at hc'
    cases hc'
    simp [indexAt, hv]
  · intro p a c' hp hc' hd'
    obtain ⟨rfl, rfl⟩ := gi_leaf_path hc hn hp
    rw [hc] at hc'
    cases hc'
    exact absurd hd hd'
  · intro p m h
    cases p with
    | nil => exact ⟨b, .nil b⟩
    | cons i p => simp [indexAt] at h

private theorem gi_covered_leaf {g : Graph T} {O : List Addr} {b : Addr} {c : Cell T}
    (hc : g.cells b = some c) (hn : c.children = []) (hk : c.constant = true → b ∈ O) :
    IndexCovered g O b := by
  intro p a c' hp hc' _ hk'
  obtain ⟨rfl, rfl⟩ := gi_leaf_path hc hn hp
  rw [hc] at hc'
  cases hc'
  exact hk hk'

private theorem gi_labels_branch {g : Graph T} {O : List Addr} {b : Addr} {c : Cell T}
    {ms : List NodeIndex} (hc : g.cells b = some c) (hd : c.degree ≠ 0)
    (hlen : ms.length = c.children.length)
    (hk : ∀ (i : Nat) (x : Addr) (mi : NodeIndex), c.children[i]? = some x → ms[i]? = some mi →
      IndexLabels g O x mi) :
    IndexLabels g O b (.branch ms) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p a c' hp hc' hd'
    cases hp with
    | nil =>
        rw [hc] at hc'
        cases hc'
        exact absurd hd' hd
    | @cons _ x _ i p' c'' hcell hget hp' =>
        rw [hc] at hcell
        cases hcell
        obtain ⟨mi, hmi⟩ := gi_exists_getElem (l := ms) (i := i)
          (by have := gi_getElem_lt hget; omega)
        simp only [indexAt, hmi]
        exact (hk i x mi hget hmi).1 p' a c' hp' hc' hd'
  · intro p a c' hp hc' hd'
    cases hp with
    | nil =>
        rw [hc] at hc'
        cases hc'
        exact ⟨ms, by simp [indexAt], hlen⟩
    | @cons _ x _ i p' c'' hcell hget hp' =>
        rw [hc] at hcell
        cases hcell
        obtain ⟨mi, hmi⟩ := gi_exists_getElem (l := ms) (i := i)
          (by have := gi_getElem_lt hget; omega)
        simp only [indexAt, hmi]
        exact (hk i x mi hget hmi).2.1 p' a c' hp' hc' hd'
  · intro p m' h
    cases p with
    | nil => exact ⟨b, .nil b⟩
    | cons i p' =>
        cases hmi : ms[i]? with
        | none => simp [indexAt, hmi] at h
        | some mi =>
            simp [indexAt, hmi] at h
            obtain ⟨x, hx⟩ := gi_exists_getElem (l := c.children) (i := i)
              (by have := gi_getElem_lt hmi; omega)
            obtain ⟨a, ha⟩ := (hk i x mi hx hmi).2.2 p' m' h
            exact ⟨a, .cons hc hx ha⟩

private theorem gi_covered_branch {g : Graph T} {O : List Addr} {b : Addr} {c : Cell T}
    {ms : List NodeIndex} (hc : g.cells b = some c) (hd : c.degree ≠ 0)
    (hlen : ms.length = c.children.length)
    (hk : ∀ (i : Nat) (x : Addr) (mi : NodeIndex), c.children[i]? = some x → ms[i]? = some mi →
      IndexCovered g O x) :
    IndexCovered g O b := by
  intro p a c' hp hc' hd' hk'
  cases hp with
  | nil =>
      rw [hc] at hc'
      cases hc'
      exact absurd hd' hd
  | @cons _ x _ i p' c'' hcell hget hp' =>
      rw [hc] at hcell
      cases hcell
      obtain ⟨mi, hmi⟩ := gi_exists_getElem (l := ms) (i := i)
        (by have := gi_getElem_lt hget; omega)
      exact hk i x mi hget hmi p' a c' hp' hc' hd' hk'

private theorem gi_walk_leaf {g : Graph T} {M f b i : Nat} {cache : List (Addr × NodeIndex)} {c : Cell T}
    (hl : cache.lookup b = none) (hc : g.cells b = some c) (hd : c.degree = 0) :
    indexGraphWalk g true M (f + 1) b i cache =
      .ok (.leaf (if c.constant then (i + 1) % M else 0), (if c.constant then (i + 1) % M else i),
        (b, .leaf (if c.constant then (i + 1) % M else 0)) :: cache) := by
  cases hk : c.constant <;> simp [indexGraphWalk, hl, Heap.read, hc, hd, hk]

private theorem gi_walk_branch {g : Graph T} {M f b i j : Nat} {cache m : List (Addr × NodeIndex)}
    {c : Cell T} {ns : List NodeIndex}
    (hl : cache.lookup b = none) (hc : g.cells b = some c) (hd : c.degree ≠ 0)
    (hrun : indexChildren (indexGraphWalk g true M f) c.children [] i cache = .ok (ns, j, m)) :
    indexGraphWalk g true M (f + 1) b i cache = .ok (.branch ns, j, (b, .branch ns) :: m) := by
  simp [indexGraphWalk, hl, Heap.read, hc, hd, hrun]

/-- Simulation invariant for one call of the walk at fuel `f` below the global root `R`. -/
def IndexWalkSpec (g : Graph T) (R : Addr) (f : Nat) : Prop :=
  ∀ (b : Addr) (q : List Nat) (O : List Addr) (cache : List (Addr × NodeIndex)),
    Graph.Path g R q b → (∃ t, Graph.unfold g f b = some t) → O.Nodup →
    (∀ a ∈ O, ConstLeafAt g R a) → IndexCacheInv g O cache →
    ∃ l m cache', constLeafOccurrences g f b = some l ∧
      indexGraphWalk g true 65536 f b O.length cache = .ok (m, (firstVisits O l).length, cache') ∧
      IndexLabels g (firstVisits O l) b m ∧ IndexCovered g (firstVisits O l) b ∧
      IndexCacheInv g (firstVisits O l) cache'

private theorem gi_children_spec {g : Graph T} {R : Addr} {f : Nat} (hIH : IndexWalkSpec g R f) :
    ∀ (as : List Addr) (ns : List NodeIndex) (O : List Addr) (cache : List (Addr × NodeIndex)),
      (∀ x ∈ as, (∃ qx, Graph.Path g R qx x) ∧ ∃ u, Graph.unfold g f x = some u) →
      O.Nodup → (∀ a ∈ O, ConstLeafAt g R a) → IndexCacheInv g O cache →
      ∃ ls ms cache', as.mapM (constLeafOccurrences g f) = some ls ∧
        indexChildren (indexGraphWalk g true 65536 f) as ns O.length cache =
          .ok (ns ++ ms, (firstVisits O ls.flatten).length, cache') ∧
        ms.length = as.length ∧
        (∀ (i : Nat) (x : Addr) (mi : NodeIndex), as[i]? = some x → ms[i]? = some mi →
          IndexLabels g (firstVisits O ls.flatten) x mi ∧ IndexCovered g (firstVisits O ls.flatten) x) ∧
        IndexCacheInv g (firstVisits O ls.flatten) cache'
  | [], ns, O, cache, _, _, _, hinv =>
      ⟨[], [], cache, by simp, by simp [indexChildren, firstVisits], rfl, by simp,
        by simpa [firstVisits] using hinv⟩
  | x :: as, ns, O, cache, hall, hnd, hO, hinv => by
      obtain ⟨⟨qx, hqx⟩, hux⟩ := hall x (by simp)
      obtain ⟨l0, m0, c1, hocc0, hwalk0, hlab0, hcov0, hinv1⟩ := hIH x qx O cache hqx hux hnd hO hinv
      have hnd1 : (firstVisits O l0).Nodup := firstVisits_nodup O l0 hnd
      have hO1 : ∀ a ∈ firstVisits O l0, ConstLeafAt g R a := by
        intro a ha
        rcases mem_firstVisits ha with ha | ha
        · exact hO a ha
        · exact gi_constLeafAt_trans hqx (constLeafOccurrences_mem f x l0 a hocc0 ha)
      obtain ⟨ls, ms, c2, hls, hrun, hlen, hlabs, hinv2⟩ :=
        gi_children_spec hIH as (ns ++ [m0]) (firstVisits O l0) c1
          (fun y hy => hall y (List.mem_cons_of_mem _ hy)) hnd1 hO1 hinv1
      have hfv : firstVisits O (l0 :: ls).flatten = firstVisits (firstVisits O l0) ls.flatten := by
        rw [List.flatten_cons, firstVisits_append]
      obtain ⟨E, hE⟩ := firstVisits_prefix (firstVisits O l0) ls.flatten
      refine ⟨l0 :: ls, m0 :: ms, c2, ?_, ?_, by simp [hlen], ?_, ?_⟩
      · simp [List.mapM_cons, hocc0, hls]
      · rw [hfv]
        simp only [indexChildren, hwalk0]
        rw [hrun]
        simp
      · intro i y mi hy hm
        rw [hfv]
        cases i with
        | zero =>
            simp at hy hm
            subst hy
            subst hm
            rw [hE]
            exact ⟨gi_labels_mono E hlab0 hcov0, gi_covered_mono E hcov0⟩
        | succ i =>
            simp at hy hm
            exact hlabs i y mi hy hm
      · rw [hfv]
        exact hinv2

/-- The walk simulates the specification at every fuel for an input whose
distinct constant objects fit in UInt16. -/
theorem indexWalkSpec {g : Graph T} {R : Addr} (hcap : ConstCapacity g R) :
    ∀ f, IndexWalkSpec g R f
  | 0 => by
      intro b q O cache _ hu
      obtain ⟨t, ht⟩ := hu
      simp [Graph.unfold] at ht
  | f + 1 => by
      intro b q O cache hq hu hnd hO hinv
      obtain ⟨t, ht⟩ := hu
      obtain ⟨c, hc, hlen, hch⟩ := unfold_succ_cell ht
      cases hlook : cache.lookup b with
      | some m =>
          obtain ⟨l, hl⟩ := constLeafOccurrences_exists (f + 1) b ⟨t, ht⟩
          obtain ⟨hlab, hcov⟩ := hinv.1 b m hlook
          have hfix : firstVisits O l = O := gi_firstVisits_of_subset (fun x hx => by
            obtain ⟨p, cx, hp, hcx, hdx, hkx⟩ := constLeafOccurrences_mem (f + 1) b l x hl hx
            exact hcov p x cx hp hcx hdx hkx)
          refine ⟨l, m, cache, hl, ?_, ?_, ?_, ?_⟩ <;> rw [hfix]
          · exact indexGraphWalk_cacheHit g 65536 f b O.length cache m hlook
          · exact hlab
          · exact hcov
          · exact hinv
      | none =>
          by_cases hd : c.degree = 0
          · have hnil : c.children = [] := by
              cases hch' : c.children with
              | nil => rfl
              | cons _ _ =>
                  rw [hch'] at hlen
                  simp at hlen
                  omega
            have hw := gi_walk_leaf (M := 65536) (f := f) (i := O.length) hlook hc hd
            cases hcon : c.constant
            · have hocc : constLeafOccurrences g (f + 1) b = some [] := by
                simp [constLeafOccurrences, hc, hd, hcon]
              have hlab : IndexLabels g O b (.leaf 0) := gi_labels_leaf hc hnil hd (by simp [hcon])
              have hcov : IndexCovered g O b := gi_covered_leaf hc hnil (by simp [hcon])
              refine ⟨[], .leaf 0, (b, .leaf 0) :: cache, hocc, ?_, ?_, ?_, ?_⟩
              · simpa [firstVisits, hcon] using hw
              · simpa [firstVisits] using hlab
              · simpa [firstVisits] using hcov
              · have := gi_cacheInv_insert (E := []) hinv (by simp) (by simpa using hlab)
                  (by simpa using hcov)
                simpa [firstVisits] using this
            · have hbO : b ∉ O := fun hm => by
                obtain ⟨m', hm'⟩ := hinv.2 b hm
                rw [hlook] at hm'
                cases hm'
              have hfv : firstVisits O [b] = O ++ [b] := by
                show (if b ∈ O then O else O ++ [b]) = O ++ [b]
                rw [ite_eq_right hbO]
              have hcapb : (O ++ [b]).length ≤ 65535 := hcap _ (gi_nodup_snoc hnd hbO) (fun a ha => by
                rcases List.mem_append.mp ha with ha | ha
                · exact hO a ha
                · simp at ha
                  subst ha
                  exact ⟨q, c, hq, hc, hd, hcon⟩)
              have hmod : (O.length + 1) % 65536 = O.length + 1 :=
                Nat.mod_eq_of_lt (by simp at hcapb; omega)
              have hocc : constLeafOccurrences g (f + 1) b = some [b] := by
                simp [constLeafOccurrences, hc, hd, hcon]
              have hlab : IndexLabels g (O ++ [b]) b (.leaf (O.length + 1)) :=
                gi_labels_leaf hc hnil hd (by simp [hcon, gi_posOf_snoc O b hbO])
              have hcov : IndexCovered g (O ++ [b]) b := gi_covered_leaf hc hnil (fun _ => by simp)
              refine ⟨[b], .leaf (O.length + 1), (b, .leaf (O.length + 1)) :: cache, hocc, ?_, ?_, ?_, ?_⟩ <;>
                rw [hfv]
              · simpa [hcon, hmod] using hw
              · exact hlab
              · exact hcov
              · exact gi_cacheInv_insert hinv (by simp) hlab hcov
          · have hkids : ∀ x ∈ c.children, (∃ qx, Graph.Path g R qx x) ∧ ∃ u, Graph.unfold g f x = some u := by
              intro x hx
              obtain ⟨i, hi⟩ := gi_mem_getElem hx
              exact ⟨⟨q ++ [i], Graph.Path.append hq (.cons hc hi (.nil x))⟩, hch hd x hx⟩
            obtain ⟨ls, ms, cache', hls, hrun, hmlen, hlabs, hinv'⟩ :=
              gi_children_spec (indexWalkSpec hcap f) c.children [] O cache hkids hnd hO hinv
            have hocc : constLeafOccurrences g (f + 1) b = some ls.flatten := by
              simp [constLeafOccurrences, hc, hd, hls]
            have hlab : IndexLabels g (firstVisits O ls.flatten) b (.branch ms) :=
              gi_labels_branch hc hd hmlen (fun i x mi hx hm => (hlabs i x mi hx hm).1)
            have hcov : IndexCovered g (firstVisits O ls.flatten) b :=
              gi_covered_branch hc hd hmlen (fun i x mi hx hm => (hlabs i x mi hx hm).2)
            refine ⟨ls.flatten, .branch ms, (b, .branch ms) :: cache', hocc, ?_, hlab, hcov, ?_⟩
            · exact gi_walk_branch hlook hc hd (by simpa using hrun)
            · have := gi_cacheInv_insert (E := []) hinv' (by simp) (by simpa using hlab)
                (by simpa using hcov)
              simpa using this

/-- Index labels for the whole source satisfy the public specification. -/
theorem indexSpec_of_labels {g : Graph T} {O : List Addr} {root : Addr} {n : NodeIndex}
    (hlab : IndexLabels g O root n) (hcov : IndexCovered g O root) (hnd : O.Nodup)
    (hO : ∀ a ∈ O, ConstLeafAt g root a) : IndexSpec g root O n := by
  obtain ⟨h1, h2, h3⟩ := hlab
  refine ⟨hnd, hO, ?_, ?_, ?_, ?_, h2, h3⟩
  · intro p a c hp hc hd hk
    have ha := hcov p a c hp hc hd hk
    have hlt := gi_posOf_lt ha
    refine ⟨posOf a O + 1, by rw [h1 p a c hp hc hd]; simp [hk], by omega, by omega, ?_⟩
    simpa using gi_getElem_posOf ha
  · intro p a c hp hc hd hk
    rw [h1 p a c hp hc hd]
    simp [hk]
  · intro x hx1 hx2
    obtain ⟨a, ha⟩ := gi_exists_getElem (l := O) (i := x - 1) (by omega)
    obtain ⟨p, c, hp, hc, hd, hk⟩ := hO a (gi_getElem_mem ha)
    refine ⟨p, a, hp, ?_⟩
    rw [h1 p a c hp hc hd, gi_posOf_of_getElem hnd ha]
    have hx : x - 1 + 1 = x := by omega
    simp [hk, hx]
  · intro p q a b ca cb x y hp hq hca hcb hda hdb hka hkb hx hy
    rw [h1 p a ca hp hca hda] at hx
    rw [h1 q b cb hq hcb hdb] at hy
    simp [hka] at hx
    simp [hkb] at hy
    subst hx
    subst hy
    have ha := hcov p a ca hp hca hda hka
    have hb := hcov q b cb hq hcb hdb hkb
    constructor
    · intro he
      have e : posOf a O = posOf b O := by omega
      have hpa := gi_getElem_posOf ha
      rw [e, gi_getElem_posOf hb] at hpa
      exact (Option.some.inj hpa).symm
    · intro he
      subst he
      rfl

theorem graphIndexConsistency_proven : GraphIndexConsistency := by
  intro T g fuel root _hacyc hu hcap
  have hinv0 : IndexCacheInv g [] [] :=
    ⟨fun b m h => by simp [List.lookup] at h, fun a h => by simp at h⟩
  obtain ⟨l, n, cache, hocc, hrun, hlab, hcov, _⟩ :=
    indexWalkSpec hcap fuel root [] [] [] (.nil root) hu List.nodup_nil (by simp) hinv0
  have hord : firstVisitOrder g fuel root = firstVisits [] l := by
    simp [firstVisitOrder, hocc]
  rw [hord]
  exact ⟨n, (firstVisits [] l).length, cache, hrun, rfl,
    indexSpec_of_labels hlab hcov (firstVisits_nodup [] l List.nodup_nil) (fun a ha => by
      rcases mem_firstVisits ha with ha | ha
      · simp at ha
      · exact constLeafOccurrences_mem fuel root l a hocc ha)⟩

/-! ### Satisfiable hypotheses on a shared graph -/

private theorem gi_alias0 : aliasGraph.cells 0 = some (constantCell 1) := rfl
private theorem gi_alias1 : aliasGraph.cells 1 = some (operatorCell 1 [0, 0]) := rfl

private theorem gi_alias_reach {p : List Nat} {z : Addr} (hp : Graph.Path aliasGraph 1 p z) :
    (p = [] ∧ z = 1) ∨ z = 0 := by
  cases hp with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons _ x _ i p' c hcell hget hp' =>
      rw [gi_alias1] at hcell
      cases hcell
      have hx : x = 0 := by
        have hm := gi_getElem_mem hget
        simpa [operatorCell] using hm
      subst hx
      exact .inr (gi_leaf_path gi_alias0 rfl hp').2

/-- The graph `[c, c]` sharing one constant object satisfies every hypothesis. -/
example : Graph.Acyclic aliasGraph 1 ∧ (∃ t, Graph.unfold aliasGraph 2 1 = some t) ∧
    ConstCapacity aliasGraph 1 := by
  refine ⟨?_, ⟨.branch 1 [.const 1, .const 1], rfl⟩, ?_⟩
  · intro a ⟨p, hp⟩ q hq
    rcases gi_alias_reach hp with ⟨_, rfl⟩ | rfl
    · rcases gi_alias_reach hq with ⟨hq', _⟩ | h
      · exact hq'
      · exact absurd h (by decide)
    · exact (gi_leaf_path gi_alias0 rfl hq).1
  · intro l hnd hl
    have h0 : ∀ a ∈ l, a = 0 := by
      intro a ha
      obtain ⟨p, c, hp, hc, hd, _⟩ := hl a ha
      rcases gi_alias_reach hp with ⟨_, rfl⟩ | h
      · rw [gi_alias1] at hc
        cases hc
        simp [operatorCell] at hd
      · exact h
    rcases l with _ | ⟨x, _ | ⟨y, r⟩⟩
    · simp
    · simp
    · exfalso
      have hx := h0 x (by simp)
      have hy := h0 y (by simp)
      rw [List.nodup_cons] at hnd
      exact hnd.1 (by simp [hx, hy])

end DynExpr.NodeUtils
