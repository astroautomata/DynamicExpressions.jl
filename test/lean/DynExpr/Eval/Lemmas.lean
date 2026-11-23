import DynExpr.Eval.Props

/-!
General lemmas for the evaluator proofs: `Except`/`Option` traversals, matrix
indexing, buffer allocation, operator lookup and denotations.
-/

namespace DynExpr.Eval

section general

@[simp] theorem jl_pure {α : Type} (a : α) : (pure a : Jl α) = .ok a := rfl
@[simp] theorem jl_ok_bind {α β : Type} (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] theorem jl_error_bind {α β : Type} (e : JlError) (f : α → Jl β) :
    (Except.error e >>= f : Jl β) = .error e := rfl

/-- `mapM` in `Jl` with every call succeeding. -/
theorem mapM_jl_eq {α β : Type} (F : α → Jl β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, F a = .ok (g a)) → l.mapM F = .ok (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := mapM_jl_eq F g l (fun b hb => h b (by simp [hb]))
    simp [List.mapM_cons, ha, hl]

/-- `mapM` in `Option` with every call succeeding. -/
theorem mapM_opt_eq {α β : Type} (F : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, F a = some (g a)) → l.mapM F = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := mapM_opt_eq F g l (fun b hb => h b (by simp [hb]))
    simp [List.mapM_cons, ha, hl]

theorem range_map_size {β : Type} (n : Nat) (g : Nat → β) :
    ((List.range n).map g).toArray.size = n := by simp

theorem range_map_get {β : Type} (n : Nat) (g : Nat → β) (j : Nat) (hj : j < n) :
    ((List.range n).map g).toArray[j]? = some (g j) := by
  simp [hj]

end general

section matrix
variable {T : Type}

private theorem idx_lt (nr nc a b : Nat) (ha : a < nr) (hb : b < nc) : nr * b + a < nr * nc := by
  calc nr * b + a < nr * b + nr := by omega
    _ = nr * (b + 1) := by rw [Nat.mul_succ]
    _ ≤ nr * nc := Nat.mul_le_mul_left nr hb

/-- Every matrix is the column-major `ofFn` of its own storage. -/
theorem JMat.eq_ofFn (X : JMat T) :
    X = JMat.ofFn X.nrows X.ncols (fun a b =>
      X.data[X.nrows * b.val + a.val]'(by rw [X.size_eq]; exact idx_lt _ _ _ _ a.isLt b.isLt)) := by
  rcases X with ⟨nr, nc, data, hs⟩
  simp only [JMat.ofFn, JMat.mk.injEq, true_and]
  apply Array.ext
  · simp [hs]
  · intro k h1 h2
    simp only [Array.getElem_ofFn]
    congr 1
    have hn : 0 < nr := by
      rcases Nat.eq_zero_or_pos nr with h | h
      · subst h; simp at h2
      · exact h
    exact (Nat.div_add_mod k nr).symm

/-- Explicit value of a valid one-based matrix access. -/
theorem JMat.get?_eq (X : JMat T) (i j : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ X.nrows)
    (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    X.get? i j = .ok (X.data[X.nrows * (j - 1) + (i - 1)]'(by
      rw [X.size_eq]; exact idx_lt _ _ _ _ (by omega) (by omega))) := by
  conv => lhs; rw [JMat.eq_ofFn X]
  rw [JMat.get_ofFn _ _ _ _ _ hi1 hi2 hj1 hj2]

/-- `@inbounds X[f, :]` for a valid row. -/
theorem rowInb_eq (X : JMat T) (f : Nat) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows) :
    rowInb X f = .ok (Array.ofFn fun j : Fin X.ncols =>
      X.data[X.nrows * j.val + (f - 1)]'(by
        rw [X.size_eq]; exact idx_lt _ _ _ _ (by omega) j.isLt)) := by
  simp [rowInb, JMat.row, hf1, hf2]

/-- Linear `feature_at` reads the matrix entry `(f, j)`. -/
theorem featureAt_eq (X : JMat T) (f j : Nat) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows)
    (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    featureAt X f j = X.get? f j := by
  rw [JMat.get?_eq X f j hf1 hf2 hj1 hj2]
  have hlt := idx_lt X.nrows X.ncols (f - 1) (j - 1) (by omega) (by omega)
  have hs := X.size_eq
  have hk : f + (j - 1) * X.nrows - 1 = X.nrows * (j - 1) + (f - 1) := by
    rw [Nat.mul_comm]; omega
  unfold featureAt linInb
  split
  · simp [hk]
  · exfalso; omega

end matrix

section scalar
variable {T : Type} [JlScalar T]

/-- Value of a denotation, with `undef` when undefined. -/
def vx (o : OpEnum T) (x : Nat → Option T) (t : Tree T) : T :=
  (t.denote o x).getD JlScalar.undef

/-- Canonical evaluation output: the denotation at every sample. -/
def canon (o : OpEnum T) (X : JMat T) (t : Tree T) : JVec T :=
  ((List.range X.ncols).map (fun j => vx o (col X (j + 1)) t)).toArray

theorem AllValid.some (o : OpEnum T) (x : Nat → Option T) (t : Tree T) (h : AllValid o x t) :
    t.denote o x = some (vx o x t) := by
  cases t with
  | const v => simp [vx, Tree.denote]
  | feature i =>
    simp only [AllValid] at h
    obtain ⟨v, hv, _⟩ := h
    simp [vx, Tree.denote, hv]
  | branch op cs =>
    simp only [AllValid] at h
    obtain ⟨_, v, hv, _⟩ := h
    simp [vx, hv]

theorem AllValid.valid (o : OpEnum T) (x : Nat → Option T) (t : Tree T) (h : AllValid o x t) :
    valid (vx o x t) = true := by
  cases t with
  | const v => simpa [AllValid, vx, Tree.denote] using h
  | feature i =>
    simp only [AllValid] at h
    obtain ⟨v, hv, hval⟩ := h
    simpa [vx, Tree.denote, hv] using hval
  | branch op cs =>
    simp only [AllValid] at h
    obtain ⟨_, v, hv, hval⟩ := h
    simpa [vx, hv] using hval

theorem AllValid.children (o : OpEnum T) (x : Nat → Option T) (op : Nat) (cs : List (Tree T))
    (h : AllValid o x (.branch op cs)) : ∀ c ∈ cs, AllValid o x c := by
  simp only [AllValid] at h
  exact h.1

/-- The denotation of a branch whose children are defined. -/
theorem vx_branch (o : OpEnum T) (x : Nat → Option T) (op : Nat) (cs : List (Tree T))
    (g : List T → T) (hg : o.lookup cs.length op = some g)
    (hc : ∀ c ∈ cs, c.denote o x = some (vx o x c)) :
    vx o x (.branch op cs) = g (cs.map (vx o x)) := by
  have hm := mapM_opt_eq (Tree.denote o x) (vx o x) cs hc
  simp [vx, Tree.denote, hg, hm]

/-- One-based lookup succeeds for in-range indices and agrees with `@nif`. -/
theorem nifOp_lookup (o : OpEnum T) (d op : Nat) (hd : 1 ≤ d) (h1 : 1 ≤ op) (h2 : op ≤ o.nops d) :
    ∃ g, o.lookup d op = some g ∧ nifOp (opsOf o d) op = .ok g := by
  have hlen : op ≤ (opsOf o d).length := by
    simpa [OpEnum.nops, opsOf, show d ≠ 0 by omega] using h2
  refine ⟨(opsOf o d)[op - 1]'(by omega), ?_, ?_⟩
  · simp [OpEnum.lookup, opsOf, show d ≠ 0 by omega, show op ≠ 0 by omega]
  · unfold nifOp
    have hne : (opsOf o d) ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    rw [List.getLast?_eq_some_getLast hne]
    simp only
    congr 1
    by_cases hlt : op < (opsOf o d).length
    · rw [if_pos ⟨h1, hlt⟩, List.getElem?_eq_getElem (by omega)]
      rfl
    · have heq : op = (opsOf o d).length := by omega
      simp only [h1, hlt, and_false, ↓reduceIte]
      rw [List.getLast_eq_getElem]
      congr 1
      omega

omit [JlScalar T] in
/-- Bounds-checked lookup agrees with one-based lookup. -/
theorem idxOp_lookup (o : OpEnum T) (d op : Nat) (g : List T → T) (hd : 1 ≤ d)
    (hg : o.lookup d op = some g) : idxOp (opsOf o d) op = .ok g := by
  have hop : op ≠ 0 := by
    intro h; simp [OpEnum.lookup, h] at hg
  simp only [OpEnum.lookup, show d ≠ 0 by omega, hop, or_self, ↓reduceIte] at hg
  simp [idxOp, hop, opsOf, hg]

end scalar

end DynExpr.Eval
