import DynExpr.NoAlias.Core
import DynExpr.Simplify.Combine
import DynExpr.Simplify.CombineProofs

/-!
`combine_operators!` on `Node{T,2}` (src/Simplify.jl:32-126, mirrored as
`DynExpr.Simplify.combineOps`) never creates aliasing in plain `Node` trees.

Each step of the mirror (recursive calls, `set_child!` on the current node,
the commutative and subtraction rewrites) satisfies `Step g a g' r`: the
returned root `r` is alias-free in the new heap, reaches only objects of the
input tree at `a`, and nothing outside the input tree changes. Intermediate
heaps may be aliased (the swap at src/Simplify.jl:58-62 first stores the same
child twice); each rewrite is checked on the final child list of the rewired
node, whose entries come from pairwise disjoint subtrees of the old node.
-/

namespace DynExpr.NoAlias
open DynExpr Graph Simplify

variable {T : Type}

/-- The returned root is alias-free, uses only objects reachable from the old
root, and objects outside the old tree keep their contents. -/
private def Step (g : Graph T) (a : Addr) (g' : Graph T) (r : Addr) : Prop :=
  NoAlias g' r ∧ (∀ x, Reachable g' r x → Reachable g a x) ∧
    (∀ x, ¬ Reachable g a x → g'.cells x = g.cells x)

private theorem step_refl {g : Graph T} {a : Addr} (h : NoAlias g a) : Step g a g a :=
  ⟨h, fun _ hx => hx, fun _ _ => rfl⟩

private theorem step_trans {g g1 g2 : Graph T} {a b r : Addr} (h1 : Step g a g1 b)
    (h2 : Step g1 b g2 r) : Step g a g2 r :=
  ⟨h2.1, fun x hx => h1.2.1 x (h2.2.1 x hx),
    fun x hx => by rw [h2.2.2 x (fun h => hx (h1.2.1 x h)), h1.2.2 x hx]⟩

/-! ## Inverting the monadic primitives -/

private theorem bind_ok {α β : Type} {x : Jl α} {f : α → Jl β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem pure_inv {α : Type} {x y : α} (h : (pure x : Jl α) = .ok y) : x = y := by
  cases h; rfl

private theorem read_inv {g : Graph T} {a : Addr} {c : Cell T} (h : g.read a = .ok c) :
    g.cells a = some c := by
  unfold Heap.read at h
  cases hc : g.cells a with
  | none => rw [hc] at h; cases h
  | some v => rw [hc] at h; cases h; rfl

private theorem childAt_inv {c : Cell T} {i : Nat} {b : Addr} (h : childAt c i = .ok b) :
    c.children[i - 1]? = some b := by
  unfold childAt at h
  split at h
  · cases h
  · cases hx : c.children[i - 1]? with
    | none => rw [hx] at h; cases h
    | some v => rw [hx] at h; cases h; rfl

private theorem childOf_inv {g : Graph T} {a : Addr} {i : Nat} {b : Addr}
    (h : childOf g a i = .ok b) : ∃ c, g.cells a = some c ∧ c.children[i - 1]? = some b := by
  unfold childOf at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  exact ⟨c, read_inv hc, childAt_inv h⟩

private theorem childOf_at {g : Graph T} {a : Addr} {c : Cell T} {i : Nat} {b : Addr}
    (hc : g.cells a = some c) (h : childOf g a i = .ok b) : c.children[i - 1]? = some b := by
  obtain ⟨c', hc', h'⟩ := childOf_inv h
  rw [hc] at hc'
  cases hc'
  exact h'

private theorem set_of_le : ∀ {l : List Addr} {n : Nat} {b : Addr}, l.length ≤ n → l.set n b = l
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | x :: l, _ + 1, _, h => congrArg (x :: ·) (set_of_le (l := l) (Nat.le_of_succ_le_succ h))

private theorem setChild_at {g g' : Graph T} {a : Addr} {c : Cell T} {i : Nat} {b : Addr}
    (hc : g.cells a = some c) (h : setChild g a i b = .ok g') :
    g'.cells a = some { c with children := c.children.set (i - 1) b } ∧
      ∀ x, x ≠ a → g'.cells x = g.cells x := by
  unfold setChild at h
  obtain ⟨c', hc', h⟩ := bind_ok h
  rw [read_inv hc'] at hc
  cases hc
  split at h
  · cases h
  · split at h
    · have hw := write_cells h
      exact ⟨hw.1, hw.2.1⟩
    · cases h
      refine ⟨?_, fun _ _ => rfl⟩
      rw [set_of_le (by omega)]
      exact read_inv hc'

private theorem setVal_inv {g g' : Graph T} {a : Addr} {v : T} (h : setVal g a v = .ok g') :
    (∀ x, kids g' x = kids g x) ∧ ∀ x, x ≠ a → g'.cells x = g.cells x := by
  unfold setVal at h
  obtain ⟨c, hc, h⟩ := bind_ok h
  have hw := write_cells h
  refine ⟨fun x => ?_, hw.2.1⟩
  by_cases hx : x = a
  · subst hx
    simp [kids, hw.1, read_inv hc]
  · exact write_kids_off h x hx

private theorem one_cons {l : List Addr} {x : Addr} (h : l[0]? = some x) :
    ∃ rest, l = x :: rest := by
  cases l with
  | nil => simp at h
  | cons y rest => simp at h; exact ⟨rest, by rw [h]⟩

private theorem two_cons {l : List Addr} {x y : Addr} (hx : l[0]? = some x)
    (hy : l[1]? = some y) : ∃ rest, l = x :: y :: rest := by
  obtain ⟨t, rfl⟩ := one_cons hx
  obtain ⟨rest, rfl⟩ := one_cons (l := t) (by simpa using hy)
  exact ⟨rest, rfl⟩

private theorem ne_of_not_reach {g : Graph T} {a z : Addr} (hz : ¬ Reachable g a z) : z ≠ a := by
  intro e
  subst e
  exact hz (reach_refl g z)

private theorem ne_of_reach {g : Graph T} {b z a : Addr} (hz : Reachable g b z)
    (ha : ¬ Reachable g b a) : z ≠ a := by
  intro e
  subst e
  exact ha hz

/-! ## Rebuilding one node from disjoint old subtrees -/

private theorem nodup_idx {l : List Addr} (hl : l.Nodup) :
    ∀ {i j : Nat} {x : Addr}, l[i]? = some x → l[j]? = some x → i = j := by
  induction l with
  | nil => intro i j x hi; simp at hi
  | cons y ys ih =>
    intro i j x hi hj
    have hy : y ∉ ys := (List.nodup_cons.mp hl).1
    have hys := (List.nodup_cons.mp hl).2
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        simp only [List.getElem?_cons_succ] at hj
        subst hi
        exact absurd (List.mem_of_getElem? hj) hy
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        simp only [List.getElem?_cons_succ] at hi
        subst hj
        exact absurd (List.mem_of_getElem? hi) hy
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact congrArg Nat.succ (ih hys hi hj)

/-- The node at `a` gets the child list `l`; the child at position `i` is an
alias-free tree living inside the old subtree of `os[i]`, where `os` lists the
old children in some order. Then `a` is alias-free again. -/
private theorem node_step {g g' : Graph T} {a : Addr} {c : Cell T} {l os : List Addr}
    (h : NoAlias g a) (hc : g.cells a = some c) (hk : kids g' a = some l)
    (hp : os.Perm c.children)
    (hch : ∀ (i : Nat) b, l[i]? = some b → ∃ o, os[i]? = some o ∧ NoAlias g' b ∧
      ∀ x, Reachable g' b x → Reachable g o x)
    (hfr : ∀ x, ¬ Reachable g a x → g'.cells x = g.cells x) : Step g a g' a := by
  obtain ⟨c', hc', rfl⟩ := cell_of_kids hk
  have hnd : os.Nodup := hp.nodup_iff.mpr (noAlias_kids_nodup h hc)
  have hmem : ∀ {i : Nat} {o}, os[i]? = some o → o ∈ c.children :=
    fun ho => hp.subset (List.mem_of_getElem? ho)
  have sep : ∀ {i j : Nat} {b b' z}, c'.children[i]? = some b → c'.children[j]? = some b' →
      Reachable g' b z → Reachable g' b' z → i = j := by
    intro i j b b' z hb hb' hz hz'
    obtain ⟨o, ho, -, hro⟩ := hch i b hb
    obtain ⟨o', ho', -, hro'⟩ := hch j b' hb'
    by_cases hoo : o = o'
    · subst hoo
      exact nodup_idx hnd ho ho'
    · exact (noAlias_mem_disjoint h hc (hmem ho) (hmem ho') hoo z (hro z hz) (hro' z hz')).elim
  refine ⟨noAlias_node hc' ?_ ?_ ?_ ?_, ?_, hfr⟩
  · unfold List.Nodup
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    have hi' : c'.children[i]? = some c'.children[i] := by simp [List.getElem?_eq_getElem hi]
    have hj' : c'.children[j]? = some c'.children[i] := by
      rw [heq]; simp [List.getElem?_eq_getElem hj]
    have := sep hi' hj' (reach_refl g' _) (reach_refl g' _)
    omega
  · intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨o, -, hn, -⟩ := hch i b hi
    exact hn
  · intro b hb hba
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨o, ho, -, hro⟩ := hch i b hi
    exact noAlias_child_not_reach h hc (hmem ho) (hro a hba)
  · intro b hb b' hb' hne z hz hz'
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb'
    have hij := sep hi hj hz hz'
    subst hij
    rw [hi] at hj
    cases hj
    exact hne rfl
  · intro x hx
    rcases reach_inv hx with rfl | ⟨c'', b, hc'', hb, hbx⟩
    · exact reach_refl g _
    · rw [hc'] at hc''
      cases hc''
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      obtain ⟨o, ho, -, hro⟩ := hch i b hi
      exact reach_trans (reach_mem hc (hmem ho)) (hro x hbx)

/-- Only the child list of `a` and value fields changed: each new child of
`a` is an old descendant inside the subtree of the matching old child. -/
private theorem rewire_step {g g' : Graph T} {a : Addr} {c : Cell T} {l os : List Addr}
    (h : NoAlias g a) (hc : g.cells a = some c) (hk : kids g' a = some l)
    (hp : os.Perm c.children)
    (hch : ∀ (i : Nat) b, l[i]? = some b → ∃ o, os[i]? = some o ∧ Reachable g o b)
    (hoff : ∀ x, x ≠ a → kids g' x = kids g x)
    (hfr : ∀ x, ¬ Reachable g a x → g'.cells x = g.cells x) : Step g a g' a := by
  refine node_step h hc hk hp (fun i b hb => ?_) hfr
  obtain ⟨o, ho, hob⟩ := hch i b hb
  have hmo : o ∈ c.children := hp.subset (List.mem_of_getElem? ho)
  have hnr : ¬ Reachable g b a := fun hba =>
    noAlias_child_not_reach h hc hmo (reach_trans hob hba)
  have hs : SameKidsOn g g' b := sameKidsOn_of_frame hoff hnr
  exact ⟨o, ho, noAlias_transfer hs (noAlias_reach h (reach_trans (reach_mem hc hmo) hob)),
    fun x hx => reach_trans hob ((reach_transfer hs).mp hx)⟩

/-- A descendant becomes the new root and no child reference changed. -/
private theorem desc_step {g g' : Graph T} {a r : Addr} (h : NoAlias g a)
    (hr : Reachable g a r) (hoff : ∀ x, kids g' x = kids g x)
    (hfr : ∀ x, ¬ Reachable g a x → g'.cells x = g.cells x) : Step g a g' r := by
  have hs : SameKidsOn g g' r := fun x _ => hoff x
  exact ⟨noAlias_transfer hs (noAlias_reach h hr),
    fun x hx => reach_trans hr ((reach_transfer hs).mp hx), hfr⟩

private theorem sameKids_of_eq {g g' : Graph T} {b : Addr}
    (h : ∀ z, Reachable g b z → g'.cells z = g.cells z) : SameKidsOn g g' b :=
  fun z hz => by simp only [kids, h z hz]

private theorem sub_of_eq {g g' g0 : Graph T} {b o : Addr} (hb : NoAlias g b)
    (heq : ∀ z, Reachable g b z → g'.cells z = g.cells z)
    (ho : ∀ z, Reachable g b z → Reachable g0 o z) :
    NoAlias g' b ∧ ∀ z, Reachable g' b z → Reachable g0 o z := by
  have hs := sameKids_of_eq heq
  exact ⟨noAlias_transfer hs hb, fun z hz => ho z ((reach_transfer hs).mp hz)⟩

private theorem origins2 {g : Graph T} {x y x' y' : Addr} {rest : List Addr}
    (hx : Reachable g x' x) (hy : Reachable g y' y) :
    ∀ (i : Nat) b, (x :: y :: rest)[i]? = some b → ∃ o, (x' :: y' :: rest)[i]? = some o ∧
      Reachable g o b
  | 0, b, hb => ⟨x', rfl, by simp at hb; exact hb ▸ hx⟩
  | 1, b, hb => ⟨y', rfl, by simp at hb; exact hb ▸ hy⟩
  | _ + 2, b, hb => ⟨b, by simpa using hb, reach_refl g b⟩

/-- The two leading children of `a` were rewired (from inside the subtrees of
`x'` and `y'`) and then the value of a node of the old tree was set. -/
private theorem finish_step {g g2 g3 : Graph T} {a w : Addr} {c : Cell T} {x y x' y' : Addr}
    {rest : List Addr} {v : T} (h : NoAlias g a) (hc : g.cells a = some c)
    (hp : (x' :: y' :: rest).Perm c.children) (hx : Reachable g x' x) (hy : Reachable g y' y)
    (hk : kids g2 a = some (x :: y :: rest)) (hoff : ∀ z, z ≠ a → g2.cells z = g.cells z)
    (h3 : setVal g2 w v = .ok g3) (hw : Reachable g a w) : Step g a g3 a := by
  obtain ⟨hk3, hf3⟩ := setVal_inv h3
  refine rewire_step h hc (by rw [hk3]; exact hk) hp (origins2 hx hy) (fun z hz => ?_)
    (fun z hz => ?_)
  · rw [hk3]
    simp only [kids, hoff z hz]
  · rw [hf3 z (ne_of_reach hw hz).symm, hoff z (ne_of_not_reach hz)]

/-! ## The rewrite blocks -/

section Blocks

variable [Add T] [Mul T] [Sub T]

/-- The commutative block after the optional swap (src/Simplify.jl:63-79). -/
private def commTail (o : CEnum T) (g : Graph T) (tree : Addr) (op : Nat) :
    Jl (Addr × Graph T) := do
  let topconstant ← valOf g (← childOf g tree 2)
  let below ← childOf g tree 1
  let bc ← g.read below
  if bc.degree = 2 ∧ bc.op = op then
    let b1 ← childAt bc 1
    if ← isConstAt g b1 then
      let f ← o.binop op
      let g ← setVal g b1 (f.eval (← valOf g b1) topconstant)
      return (below, g)
    else
      let b2 ← childAt bc 2
      if ← isConstAt g b2 then
        let f ← o.binop op
        let g ← setVal g b2 (f.eval (← valOf g b2) topconstant)
        return (below, g)
      else return (tree, g)
  else return (tree, g)

private theorem commTail_step {o : CEnum T} {g g' : Graph T} {a r : Addr} {op : Nat}
    (h : NoAlias g a) (ht : commTail o g a op = .ok (r, g')) : Step g a g' r := by
  unfold commTail at ht
  obtain ⟨_, -, ht⟩ := bind_ok ht
  obtain ⟨_, -, ht⟩ := bind_ok ht
  obtain ⟨below, hbelow, ht⟩ := bind_ok ht
  obtain ⟨bc, hbc, ht⟩ := bind_ok ht
  have hbc := read_inv hbc
  obtain ⟨ca, hca, hbelow⟩ := childOf_inv hbelow
  have hrb : Reachable g a below := reach_child hca hbelow
  have leaf : ∀ {i w} {v : T} {g2 : Graph T}, childAt bc i = .ok w → setVal g w v = .ok g2 →
      Step g a g2 below := by
    intro i w v g2 hw hs
    obtain ⟨hk, hf⟩ := setVal_inv hs
    have hrw : Reachable g a w := reach_trans hrb (reach_child hbc (childAt_inv hw))
    exact desc_step h hrb hk (fun z hz => hf z (ne_of_reach hrw hz).symm)
  split at ht
  · obtain ⟨_, hb1, ht⟩ := bind_ok ht
    obtain ⟨_, -, ht⟩ := bind_ok ht
    split at ht
    · obtain ⟨_, -, ht⟩ := bind_ok ht
      obtain ⟨_, -, ht⟩ := bind_ok ht
      obtain ⟨g2, hg2, ht⟩ := bind_ok ht
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
      exact leaf hb1 hg2
    · obtain ⟨_, hb2, ht⟩ := bind_ok ht
      obtain ⟨_, -, ht⟩ := bind_ok ht
      split at ht
      · obtain ⟨_, -, ht⟩ := bind_ok ht
        obtain ⟨_, -, ht⟩ := bind_ok ht
        obtain ⟨g2, hg2, ht⟩ := bind_ok ht
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
        exact leaf hb2 hg2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
        exact step_refl h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
    exact step_refl h

/-- Commutative block (src/Simplify.jl:54-79): the swap rewires `a`, then the
result is either `a` or its first child with one constant leaf updated. -/
private theorem commBlock_step {o : CEnum T} {g g' : Graph T} {a r : Addr}
    (h : NoAlias g a) (hcb : commBlock o g a = .ok (r, g')) : Step g a g' r := by
  unfold commBlock at hcb
  dsimp only at hcb
  obtain ⟨c, hc, hcb⟩ := bind_ok hcb
  have hc := read_inv hc
  obtain ⟨x, hx, hcb⟩ := bind_ok hcb
  have hx : c.children[0]? = some x := childAt_inv hx
  obtain ⟨_, -, hcb⟩ := bind_ok hcb
  split at hcb
  · obtain ⟨tmp, htmp, hcb⟩ := bind_ok hcb
    obtain ⟨y, hy, hcb⟩ := bind_ok hcb
    obtain ⟨g0, hg0, hcb⟩ := bind_ok hcb
    obtain ⟨g1, hg1, hcb⟩ := bind_ok hcb
    have htmp : c.children[1]? = some tmp := childOf_at hc htmp
    have hy : c.children[0]? = some y := childOf_at hc hy
    have hxy : x = y := by rw [hx] at hy; exact Option.some.inj hy
    obtain ⟨rest, hcl⟩ := two_cons hx htmp
    obtain ⟨hc0, hf0⟩ := setChild_at hc hg0
    obtain ⟨hc1, hf1⟩ := setChild_at hc0 hg1
    have hk1 : kids g1 a = some (tmp :: x :: rest) := by
      rw [kids_some hc1]; simp [hcl, hxy]
    have s1 : Step g a g1 a :=
      rewire_step h hc hk1 (hcl ▸ List.Perm.swap x tmp rest)
        (origins2 (reach_refl g tmp) (reach_refl g x))
        (fun z hz => by simp only [kids, hf1 z hz, hf0 z hz])
        (fun z hz => by rw [hf1 z (ne_of_not_reach hz), hf0 z (ne_of_not_reach hz)])
    exact step_trans s1 (commTail_step (o := o) (op := c.op) s1.1 hcb)
  · obtain ⟨g1, hg1, hcb⟩ := bind_ok hcb
    cases pure_inv hg1
    exact commTail_step (o := o) (op := c.op) h hcb

omit [Mul T] in
/-- Subtraction block (src/Simplify.jl:85-123): every rewrite rewires the two
children of `a` from inside its old child subtrees and updates one leaf. -/
private theorem subBlock_step {g g' : Graph T} {a r : Addr} (h : NoAlias g a)
    (hs : subBlock g a = .ok (r, g')) : Step g a g' r := by
  unfold subBlock at hs
  dsimp only at hs
  obtain ⟨c, hc, hs⟩ := bind_ok hs
  have hc := read_inv hc
  obtain ⟨l, hl, hs⟩ := bind_ok hs
  have hl : c.children[0]? = some l := childAt_inv hl
  have hrl : Reachable g a l := reach_child hc hl
  obtain ⟨_, -, hs⟩ := bind_ok hs
  split at hs
  · obtain ⟨rr, hrr, hs⟩ := bind_ok hs
    have hrr : c.children[1]? = some rr := childAt_inv hrr
    obtain ⟨rest, hcl⟩ := two_cons hl hrr
    obtain ⟨_, -, hs⟩ := bind_ok hs
    split at hs
    · obtain ⟨_, -, hs⟩ := bind_ok hs
      obtain ⟨_, -, hs⟩ := bind_ok hs
      split at hs
      · -- Lines 78-84: children become (rr.2, l); `l` gets the new value.
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨p, hp, hs⟩ := bind_ok hs
        obtain ⟨q, hq, hs⟩ := bind_ok hs
        obtain ⟨g1, hg1, hs⟩ := bind_ok hs
        obtain ⟨g2, hg2, hs⟩ := bind_ok hs
        obtain ⟨w, hw, hs⟩ := bind_ok hs
        obtain ⟨g3, hg3, hs⟩ := bind_ok hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
        have hpr : rr = p := by have := childOf_at hc hp; simpa [hcl] using this
        have hrq : Reachable g rr q := by
          obtain ⟨cp, hcp, hq⟩ := childOf_inv hq
          rw [hpr]; exact reach_child hcp hq
        obtain ⟨hc1, hf1⟩ := setChild_at hc hg1
        obtain ⟨hc2, hf2⟩ := setChild_at hc1 hg2
        have hw : l = w := by have := childOf_at hc2 hw; simpa [hcl] using this
        have hk2 : kids g2 a = some (q :: l :: rest) := by rw [kids_some hc2]; simp [hcl]
        exact finish_step h hc (hcl ▸ List.Perm.swap l rr rest) hrq (reach_refl g l) hk2
          (fun z hz => by rw [hf2 z hz, hf1 z hz]) hg3 (hw ▸ hrl)
      · obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        split at hs
        · -- Lines 86-91: children become (l, rr.1); `l` gets the new value.
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨p, hp, hs⟩ := bind_ok hs
          obtain ⟨q, hq, hs⟩ := bind_ok hs
          obtain ⟨g1, hg1, hs⟩ := bind_ok hs
          obtain ⟨w, hw, hs⟩ := bind_ok hs
          obtain ⟨g3, hg3, hs⟩ := bind_ok hs
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
          have hpr : rr = p := by have := childOf_at hc hp; simpa [hcl] using this
          have hrq : Reachable g rr q := by
            obtain ⟨cp, hcp, hq⟩ := childOf_inv hq
            rw [hpr]; exact reach_child hcp hq
          obtain ⟨hc1, hf1⟩ := setChild_at hc hg1
          have hw : l = w := by have := childOf_at hc1 hw; simpa [hcl] using this
          have hk1 : kids g1 a = some (l :: q :: rest) := by rw [kids_some hc1]; simp [hcl]
          exact finish_step h hc (hcl ▸ List.Perm.refl _) (reach_refl g l) hrq hk1 hf1 hg3
            (hw ▸ hrl)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
          exact step_refl h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
      exact step_refl h
  · obtain ⟨rr, hrr, hs⟩ := bind_ok hs
    have hrr : c.children[1]? = some rr := childAt_inv hrr
    obtain ⟨rest, hcl⟩ := two_cons hl hrr
    have hrrr : Reachable g a rr := reach_child hc hrr
    obtain ⟨_, -, hs⟩ := bind_ok hs
    split at hs
    · obtain ⟨_, -, hs⟩ := bind_ok hs
      obtain ⟨_, -, hs⟩ := bind_ok hs
      split at hs
      · -- Lines 97-103: children become (rr, l.2); `rr` gets the new value.
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨p, hp, hs⟩ := bind_ok hs
        obtain ⟨q, hq, hs⟩ := bind_ok hs
        obtain ⟨g1, hg1, hs⟩ := bind_ok hs
        obtain ⟨g2, hg2, hs⟩ := bind_ok hs
        obtain ⟨w, hw, hs⟩ := bind_ok hs
        obtain ⟨g3, hg3, hs⟩ := bind_ok hs
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
        have hpl : l = p := by have := childOf_at hc hp; simpa [hcl] using this
        have hlq : Reachable g l q := by
          obtain ⟨cp, hcp, hq⟩ := childOf_inv hq
          rw [hpl]; exact reach_child hcp hq
        obtain ⟨hc1, hf1⟩ := setChild_at hc hg1
        obtain ⟨hc2, hf2⟩ := setChild_at hc1 hg2
        have hw : rr = w := by have := childOf_at hc2 hw; simpa [hcl] using this
        have hk2 : kids g2 a = some (rr :: q :: rest) := by rw [kids_some hc2]; simp [hcl]
        exact finish_step h hc (hcl ▸ List.Perm.swap l rr rest) (reach_refl g rr) hlq hk2
          (fun z hz => by rw [hf2 z hz, hf1 z hz]) hg3 (hw ▸ hrrr)
      · obtain ⟨_, -, hs⟩ := bind_ok hs
        obtain ⟨_, -, hs⟩ := bind_ok hs
        split at hs
        · -- Lines 105-110: children become (l.1, rr); `rr` gets the new value.
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨_, -, hs⟩ := bind_ok hs
          obtain ⟨p, hp, hs⟩ := bind_ok hs
          obtain ⟨q, hq, hs⟩ := bind_ok hs
          obtain ⟨g1, hg1, hs⟩ := bind_ok hs
          obtain ⟨w, hw, hs⟩ := bind_ok hs
          obtain ⟨g3, hg3, hs⟩ := bind_ok hs
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
          have hpl : l = p := by have := childOf_at hc hp; simpa [hcl] using this
          have hlq : Reachable g l q := by
            obtain ⟨cp, hcp, hq⟩ := childOf_inv hq
            rw [hpl]; exact reach_child hcp hq
          obtain ⟨hc1, hf1⟩ := setChild_at hc hg1
          have hw : rr = w := by have := childOf_at hc1 hw; simpa [hcl] using this
          have hk1 : kids g1 a = some (q :: rr :: rest) := by rw [kids_some hc1]; simp [hcl]
          exact finish_step h hc (hcl ▸ List.Perm.refl _) hlq (reach_refl g rr) hk1 hf1 hg3
            (hw ▸ hrrr)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
          exact step_refl h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hs)
      exact step_refl h

/-- Line 71 onwards, on the possibly replaced root. -/
private def subStage (o : CEnum T) (g : Graph T) (tree : Addr) (tlc : Bool) :
    Jl (Addr × Graph T) := do
  let c ← g.read tree
  if c.degree = 2 then
    let b ← o.binop c.op
    if b.isSub && tlc then subBlock g tree else pure (tree, g)
  else pure (tree, g)

omit [Mul T] in
private theorem subStage_step {o : CEnum T} {g g' : Graph T} {a r : Addr} {tlc : Bool}
    (h : NoAlias g a) (ht : subStage o g a tlc = .ok (r, g')) : Step g a g' r := by
  unfold subStage at ht
  obtain ⟨_, -, ht⟩ := bind_ok ht
  split at ht
  · obtain ⟨_, -, ht⟩ := bind_ok ht
    split at ht
    · exact subBlock_step h ht
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
      exact step_refl h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv ht)
    exact step_refl h

/-- Lines 44-115 when `tree.degree == 2` and `top_level_constant` is `tlc`. -/
private theorem commStage_step {o : CEnum T} {g g' : Graph T} {a r : Addr} {op : Nat}
    {tlc : Bool} (h : NoAlias g a)
    (ht : (do
      let b ← o.binop op
      if b.isComm && tlc then do
        let p ← commBlock o g a
        subStage o p.2 p.1 tlc
      else do
        let p ← pure (a, g)
        subStage o p.2 p.1 tlc : Jl (Addr × Graph T)) = .ok (r, g')) :
    Step g a g' r := by
  obtain ⟨_, -, ht⟩ := bind_ok ht
  split at ht
  · obtain ⟨⟨t1, g1⟩, h1, ht⟩ := bind_ok ht
    have s1 := commBlock_step h h1
    exact step_trans s1 (subStage_step s1.1 ht)
  · obtain ⟨p, hp, ht⟩ := bind_ok ht
    cases pure_inv hp
    exact subStage_step h ht

private theorem rewrite_step {o : CEnum T} {g g' : Graph T} {a r : Addr} (h : NoAlias g a)
    (hrw : rewrite o g a = .ok (r, g')) : Step g a g' r := by
  unfold rewrite at hrw
  dsimp only at hrw
  obtain ⟨c, -, hrw⟩ := bind_ok hrw
  split at hrw
  · obtain ⟨_, -, hrw⟩ := bind_ok hrw
    obtain ⟨_, -, hrw⟩ := bind_ok hrw
    split at hrw
    · obtain ⟨tlc, -, hrw⟩ := bind_ok hrw
      exact commStage_step (op := c.op) (tlc := tlc) h hrw
    · obtain ⟨_, -, hrw⟩ := bind_ok hrw
      obtain ⟨tlc, -, hrw⟩ := bind_ok hrw
      exact commStage_step (op := c.op) (tlc := tlc) h hrw
  · obtain ⟨tlc, -, hrw⟩ := bind_ok hrw
    obtain ⟨p, hp, hrw⟩ := bind_ok hrw
    cases pure_inv hp
    exact subStage_step (tlc := tlc) h hrw

end Blocks

/-! ## Recursion over the children -/

/-- Degree 1 (src/Simplify.jl:42-44): the combined child replaces child 1. -/
private theorem unary_step {g h1 g2 : Graph T} {a x r1 : Addr} {c : Cell T}
    (h : NoAlias g a) (hc : g.cells a = some c) (hx : c.children[0]? = some x)
    (s1 : Step g x h1 r1) (hg2 : setChild h1 a 1 r1 = .ok g2) : Step g a g2 a := by
  obtain ⟨rest, hcl⟩ := one_cons hx
  have hxm : x ∈ c.children := List.mem_of_getElem? hx
  have hax : ¬ Reachable g x a := noAlias_child_not_reach h hc hxm
  have hca : h1.cells a = some c := by rw [s1.2.2 a hax]; exact hc
  obtain ⟨hc2, hf2⟩ := setChild_at hca hg2
  have eq2 : ∀ z, z ≠ a → ¬ Reachable g x z → g2.cells z = g.cells z := fun z hza hzx => by
    rw [hf2 z hza, s1.2.2 z hzx]
  have hk2 : kids g2 a = some (r1 :: rest) := by rw [kids_some hc2]; simp [hcl]
  refine node_step h hc hk2 (os := x :: rest) (hcl ▸ List.Perm.refl _) ?_ ?_
  · intro i b hb
    match i, hb with
    | 0, hb =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact ⟨x, rfl, sub_of_eq s1.1
        (fun z hz => hf2 z (ne_of_reach (s1.2.1 z hz) hax)) s1.2.1⟩
    | i + 1, hb =>
      have hbi : c.children[i + 1]? = some b := by rw [hcl]; simpa using hb
      have hbm := List.mem_of_getElem? hbi
      have hab := noAlias_child_not_reach h hc hbm
      have dxb : Disjoint g x b := noAlias_kids_disjoint h hc hx hbi (by omega)
      exact ⟨b, by simpa using hb, sub_of_eq (noAlias_child h hc hbm)
        (fun z hz => eq2 z (ne_of_reach hz hab) (fun hxz => dxb z hxz hz)) (fun z hz => hz)⟩
  · intro z hz
    exact eq2 z (ne_of_not_reach hz) (fun hxz => hz (reach_trans (reach_mem hc hxm) hxz))

/-- Degree 2 (src/Simplify.jl:45-49): both combined children are stored back. -/
private theorem binary_step {g h1 g1 h2 g2 : Graph T} {a x y r1 r2 : Addr} {c : Cell T}
    (h : NoAlias g a) (hc : g.cells a = some c) (hx : c.children[0]? = some x)
    (s1 : Step g x h1 r1) (hg1 : setChild h1 a 1 r1 = .ok g1) (hy : childOf g1 a 2 = .ok y)
    (s2 : NoAlias g1 y → Step g1 y h2 r2) (hg2 : setChild h2 a 2 r2 = .ok g2) :
    Step g a g2 a := by
  have hxm : x ∈ c.children := List.mem_of_getElem? hx
  have hax : ¬ Reachable g x a := noAlias_child_not_reach h hc hxm
  have hca : h1.cells a = some c := by rw [s1.2.2 a hax]; exact hc
  obtain ⟨hc1, hf1⟩ := setChild_at hca hg1
  obtain ⟨t, hcl⟩ := one_cons hx
  have hy' : t[0]? = some y := by have := childOf_at hc1 hy; simpa [hcl] using this
  obtain ⟨rest, rfl⟩ := one_cons hy'
  have hyi : c.children[1]? = some y := by rw [hcl]; rfl
  have hym : y ∈ c.children := List.mem_of_getElem? hyi
  have hay : ¬ Reachable g y a := noAlias_child_not_reach h hc hym
  have dxy : Disjoint g x y := noAlias_kids_disjoint h hc hx hyi (by decide)
  have eq1 : ∀ z, z ≠ a → ¬ Reachable g x z → g1.cells z = g.cells z := fun z hza hzx => by
    rw [hf1 z hza, s1.2.2 z hzx]
  have sy : SameKidsOn g g1 y := sameKids_of_eq fun z hz =>
    eq1 z (ne_of_reach hz hay) (fun hxz => dxy z hxz hz)
  have s2 := s2 (noAlias_transfer sy (noAlias_child h hc hym))
  have hay1 : ¬ Reachable g1 y a := fun hr => hay ((reach_transfer sy).mp hr)
  obtain ⟨hc2, hf2⟩ := setChild_at ((s2.2.2 a hay1).trans hc1) hg2
  have eq2 : ∀ z, z ≠ a → ¬ Reachable g x z → ¬ Reachable g y z → g2.cells z = g.cells z :=
    fun z hza hzx hzy => by
      rw [hf2 z hza, s2.2.2 z (fun hr => hzy ((reach_transfer sy).mp hr)), eq1 z hza hzx]
  have hk2 : kids g2 a = some (r1 :: r2 :: rest) := by rw [kids_some hc2]; simp [hcl]
  refine node_step h hc hk2 (os := x :: y :: rest) (hcl ▸ List.Perm.refl _) ?_ ?_
  · intro i b hb
    match i, hb with
    | 0, hb =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      refine ⟨x, rfl, sub_of_eq s1.1 (fun z hz => ?_) s1.2.1⟩
      have hxz := s1.2.1 z hz
      have hza : z ≠ a := ne_of_reach hxz hax
      rw [hf2 z hza, s2.2.2 z (fun hr => dxy z hxz ((reach_transfer sy).mp hr)), hf1 z hza]
    | 1, hb =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      obtain ⟨hn, hr⟩ := sub_of_eq s2.1
        (fun z hz => hf2 z (ne_of_reach (s2.2.1 z hz) hay1)) s2.2.1
      exact ⟨y, rfl, hn, fun z hz => (reach_transfer sy).mp (hr z hz)⟩
    | i + 2, hb =>
      have hbi : c.children[i + 2]? = some b := by rw [hcl]; simpa using hb
      have hbm := List.mem_of_getElem? hbi
      have hab := noAlias_child_not_reach h hc hbm
      have dxb : Disjoint g x b := noAlias_kids_disjoint h hc hx hbi (by omega)
      have dyb : Disjoint g y b := noAlias_kids_disjoint h hc hyi hbi (by omega)
      exact ⟨b, by simpa using hb, sub_of_eq (noAlias_child h hc hbm)
        (fun z hz => eq2 z (ne_of_reach hz hab) (fun hxz => dxb z hxz hz)
          (fun hyz => dyb z hyz hz)) (fun z hz => hz)⟩
  · intro z hz
    exact eq2 z (ne_of_not_reach hz) (fun hxz => hz (reach_trans (reach_mem hc hxm) hxz))
      (fun hyz => hz (reach_trans (reach_mem hc hym) hyz))

private theorem combineOps_step [Add T] [Mul T] [Sub T] (o : CEnum T) (fuel : Nat) :
    ∀ {g g' : Graph T} {a r : Addr}, NoAlias g a → combineOps o fuel g a = .ok (r, g') →
      Step g a g' r := by
  induction fuel with
  | zero =>
    intro g g' a r _ hco
    simp only [combineOps] at hco
    cases hco
  | succ fuel ih =>
    intro g g' a r h hco
    simp only [combineOps] at hco
    obtain ⟨c, hc, hco⟩ := bind_ok hco
    have hc := read_inv hc
    split at hco
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pure_inv hco)
      exact step_refl h
    · split at hco
      · obtain ⟨x, hx, hco⟩ := bind_ok hco
        have hx : c.children[0]? = some x := childAt_inv hx
        obtain ⟨⟨r1, h1⟩, hrec, hco⟩ := bind_ok hco
        obtain ⟨g2, hg2, hco⟩ := bind_ok hco
        have s := unary_step h hc hx (ih (noAlias_child h hc (List.mem_of_getElem? hx)) hrec) hg2
        exact step_trans s (rewrite_step s.1 hco)
      · split at hco
        · obtain ⟨x, hx, hco⟩ := bind_ok hco
          have hx : c.children[0]? = some x := childAt_inv hx
          obtain ⟨⟨r1, h1⟩, hrec1, hco⟩ := bind_ok hco
          obtain ⟨g1, hg1, hco⟩ := bind_ok hco
          obtain ⟨y, hy, hco⟩ := bind_ok hco
          obtain ⟨⟨r2, h2⟩, hrec2, hco⟩ := bind_ok hco
          obtain ⟨g2, hg2, hco⟩ := bind_ok hco
          have s := binary_step h hc hx
            (ih (noAlias_child h hc (List.mem_of_getElem? hx)) hrec1) hg1 hy
            (fun hy' => ih hy' hrec2) hg2
          exact step_trans s (rewrite_step s.1 hco)
        · obtain ⟨g2, hg2, hco⟩ := bind_ok hco
          cases pure_inv hg2
          exact rewrite_step h hco

/-! ## The property -/

/-- `combine_operators!(tree, operators)` (`src/Simplify.jl:32-126`) on an
alias-free input that unfolds to a well-formed binary tree succeeds (success
from the Simplify slice's `combine_matches_spec`), and returns an alias-free
root that uses only objects of the input tree; nothing outside the input tree
changes. -/
def combine_operators_noalias : Prop :=
  ∀ (T : Type) [Add T] [Mul T] [Sub T] (o : Simplify.CEnum T) (nf fuel : Nat) (g : Graph T)
    (tree : Addr) (t : Tree T),
    g.unfold fuel tree = some t → t.WF 2 o.nops nf → Graph.NoAlias g tree →
    ∃ r g', Simplify.combineOps o fuel g tree = .ok (r, g') ∧
      Graph.NoAlias g' r ∧ (∀ x, Graph.Reachable g' r x → Graph.Reachable g tree x) ∧
      (∀ x, ¬ Graph.Reachable g tree x → g'.cells x = g.cells x)

theorem combine_operators_noalias_holds : combine_operators_noalias := by
  intro T _ _ _ o nf fuel g tree t hu hw h
  obtain ⟨r, g', hco, _⟩ := Simplify.combine_matches_spec_proof T o nf fuel g tree t hu hw h
  exact ⟨r, g', hco, combineOps_step o fuel h hco⟩

/-- The hypotheses are satisfiable: a constant leaf unfolds to a well-formed
tree and is alias-free. -/
example : Graph.unfold (Heap.empty.alloc (⟨0, true, some 3, 0, 0, []⟩ : Cell Nat)).2 1 0 =
      some (Tree.const 3) ∧ (Tree.const (3 : Nat)).WF 2 (⟨[], []⟩ : Simplify.CEnum Nat).nops 0 ∧
    Graph.NoAlias (Heap.empty.alloc (⟨0, true, some 3, 0, 0, []⟩ : Cell Nat)).2 0 :=
  ⟨rfl, by simp [Tree.WF], noAlias_leaf (fun _ hc => by cases hc; rfl)⟩

end DynExpr.NoAlias
