import DynExpr.Simplify.Aliasing
import DynExpr.Simplify.EnumProofs

namespace DynExpr.Simplify

open DynExpr

private theorem mapM_defined {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hx, ht] at h
      | some zs =>
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨y, hx⟩
        · exact ih zs ht a ha

private theorem unfold_path_bound {T : Type} (g : Graph T) (fuel : Nat) (root : Addr)
    (t : Tree T) (hu : g.unfold fuel root = some t) :
    ∀ p a, Graph.Path g root p a → a < g.next := by
  induction fuel generalizing root t with
  | zero => simp [Graph.unfold] at hu
  | succ fuel ih =>
    cases hc : g.cells root with
    | none => simp [Graph.unfold, hc] at hu
    | some c =>
      have hr : root < g.next := by
        by_cases h : root < g.next
        · exact h
        · have hn : g.next ≤ root := Nat.le_of_not_gt h
          have hf := g.fresh root hn
          simp [hc] at hf
      by_cases hl : c.children.length ≠ c.degree
      · simp [Graph.unfold, hc, hl] at hu
      · by_cases hz : c.degree = 0
        · have hn : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
          intro p a hp
          cases hp with
          | nil => exact hr
          | cons hcell hi hp =>
            rw [hc] at hcell
            cases hcell
            simp [hn] at hi
        · cases hm : c.children.mapM (g.unfold fuel) with
          | none => simp [Graph.unfold, hc, hz, hm] at hu
          | some ts =>
            intro p a hp
            cases hp with
            | nil => exact hr
            | @cons _ b _ i p _ hcell hi hp =>
              rw [hc] at hcell
              cases hcell
              have hb : b ∈ c.children := List.mem_of_getElem? hi
              obtain ⟨u, hu⟩ := mapM_defined _ _ _ hm b hb
              exact ih b u hu p a hp

private theorem path_transfer {T : Type} {g h : Graph T}
    (heq : ∀ a, a < g.next → h.cells a = g.cells a)
    {root : Addr} (hb : ∀ p a, Graph.Path g root p a → a < g.next)
    {p : List Nat} {a : Addr} (hp : Graph.Path h root p a) : Graph.Path g root p a := by
  induction p generalizing root a with
  | nil => cases hp; exact Graph.Path.nil _
  | cons i p ih =>
    cases hp with
    | @cons _ b _ _ _ c hc hi hp =>
      have hr := hb [] root (Graph.Path.nil _)
      rw [heq root hr] at hc
      have hbb : ∀ q z, Graph.Path g b q z → z < g.next := by
        intro q z hq
        exact hb (i :: q) z (Graph.Path.cons hc hi hq)
      exact Graph.Path.cons hc hi (ih hbb hp)

private theorem alloc_preserves {T : Type} (g : Graph T) (c : Cell T) :
    ∀ a, a < g.next → (g.alloc c).2.cells a = g.cells a := by
  intro a ha
  simp [Heap.alloc, show a ≠ g.next by omega]

private theorem alloc_noAlias {T : Type} (g : Graph T) (c : Cell T)
    (hb : ∀ (i : Nat) (b : Addr), c.children[i]? = some b →
      ∀ p a, Graph.Path g b p a → a < g.next)
    (hq : ∀ (i j : Nat) (b d : Addr) (p q : List Nat) (a : Addr),
      c.children[i]? = some b → c.children[j]? = some d →
      Graph.Path g b p a → Graph.Path g d q a → i = j ∧ p = q) :
    Graph.NoAlias (g.alloc c).2 (g.alloc c).1 := by
  intro p q a hp hq'
  have hc : (g.alloc c).2.cells (g.alloc c).1 = some c := by simp [Heap.alloc]
  cases hp with
  | nil =>
    cases hq' with
    | nil => rfl
    | @cons _ b _ i q _ hcell hi hp =>
      rw [hc] at hcell
      cases hcell
      have hp' := path_transfer (alloc_preserves g c) (hb i b hi) hp
      have := hb i b hi q (g.alloc c).1 hp'
      simp [Heap.alloc] at this
  | @cons _ b _ i p _ hcell hi hp =>
    rw [hc] at hcell
    cases hcell
    have hp' := path_transfer (alloc_preserves g c) (hb i b hi) hp
    cases hq' with
    | nil =>
      have := hb i b hi p (g.alloc c).1 hp'
      simp [Heap.alloc] at this
    | @cons _ d _ j q _ hcell hj hpath =>
      rw [hc] at hcell
      cases hcell
      have hd' := path_transfer (alloc_preserves g c) (hb j d hj) hpath
      obtain ⟨rfl, rfl⟩ := hq i j b d p q a hi hj hp' hd'
      rfl

private theorem leaf_noAlias {T : Type} (g : Graph T) (v : T) :
    Graph.NoAlias (g.alloc (constCellOf v)).2 (g.alloc (constCellOf v)).1 := by
  apply alloc_noAlias
  · intro i b hi
    simp [constCellOf] at hi
  · intro i j b d p q a hi
    simp [constCellOf] at hi

private theorem get_one {l b : Addr} {i : Nat} (h : [l][i]? = some b) :
    i = 0 ∧ b = l := by
  cases i with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ i => simp at h

private theorem get_two {l r b : Addr} {i : Nat} (h : [l, r][i]? = some b) :
    (i = 0 ∧ b = l) ∨ (i = 1 ∧ b = r) := by
  cases i with
  | zero => simp at h; exact Or.inl ⟨rfl, h.symm⟩
  | succ i =>
    cases i with
    | zero => simp at h; exact Or.inr ⟨rfl, h.symm⟩
    | succ i => simp at h

private theorem unary_noAlias {T : Type} (g : Graph T) (op l : Nat)
    (hb : ∀ p a, Graph.Path g l p a → a < g.next) (hn : Graph.NoAlias g l) :
    Graph.NoAlias (g.alloc (branchCellOf op [l])).2 (g.alloc (branchCellOf op [l])).1 := by
  apply alloc_noAlias
  · intro i b hi
    obtain ⟨rfl, rfl⟩ := get_one hi
    exact hb
  · intro i j b d p q a hi hj hp hq
    obtain ⟨rfl, rfl⟩ := get_one hi
    obtain ⟨rfl, rfl⟩ := get_one hj
    exact ⟨rfl, hn p q a hp hq⟩

private theorem binary_noAlias {T : Type} (g : Graph T) (op l r : Nat)
    (hl : ∀ p a, Graph.Path g l p a → a < g.next)
    (hr : ∀ p a, Graph.Path g r p a → a < g.next)
    (nl : Graph.NoAlias g l) (nr : Graph.NoAlias g r)
    (hd : ∀ a, Graph.Reachable g l a → ¬ Graph.Reachable g r a) :
    Graph.NoAlias (g.alloc (branchCellOf op [l, r])).2
      (g.alloc (branchCellOf op [l, r])).1 := by
  apply alloc_noAlias
  · intro i b hi
    rcases get_two hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl
    · exact hr
  · intro i j b d p q a hi hj hp hq
    rcases get_two hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases get_two hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, nl p q a hp hq⟩
      · exact False.elim (hd a ⟨p, hp⟩ ⟨q, hq⟩)
    · rcases get_two hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim (hd a ⟨q, hq⟩ ⟨p, hp⟩)
      · exact ⟨rfl, nr p q a hp hq⟩

private theorem scalar_noAlias {T : Type} (g : Graph T) (op l : Nat) (v : T)
    (hb : ∀ p a, Graph.Path g l p a → a < g.next) (hn : Graph.NoAlias g l) :
    Graph.NoAlias ((g.alloc (constCellOf v)).2.alloc
      (branchCellOf op [l, (g.alloc (constCellOf v)).1])).2
      ((g.alloc (constCellOf v)).2.alloc
      (branchCellOf op [l, (g.alloc (constCellOf v)).1])).1 := by
  let h : Graph T := (g.alloc (constCellOf v)).2
  let r := (g.alloc (constCellOf v)).1
  have he := alloc_preserves g (constCellOf v)
  have hu : h.unfold 1 r = some (.const v) := by
    simp [h, r, Graph.unfold, Heap.alloc, constCellOf]
  have hr := unfold_path_bound h 1 r (.const v) hu
  have hl : ∀ p a, Graph.Path h l p a → a < h.next := by
    intro p a hp
    have ha := hb p a (path_transfer he hb hp)
    change a < g.next + 1
    exact Nat.lt_succ_of_lt ha
  have nl : Graph.NoAlias h l := by
    intro p q a hp hq
    exact hn p q a (path_transfer he hb hp) (path_transfer he hb hq)
  apply binary_noAlias h op l r hl hr nl (leaf_noAlias g v)
  intro a ⟨p, hp⟩ ⟨q, hq⟩
  have ha := hb p a (path_transfer he hb hp)
  have heq : a = r := by
    have hc : h.cells r = some (constCellOf v) := by simp [h, r, Heap.alloc]
    cases hq with
    | nil => rfl
    | cons hcell hi hp =>
      rw [hc] at hcell
      cases hcell
      simp [constCellOf] at hi
  simp [r, Heap.alloc, heq] at ha

private theorem unfold_cell_info {T : Type} (g : Graph T) (fuel : Nat) (root : Addr)
    (t : Tree T) (hu : g.unfold fuel root = some t) :
    ∃ c, g.read root = .ok c ∧
      (cellConst c = true → ∃ v, valOf g root = .ok v) := by
  cases fuel with
  | zero => simp [Graph.unfold] at hu
  | succ fuel =>
    cases hc : g.cells root with
    | none => simp [Graph.unfold, hc] at hu
    | some c =>
      refine ⟨c, by simp [Heap.read, hc], ?_⟩
      intro hn
      have hs : c.degree = 0 ∧ c.constant = true := by simpa [cellConst] using hn
      cases hv : c.val with
      | none => simp [Graph.unfold, hc, hs.1, hs.2, hv] at hu
      | some v =>
        exact ⟨v, by simp [valOf, Heap.read, hc, hv, bind, Except.bind, pure, Except.pure]⟩

theorem overload_heap_noalias_proof : overload_heap_noalias := by
  intro T I st f g l r fuel tl tr hul hur hnl hnr hd
  have hl := unfold_path_bound g fuel l tl hul
  have hr := unfold_path_bound g fuel r tr hur
  obtain ⟨cl, hreadl, hvall⟩ := unfold_cell_info g fuel l tl hul
  obtain ⟨cr, hreadr, hvalr⟩ := unfold_cell_info g fuel r tr hur
  have leaf : ∀ v : T, Graph.NoAlias (g.alloc (constCellOf v)).2
      (g.alloc (constCellOf v)).1 ∧
      ∀ a, a < g.next → (g.alloc (constCellOf v)).2.cells a = g.cells a :=
    fun v => ⟨leaf_noAlias g v, alloc_preserves g _⟩
  constructor
  · intro hdef ⟨idx, hmap⟩
    have hlookup : lookupOp st f 1 false = .ok idx := by simp [lookupOp, hmap, pure, Except.pure]
    cases hconst : cellConst cl with
    | false =>
      refine ⟨(g.alloc (branchCellOf idx [l])).1, (g.alloc (branchCellOf idx [l])).2,
        ?_, unary_noAlias g idx l hl hnl, alloc_preserves g _⟩
      simp [callUnaryHeap, hdef, hreadl, hconst, hlookup, bind, Except.bind, pure, Except.pure]
    | true =>
      obtain ⟨v, hv⟩ := hvall hconst
      refine ⟨(g.alloc (constCellOf (I f [v]))).1,
        (g.alloc (constCellOf (I f [v]))).2, ?_, leaf _⟩
      simp [callUnaryHeap, hdef, hreadl, hconst, hv, bind, Except.bind, pure, Except.pure]
  · intro hdef ⟨idx, hmap⟩
    have hlookup : lookupOp st f 2 false = .ok idx := by simp [lookupOp, hmap, pure, Except.pure]
    constructor
    · by_cases hconst : cellConst cl = true ∧ cellConst cr = true
      · have hs := hconst
        obtain ⟨a, hva⟩ := hvall hs.1
        obtain ⟨b, hvb⟩ := hvalr hs.2
        refine ⟨(g.alloc (constCellOf (I f [a, b]))).1,
          (g.alloc (constCellOf (I f [a, b]))).2, ?_, leaf _⟩
        simp [callBinaryHeap, hdef, hreadl, hreadr, hs.1, hs.2, hva, hvb,
          bind, Except.bind, pure, Except.pure]
      · refine ⟨(g.alloc (branchCellOf idx [l, r])).1,
          (g.alloc (branchCellOf idx [l, r])).2, ?_,
          binary_noAlias g idx l r hl hr hnl hnr hd, alloc_preserves g _⟩
        simp [callBinaryHeap, hdef, hreadl, hreadr, hconst, hlookup,
          bind, Except.bind, pure, Except.pure]
    · intro b
      cases hconst : cellConst cl with
      | false =>
        let h : Graph T := (g.alloc (constCellOf b)).2
        let c := (g.alloc (constCellOf b)).1
        refine ⟨(h.alloc (branchCellOf idx [l, c])).1,
          (h.alloc (branchCellOf idx [l, c])).2, ?_, scalar_noAlias g idx l b hl hnl, ?_⟩
        · simp [callBinaryNSHeap, hdef, hreadl, hconst, hlookup, h, c,
            bind, Except.bind, pure, Except.pure]
        · intro a ha
          have ha' : a < h.next := Nat.lt_succ_of_lt ha
          exact (alloc_preserves h (branchCellOf idx [l, c]) a ha').trans
            (alloc_preserves g (constCellOf b) a ha)
      | true =>
        obtain ⟨a, hva⟩ := hvall hconst
        refine ⟨(g.alloc (constCellOf (I f [a, b]))).1,
          (g.alloc (constCellOf (I f [a, b]))).2, ?_, leaf _⟩
        simp [callBinaryNSHeap, hdef, hreadl, hconst, hva, bind, Except.bind, pure, Except.pure]

theorem enum_vector_pairs_copy_proof : enum_vector_pairs_copy := by
  intro inBase kind vh p ps helpers emptyOld st tup tups hp hps hinput hn
  obtain ⟨ops, st', hmake, hslot⟩ := makeEnum_ok_layout inBase kind (p.1, tup) tups helpers emptyOld st hinput hn
  refine ⟨ops, st', ?_, hslot⟩
  unfold makeEnumVec
  rw [hp, hps]
  exact hmake

private theorem leaf_path {T : Type} {g : Graph T} {root : Addr} {c : Cell T}
    (hc : g.cells root = some c) (hn : c.children = [])
    {p : List Nat} {a : Addr} (hp : Graph.Path g root p a) : p = [] ∧ a = root := by
  cases hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons hcell hi hp =>
    rw [hc] at hcell
    cases hcell
    simp [hn] at hi

example : ∃ (g : Graph Nat) (st : Globals),
    g.unfold 1 0 = some (.const 1) ∧ g.unfold 1 1 = some (.const 2) ∧
    Graph.NoAlias g 0 ∧ Graph.NoAlias g 1 ∧
    (∀ a, Graph.Reachable g 0 a → ¬ Graph.Reachable g 1 a) ∧
    st.defined 1 (.plain 0) = true ∧ (∃ i, st.mapping 1 (.plain 0) = some i) ∧
    st.defined 2 (.plain 0) = true ∧ (∃ i, st.mapping 2 (.plain 0) = some i) := by
  let g : Graph Nat := (((Heap.empty : Graph Nat).alloc (constCellOf 1)).2.alloc
    (constCellOf 2)).2
  have hc0 : g.cells 0 = some (constCellOf 1) := rfl
  have hc1 : g.cells 1 = some (constCellOf 2) := rfl
  let st : Globals := ⟨none, fun _ _ => some 1, fun _ _ => true, 0⟩
  refine ⟨g, st, ?_, ?_, ?_, ?_, ?_, rfl, ⟨1, rfl⟩, rfl, ⟨1, rfl⟩⟩
  · simp [Graph.unfold, hc0, constCellOf]
  · simp [Graph.unfold, hc1, constCellOf]
  · intro p q a hp hq
    exact (leaf_path hc0 rfl hp).1.trans (leaf_path hc0 rfl hq).1.symm
  · intro p q a hp hq
    exact (leaf_path hc1 rfl hp).1.trans (leaf_path hc1 rfl hq).1.symm
  · intro a ⟨p, hp⟩ ⟨q, hq⟩
    have h : (0 : Nat) = 1 := (leaf_path hc0 rfl hp).2.symm.trans
      (leaf_path hc1 rfl hq).2
    cases h

example : ∃ (vh : Heap (List Fn)) (p : Int × Addr) (ps : List (Int × Addr))
    (tup : List Fn) (tups : List (Int × List Fn)),
    vh.read p.2 = .ok tup ∧
      ps.mapM (fun q => do pure (q.1, ← vh.read q.2)) = .ok tups ∧
      EnumInput (p.1, tup) tups ∧ (((p.1, tup) :: tups).map Prod.fst).Nodup := by
  let vh := ((Heap.empty : Heap (List Fn)).alloc [Fn.plain 1]).2
  refine ⟨vh, (1, 0), [], [Fn.plain 1], [], ?_, ?_, ?_, by decide⟩
  · exact Heap.read_alloc_same _ _
  · rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro q hq; simp at hq; subst q; decide
    · intro q hq; simp at hq; subst q; decide
    · intro q hq n hf; simp at hq; subst q; simp at hf

end DynExpr.Simplify
