import DynExpr.NoAlias.Ctor
import DynExpr.NodeUtils.Nodes
import DynExpr.Simplify.SimplifyTree
import DynExpr.Simplify.SimplifyProofs

/-!
Mutating operations on plain `Node` trees keep them alias-free:
`set_child!`, `set_children!`, `set_node!` (`src/Node.jl:224-256,490-512`,
NodeBase mirrors), `set_scalar_constants!` (`src/NodeUtils.jl:126-130`,
NodeUtils mirror) and `simplify_tree!` (`src/Simplify.jl:131-149`, Simplify
mirror).
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

/-! ## Replacing the children of one object -/

/-- Replacing the children of `t` by a list `K` keeps an enclosing tree `r`
alias-free when the new children are distinct, alias-free, pairwise disjoint,
do not reach `t`, and meet `r` only inside the old subtree of `t`. -/
theorem noAlias_set_kids {g G : Graph T} {r t : Addr} {K : List Addr}
    (hoff : ∀ x, x ≠ t → kids G x = kids g x) (hr : NoAlias g r)
    (hK : kids G t = some K) (hnd : K.Nodup)
    (hna : ∀ b ∈ K, NoAlias g b) (hcyc : ∀ b ∈ K, ¬ Reachable g b t)
    (hsub : ∀ b ∈ K, ∀ x, Reachable g b x → Reachable g r x → Reachable g t x)
    (hdis : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → Disjoint g b b') : NoAlias G r := by
  have hsame : ∀ b ∈ K, SameKidsOn g G b := fun b hb => sameKidsOn_of_frame hoff (hcyc b hb)
  obtain ⟨c, hc, hch⟩ := cell_of_kids hK
  have ht : NoAlias G t := by
    refine noAlias_node hc (by rw [hch]; exact hnd) ?_ ?_ ?_
    · intro b hb; rw [hch] at hb; exact noAlias_transfer (hsame b hb) (hna b hb)
    · intro b hb h; rw [hch] at hb; exact hcyc b hb ((reach_transfer (hsame b hb)).mp h)
    · intro b hb b' hb' hne; rw [hch] at hb hb'
      exact disjoint_transfer (hsame b hb) (hsame b' hb') (hdis b hb b' hb' hne)
  refine noAlias_graft hoff hr ht ?_
  intro x hx hrx
  rcases reach_inv hx with rfl | ⟨c', b, hc', hb, hbx⟩
  · exact reach_refl g _
  · rw [hc] at hc'; cases hc'
    rw [hch] at hb
    exact hsub b hb x ((reach_transfer (hsame b hb)).mp hbx) hrx

/-- The children of an object inside an alias-free tree satisfy the
conditions of `noAlias_set_kids` for that object. -/
theorem old_kid_facts {g : Graph T} {r t b : Addr} {c : Cell T} (hr : NoAlias g r)
    (hrt : Reachable g r t) (hc : g.cells t = some c) (hb : b ∈ c.children) :
    NoAlias g b ∧ ¬ Reachable g b t ∧ Reachable g t b := by
  have ht := noAlias_reach hr hrt
  exact ⟨noAlias_child ht hc hb, noAlias_child_not_reach ht hc hb, reach_mem hc hb⟩

/-! ## List facts about children tuples -/

theorem slotsOf_eq (D : Nat) (l : List (Option Addr)) :
    slotsOf D l = l.take D ++ List.replicate (D - l.length) none := by
  induction D with
  | zero => simp [slotsOf]
  | succ n ih =>
    have hs : slotsOf (n + 1) l = slotsOf n l ++ [(l[n]?).getD none] := by
      simp [slotsOf, List.range_succ]
    rw [hs, ih, List.take_add_one]
    by_cases hn : n < l.length
    · rw [List.getElem?_eq_getElem hn]
      have h1 : n - l.length = 0 := by omega
      have h2 : n + 1 - l.length = 0 := by omega
      simp [h1, h2]
    · rw [List.getElem?_eq_none (by omega)]
      have h2 : n + 1 - l.length = (n - l.length) + 1 := by omega
      rw [h2, List.replicate_succ']
      simp

private theorem filterMap_replicate_none (k : Nat) :
    (List.replicate k (none : Option Addr)).filterMap id = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- The active children after storing the tuple `slotsOf D l` with degree `d`
are a sublist of the first `d` entries of `l` (`src/Node.jl:238-253`). -/
theorem active_slots_sublist (D d : Nat) (l : List (Option Addr)) :
    List.Sublist (((slotsOf D l).take d).filterMap id) ((l.take d).filterMap id) := by
  rw [slotsOf_eq, List.take_append, List.filterMap_append, List.take_replicate,
    filterMap_replicate_none, List.append_nil, List.take_take]
  apply List.Sublist.filterMap
  rw [show l.take (min d D) = (l.take d).take (min d D) by rw [List.take_take]; congr 1; omega]
  exact List.take_sublist _ _

private theorem filterMap_set_mem :
    ∀ (l : List (Option Addr)) (k : Nat) (y z : Addr),
      z ∈ (l.set k (some y)).filterMap id → z = y ∨ z ∈ l.filterMap id := by
  intro l
  induction l with
  | nil => intro k y z h; simp at h
  | cons a l ih =>
    intro k y z h
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.filterMap_cons, id] at h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right; cases a <;> simp [h]
    | succ k =>
      simp only [List.set_cons_succ] at h
      cases a with
      | none =>
        simp only [List.filterMap_cons, id] at h
        rcases ih k y z h with h | h
        · exact Or.inl h
        · right; simpa using h
      | some a =>
        simp only [List.filterMap_cons, id, List.mem_cons] at h
        rcases h with rfl | h
        · right; simp
        · rcases ih k y z h with h | h
          · exact Or.inl h
          · right; simp [h]

private theorem filterMap_set_nodup :
    ∀ (l : List (Option Addr)) (k : Nat) (y : Addr),
      (l.filterMap id).Nodup → y ∉ l.filterMap id → ((l.set k (some y)).filterMap id).Nodup := by
  intro l
  induction l with
  | nil => intro k y _ _; simp
  | cons a l ih =>
    intro k y hnd hy
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.filterMap_cons, id]
      cases a with
      | none =>
        simp only [List.filterMap_cons, id] at hnd hy
        exact List.nodup_cons.mpr ⟨hy, hnd⟩
      | some a =>
        simp only [List.filterMap_cons, id, List.mem_cons, not_or] at hnd hy
        exact List.nodup_cons.mpr ⟨hy.2, (List.nodup_cons.mp hnd).2⟩
    | succ k =>
      simp only [List.set_cons_succ]
      cases a with
      | none =>
        simp only [List.filterMap_cons, id] at hnd hy ⊢
        exact ih k y hnd hy
      | some a =>
        simp only [List.filterMap_cons, id, List.mem_cons, not_or] at hnd hy ⊢
        obtain ⟨ha, hnd⟩ := List.nodup_cons.mp hnd
        refine List.nodup_cons.mpr ⟨?_, ih k y hnd hy.2⟩
        intro hm
        rcases filterMap_set_mem l k y a hm with h | h
        · exact hy.1 h.symm
        · exact ha h

theorem take_set_comm (l : List (Option Addr)) (d k : Nat) (x : Option Addr) :
    (l.set k x).take d = (l.take d).set k x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_set]

/-! ## SGraph mutators -/

theorem read_ok {g : SGraph T} {a : Addr} {c : SCell T} (h : g.read a = .ok c) :
    g.cells a = some c := by
  unfold Heap.read at h
  split at h
  · cases h
  · rename_i v hv; cases h; exact hv

theorem view_kids_off {g g' : SGraph T} {n : Addr} (h : ∀ x, x ≠ n → g'.cells x = g.cells x) :
    ∀ x, x ≠ n → kids g'.view x = kids g.view x := by
  intro x hx; rw [view_kids, view_kids, h x hx]

/-- `set_child!(n, child, i)` (`src/Node.jl:224-227`) keeps every enclosing
alias-free tree `r` alias-free when `child` is an alias-free tree sharing no
object with `r`. -/
def set_child_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D r n child i res : Nat),
    NoAlias g.view r → Reachable g.view r n → NoAlias g.view child → Disjoint g.view r child →
    setChild g D n child i = .ok (res, g') → NoAlias g'.view r

theorem set_child_noalias_ok_holds : set_child_noalias_ok := by
  intro T g g' D r n child i res hr hrn hchild hdis h
  unfold setChild at h
  cases hc : g.cells n with
  | none => simp [Heap.read, hc, bind, Except.bind] at h
  | some c =>
    simp only [Heap.read, hc, bind, Except.bind] at h
    cases hs : c.slots with
    | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
    | some s =>
      simp only [hs] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · cases h
        · rename_i g1 hset
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          obtain ⟨c0, hc0, hc1, hoff, _⟩ := setChildrenRaw_ok hset
          rw [hc] at hc0; cases hc0
          let K := ((slotsOf D (s.set (i - 1) (some child))).take c.degree).filterMap id
          have hK : kids g1.view n = some K := by rw [view_kids, hc1]; rfl
          have hold : c.active = (s.take c.degree).filterMap id := by simp [SCell.active, hs]
          have hcv : g.view.cells n = some c.toCell := by rw [view_cells, hc]; rfl
          have hsub : List.Sublist K (((s.take c.degree).set (i - 1) (some child)).filterMap id) := by
            have := active_slots_sublist D c.degree (s.set (i - 1) (some child))
            rwa [take_set_comm] at this
          have hchild_notin : child ∉ c.active := by
            intro hm
            have hrc : Reachable g.view r child := reach_trans hrn (reach_mem hcv hm)
            exact hdis child hrc (reach_refl _ _)
          have hold_nd : c.active.Nodup := noAlias_kids_nodup (noAlias_reach hr hrn) hcv
          have hmem : ∀ b ∈ K, b = child ∨ b ∈ c.active := by
            intro b hb
            rw [hold]
            exact filterMap_set_mem _ _ _ _ (hsub.subset hb)
          have hnd : K.Nodup := by
            refine hsub.nodup (filterMap_set_nodup _ _ _ ?_ ?_)
            · rw [← hold]; exact hold_nd
            · rw [← hold]; exact hchild_notin
          have hnot_r : ∀ x, Reachable g.view child x → ¬ Reachable g.view r x :=
            fun x h1 h2 => hdis x h2 h1
          refine noAlias_set_kids (view_kids_off hoff) hr hK hnd ?_ ?_ ?_ ?_
          · intro b hb
            rcases hmem b hb with rfl | hb
            · exact hchild
            · exact (old_kid_facts hr hrn hcv hb).1
          · intro b hb
            rcases hmem b hb with rfl | hb
            · intro h; exact hnot_r n (reach_trans h (reach_refl _ _)) hrn
            · exact (old_kid_facts hr hrn hcv hb).2.1
          · intro b hb x hbx hrx
            rcases hmem b hb with rfl | hb
            · exact absurd hrx (hnot_r x hbx)
            · exact reach_trans (old_kid_facts hr hrn hcv hb).2.2 hbx
          · intro b hb b' hb' hne
            rcases hmem b hb with rfl | hb1 <;> rcases hmem b' hb' with rfl | hb1'
            · exact absurd rfl hne
            · intro z h1 h2
              exact hnot_r z h1 (reach_trans hrn (reach_trans (reach_mem hcv hb1') h2))
            · intro z h1 h2
              exact hnot_r z h2 (reach_trans hrn (reach_trans (reach_mem hcv hb1) h1))
            · exact noAlias_mem_disjoint (noAlias_reach hr hrn) hcv hb1 hb1' hne

/-- `set_children!(n, cs)` (`src/Node.jl:235-256`) keeps every enclosing
alias-free tree `r` alias-free when the new children are distinct, alias-free,
pairwise disjoint trees sharing no object with `r`. -/
def set_children_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D r n : Nat) (cs : List Addr),
    NoAlias g.view r → Reachable g.view r n → (∀ b ∈ cs, NoAlias g.view b) →
    PairDisj g.view cs → (∀ b ∈ cs, Disjoint g.view r b) →
    setChildren g D n cs = .ok g' → NoAlias g'.view r

theorem set_children_noalias_ok_holds : set_children_noalias_ok := by
  intro T g g' D r n cs hr hrn hna hpd hdis h
  obtain ⟨c, hc, hc1, hoff, _⟩ := setChildrenRaw_ok h
  let K := ((slotsOf D (cs.map some)).take c.degree).filterMap id
  have hK : kids g'.view n = some K := by rw [view_kids, hc1]; rfl
  have hsub : List.Sublist K cs := by
    have h1 := active_slots_sublist D c.degree (cs.map some)
    have h2 : ((cs.map some).take c.degree).filterMap id = cs.take c.degree := by
      rw [← List.map_take, List.filterMap_map]; exact List.filterMap_some
    rw [h2] at h1
    exact h1.trans (List.take_sublist _ _)
  have hnot_r : ∀ b ∈ cs, ∀ x, Reachable g.view b x → ¬ Reachable g.view r x :=
    fun b hb x h1 h2 => hdis b hb x h2 h1
  refine noAlias_set_kids (view_kids_off hoff) hr hK (hsub.nodup hpd.1) ?_ ?_ ?_ ?_
  · intro b hb; exact hna b (hsub.subset hb)
  · intro b hb h; exact hnot_r b (hsub.subset hb) n h hrn
  · intro b hb x hbx hrx; exact absurd hrx (hnot_r b (hsub.subset hb) x hbx)
  · intro b hb b' hb' hne; exact hpd.2 b (hsub.subset hb) b' (hsub.subset hb') hne

/-- `set_node!(t, s)` (`src/Node.jl:490-512`) keeps every enclosing alias-free
tree `r` alias-free when `s` is alias-free, does not reach `t`, and meets `r`
only inside the subtree of `t` (for example: `s` is a disjoint tree, or `s` is
a descendant of `t`). -/
def set_node_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D r t s : Nat),
    NoAlias g.view r → NoAlias g.view s → ¬ Reachable g.view s t →
    (∀ x, Reachable g.view s x → Reachable g.view r x → Reachable g.view t x) →
    setNode g D t s = .ok g' → NoAlias g'.view r

/-- Final heap shape of a successful `set_node!`: only `t` changes, and its
new active children are a sublist of the source's active children. -/
theorem setNode_ok {g g' : SGraph T} {D t s : Nat} (h : setNode g D t s = .ok g') :
    ∃ sc K, g.cells s = some sc ∧ kids g'.view t = some K ∧ List.Sublist K sc.active ∧
      (∀ x, x ≠ t → g'.cells x = g.cells x) := by
  unfold setNode at h
  cases hs : g.cells s with
  | none => simp [Heap.read, hs, bind, Except.bind] at h
  | some sc =>
    cases ht : g.cells t with
    | none => simp [Heap.read, hs, ht, bind, Except.bind] at h
    | some tc =>
      simp only [Heap.read, hs, ht, bind, Except.bind] at h
      split at h
      · rename_i hd
        split at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · obtain ⟨h1, h2, _⟩ := heap_write_ok h
            refine ⟨sc, [], rfl, by rw [view_kids, h1]; simp [SCell.active, hd], List.nil_sublist _, h2⟩
        · obtain ⟨h1, h2, _⟩ := heap_write_ok h
          refine ⟨sc, [], rfl, by rw [view_kids, h1]; simp [SCell.active, hd], List.nil_sublist _, h2⟩
      · cases hss : sc.slots with
        | none => simp [hss, throw, throwThe, MonadExceptOf.throw] at h
        | some ss =>
          simp only [hss] at h
          split at h
          · cases h
          · rename_i g1 hw1
            obtain ⟨h1, h2, _⟩ := heap_write_ok hw1
            obtain ⟨c1, hc1, hc2, hoff, _⟩ := setChildrenRaw_ok h
            rw [h1] at hc1; cases hc1
            refine ⟨sc, _, rfl, by rw [view_kids, hc2]; rfl, ?_, fun x hx => by rw [hoff x hx, h2 x hx]⟩
            have := active_slots_sublist D sc.degree ss
            simpa [SCell.active, hss] using this

theorem set_node_noalias_ok_holds : set_node_noalias_ok := by
  intro T g g' D r t s hr hs hst hsub h
  obtain ⟨sc, K, hsc, hK, hKs, hoff⟩ := setNode_ok h
  have hcv : g.view.cells s = some sc.toCell := by rw [view_cells, hsc]; rfl
  have hmem : ∀ b ∈ K, b ∈ sc.toCell.children := fun b hb => hKs.subset hb
  refine noAlias_set_kids (view_kids_off hoff) hr hK
    (hKs.nodup (noAlias_kids_nodup hs hcv)) ?_ ?_ ?_ ?_
  · intro b hb; exact noAlias_child hs hcv (hmem b hb)
  · intro b hb h; exact hst (reach_trans (reach_mem hcv (hmem b hb)) h)
  · intro b hb x hbx hrx; exact hsub x (reach_trans (reach_mem hcv (hmem b hb)) hbx) hrx
  · intro b hb b' hb' hne; exact noAlias_mem_disjoint hs hcv (hmem b hb) (hmem b' hb') hne

/-- `set_node!(t, s)` with a branch `s` makes `t` hold the very child objects
of `s` (a shallow copy, as documented: "Set every field of `tree` equal to the
corresponding field of `new_tree`", `src/Node.jl:485-489`), so afterwards the
trees of `t` and `s` share those children. -/
def set_node_shares_children_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D t s : Nat) (sc : SCell T) (ss : List (Option Addr)),
    g.cells s = some sc → sc.slots = some ss → ss.length = D → sc.degree ≠ 0 → t ≠ s →
    setNode g D t s = .ok g' → kids g'.view t = kids g'.view s ∧ kids g'.view s = kids g.view s

theorem set_node_shares_children_ok_holds : set_node_shares_children_ok := by
  intro T g g' D t s sc ss hsc hss hlen hd hts h
  unfold setNode at h
  cases ht : g.cells t with
  | none => simp [Heap.read, hsc, ht, bind, Except.bind] at h
  | some tc =>
    simp only [Heap.read, hsc, ht, bind, Except.bind, hd, ↓reduceIte, hss] at h
    split at h
    · cases h
    · rename_i g1 hw1
      obtain ⟨h1, h2, _⟩ := heap_write_ok hw1
      obtain ⟨c1, hc1, hc2, hoff, _⟩ := setChildrenRaw_ok h
      rw [h1] at hc1; cases hc1
      have hself : slotsOf D ss = ss := by rw [slotsOf_eq, hlen]; simp [← hlen]
      have hs' : g'.cells s = g.cells s := by
        rw [hoff s (Ne.symm hts), h2 s (Ne.symm hts)]
      refine ⟨?_, by rw [view_kids, view_kids, hs']⟩
      rw [view_kids, view_kids, hc2, hs', hsc]
      simp [SCell.active, hself, hss]

example : ∃ (g : SGraph Nat) (sc : SCell Nat), g.cells 0 = some sc ∧ sc.slots = some [none, none] := by
  refine ⟨(Heap.empty.alloc { (blankCell : SCell Nat) with slots := some [none, none] }).2, _, rfl, rfl⟩

/-! ## `set_scalar_constants!` -/

theorem setValue_kids {g g' : Graph T} {a : Addr} {v : T} (h : NodeUtils.setValue g a v = .ok g') :
    ∀ x, kids g' x = kids g x := by
  unfold NodeUtils.setValue at h
  cases hc : g.cells a with
  | none => simp [Heap.read, hc, bind, Except.bind] at h
  | some c =>
    simp only [Heap.read, hc, bind, Except.bind] at h
    obtain ⟨h1, h2, _, _⟩ := write_cells h
    intro x
    by_cases hx : x = a
    · subst hx; simp [kids, h1, hc]
    · simp [kids, h2 x hx]

theorem setLoop_kids {g g' : Graph T} :
    ∀ (vs : List T) (rs : List Addr), NodeUtils.setScalarConstantsLoop g vs rs = .ok g' →
      ∀ x, kids g' x = kids g x := by
  intro vs
  induction vs generalizing g with
  | nil =>
    intro rs h
    cases rs with
    | nil => cases h; intro x; rfl
    | cons _ _ => cases h
  | cons v vs ih =>
    intro rs h
    cases rs with
    | nil => cases h
    | cons a rs =>
      simp only [NodeUtils.setScalarConstantsLoop, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i h1 hv
        intro x
        rw [ih rs h x, setValue_kids hv x]

/-- `set_scalar_constants!(tree, constants, refs)` (`src/NodeUtils.jl:126-130`)
only writes value fields, so it changes no child reference and keeps every
alias-free tree alias-free. -/
def set_scalar_constants_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : Graph T) (vs : List T) (rs : List Addr) (r : Addr),
    NoAlias g r → NodeUtils.setScalarConstants g vs rs = .ok g' →
      NoAlias g' r ∧ ∀ x, kids g' x = kids g x

theorem set_scalar_constants_noalias_ok_holds : set_scalar_constants_noalias_ok := by
  intro T g g' vs rs r hr h
  unfold NodeUtils.setScalarConstants at h
  split at h
  · have hk := setLoop_kids vs rs h
    refine ⟨noAlias_transfer (fun x _ => hk x) hr, hk⟩
  · cases h

/-! ## `simplify_tree!` -/

theorem ite_ok {α : Type} {b : Prop} [Decidable b] {x y : Jl α} {a : α}
    (h : (if b then x else y) = .ok a) : x = .ok a ∨ y = .ok a := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte] at h; exact Or.inl h
  · simp only [hb, ↓reduceIte] at h; exact Or.inr h

theorem combineChildren_shrinks [JlValue T] {o : OpEnum T} {g g' : Graph T} {p : Addr}
    {cs : List Addr} (h : Simplify.combineChildren o g p cs = .ok g') : Shrinks g g' := by
  unfold Simplify.combineChildren at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rcases ite_ok h with h | h
  · cases (Except.ok.inj h : g = g'); exact shrinks_refl _
  split at h
  · cases h
  rcases ite_ok h with h | h
  · cases (Except.ok.inj h : g = g'); exact shrinks_refl _
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    rcases ite_ok h with h | h
    · cases (Except.ok.inj h : g = g'); exact shrinks_refl _
    · exact shrinks_write h (Or.inr rfl)
  · split at h
    · cases h
    · rename_i heq
      simp [throw, throwThe, MonadExceptOf.throw] at heq

theorem simplifyTree_shrinks [JlValue T] (o : OpEnum T) :
    ∀ (fuel : Nat) (g g' : Graph T) (a r : Addr),
      Simplify.simplifyTree o fuel g a = .ok (r, g') → r = a ∧ Shrinks g g' := by
  intro fuel
  induction fuel with
  | zero => intro g g' a r h; simp [Simplify.simplifyTree, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ fuel ih =>
    intro g g' a r h
    simp only [Simplify.simplifyTree, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i c hc
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, shrinks_refl _⟩
      · split at h
        · cases h
        · rename_i cs hcs
          split at h
          · cases h
          · rename_i acc hfold
            split at h
            · cases h
            · rename_i g2 hcomb
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨rfl, shrinks_trans ?_ (combineChildren_shrinks hcomb)⟩
              have fold : ∀ (l : List Addr) (init : List Addr × Graph T) (out : List Addr × Graph T),
                  l.foldlM (fun (acc : List Addr × Graph T) ch => do
                    let (r, g') ← Simplify.simplifyTree o fuel acc.2 ch
                    pure (acc.1 ++ [r], g')) init = .ok out → Shrinks init.2 out.2 := by
                intro l
                induction l with
                | nil => intro init out h; cases h; exact shrinks_refl _
                | cons ch l ihl =>
                  intro init out h
                  simp only [List.foldlM_cons, bind, Except.bind] at h
                  split at h
                  · cases h
                  · rename_i mid hmid
                    split at hmid
                    · cases hmid
                    · rename_i rg hst
                      simp only [pure, Except.pure, Except.ok.injEq] at hmid
                      subst hmid
                      exact shrinks_trans (ih _ _ _ _ hst).2 (ihl _ _ h)
              exact fold cs ([], g) acc hfold

/-- `simplify_tree!(tree, operators)` (`src/Simplify.jl:145-149`) returns the
same root and only turns branches into constant leaves, so an alias-free tree
stays alias-free and the result contains only objects of the input tree. -/
def simplify_tree_noalias_ok : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (fuel : Nat) (g g' : Graph T) (a r : Addr),
    NoAlias g a → Simplify.simplifyTree o fuel g a = .ok (r, g') →
      r = a ∧ NoAlias g' r ∧ ∀ x, Reachable g' r x → Reachable g a x

theorem simplify_tree_noalias_ok_holds : simplify_tree_noalias_ok := by
  intro T _ o fuel g g' a r ha h
  obtain ⟨rfl, hs⟩ := simplifyTree_shrinks o fuel g g' a r h
  exact ⟨rfl, noAlias_shrinks hs ha, fun x hx => reach_shrinks hs hx⟩

/-! ## Registered properties: success proven from input conditions -/

theorem heap_write_exists {α : Type} {g : Heap α} {a : Addr} (h : (g.cells a).isSome) (v : α) :
    ∃ g', g.write a v = .ok g' := by
  unfold Heap.write
  have hn : ¬ g.cells a = none := by intro hn; rw [hn] at h; cases h
  simp only [hn, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem set_same_slot {α : Type} : ∀ (l : List α) (k : Nat) (x : α), l[k]? = some x → l.set k x = l
  | [], _, _, h => by simp at h
  | y :: ys, 0, x, h => by simp at h; subst h; rfl
  | y :: ys, k + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ, set_same_slot ys k x h]

/-- `set_child!(n, child, i)` (`src/Node.jl:224-227`) on an existing node with a
full `D`-slot children tuple and `1 ≤ i ≤ D` succeeds (NodeBase `set_child`)
and keeps every enclosing alias-free tree alias-free when `child` is an
alias-free tree sharing no object with it, or is the object already stored in
slot `i` (writing back the current child). -/
def set_child_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D r n child i : Nat) (c : SCell T) (s : List (Option Addr)),
    g.cells n = some c → c.slots = some s → s.length = D → 1 ≤ i → i ≤ D →
    NoAlias g.view r → Reachable g.view r n → NoAlias g.view child →
    (Disjoint g.view r child ∨ s[i - 1]? = some (some child)) →
    ∃ g', setChild g D n child i = .ok (child, g') ∧ NoAlias g'.view r

theorem set_child_noalias_holds : set_child_noalias := by
  intro T g D r n child i c s hc hs hlen hi1 hiD hr hrn hch hdis
  obtain ⟨g', hok, -, -, hoff, hn⟩ := set_child_holds T g D n child i c s hc hs hlen hi1 hiD
  refine ⟨g', hok, ?_⟩
  rcases hdis with hd | hcur
  · exact set_child_noalias_ok_holds T g g' D r n child i child hr hrn hch hd hok
  · have hsame : g'.cells n = g.cells n := by
      rw [hn, set_same_slot s (i - 1) (some child) hcur, hc]
      cases c; simp only at hs; subst hs; rfl
    have hall : ∀ x, kids g'.view x = kids g.view x := by
      intro x
      by_cases hx : x = n
      · subst hx; rw [view_kids, view_kids, hsame]
      · rw [view_kids, view_kids, hoff x hx]
    exact noAlias_transfer (fun x _ => hall x) hr

/-- `set_children!(n, cs)` (`src/Node.jl:235-256`) on an existing node with at
most `D` children succeeds (NodeBase `set_children`) and keeps every enclosing
alias-free tree alias-free when the new children are distinct, alias-free,
pairwise disjoint trees, each of which shares no object with the enclosing tree
or is a current child of `n` (e.g. writing back or reordering the current
children). -/
def set_children_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D r n : Nat) (c : SCell T) (cs : List Addr),
    g.cells n = some c → cs.length ≤ D →
    NoAlias g.view r → Reachable g.view r n → (∀ b ∈ cs, NoAlias g.view b) →
    PairDisj g.view cs → (∀ b ∈ cs, Disjoint g.view r b ∨ b ∈ c.active) →
    ∃ g', setChildren g D n cs = .ok g' ∧ NoAlias g'.view r

theorem set_children_noalias_holds : set_children_noalias := by
  intro T g D r n c cs hc hlen hr hrn hna hpd hdis
  obtain ⟨g', hok, -⟩ := set_children_holds T g D n cs c hc hlen
  refine ⟨g', hok, ?_⟩
  obtain ⟨c0, hc0, hc1, hoff, _⟩ := setChildrenRaw_ok hok
  rw [hc] at hc0; cases hc0
  let K := ((slotsOf D (cs.map some)).take c.degree).filterMap id
  have hK : kids g'.view n = some K := by rw [view_kids, hc1]; rfl
  have hsub : List.Sublist K cs := by
    have h1 := active_slots_sublist D c.degree (cs.map some)
    have h2 : ((cs.map some).take c.degree).filterMap id = cs.take c.degree := by
      rw [← List.map_take, List.filterMap_map]; exact List.filterMap_some
    rw [h2] at h1
    exact h1.trans (List.take_sublist _ _)
  have hcv : g.view.cells n = some c.toCell := by rw [view_cells, hc]; rfl
  refine noAlias_set_kids (view_kids_off hoff) hr hK (hsub.nodup hpd.1) ?_ ?_ ?_ ?_
  · intro b hb; exact hna b (hsub.subset hb)
  · intro b hb h
    rcases hdis b (hsub.subset hb) with hd | hm
    · exact hd n hrn h
    · exact (old_kid_facts hr hrn hcv hm).2.1 h
  · intro b hb x hbx hrx
    rcases hdis b (hsub.subset hb) with hd | hm
    · exact absurd (hd x hrx hbx) id
    · exact reach_trans (old_kid_facts hr hrn hcv hm).2.2 hbx
  · intro b hb b' hb' hne; exact hpd.2 b (hsub.subset hb) b' (hsub.subset hb') hne

/-- `set_node!(t, s)` (`src/Node.jl:490-512`) for existing `t` and a valid
source `s` (a constant leaf holds a value; a branch has a full `D`-slot
children tuple) succeeds (NodeBase `set_node`) and keeps every enclosing
alias-free tree alias-free when `s` is alias-free, does not reach `t`, and
meets the enclosing tree only inside the subtree of `t`. -/
def set_node_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D r t s : Nat) (tc sc : SCell T) (ss : List (Option Addr)),
    g.cells t = some tc → g.cells s = some sc → ss.length = D →
    (sc.degree = 0 → sc.constant = true → sc.val.isSome) → (sc.degree ≠ 0 → sc.slots = some ss) →
    NoAlias g.view r → NoAlias g.view s → ¬ Reachable g.view s t →
    (∀ x, Reachable g.view s x → Reachable g.view r x → Reachable g.view t x) →
    ∃ g', setNode g D t s = .ok g' ∧ NoAlias g'.view r

theorem set_node_noalias_holds : set_node_noalias := by
  intro T g D r t s tc sc ss ht hs hlen hval hslots hr hsna hst hsub
  have hreach : ∀ b, Graph.Reachable g.view s b → b ≠ t := by
    intro b hb hbt; subst hbt; exact hst hb
  obtain ⟨g', hok, -⟩ := set_node_holds T g D t s tc sc ss ht hs hlen hval hslots hreach
  exact ⟨g', hok, set_node_noalias_ok_holds T g g' D r t s hr hsna hst hsub hok⟩

/-- Exposure: `set_node!(t, s)` with an existing `t` and a branch `s` with a
full `D`-slot children tuple succeeds and makes `t` hold the very child
objects of `s` (documented shallow field copy, `src/Node.jl:485-489`), so
afterwards the trees of `t` and `s` share those children. -/
def set_node_shares_children : Prop :=
  ∀ (T : Type) (g : SGraph T) (D t s : Nat) (tc sc : SCell T) (ss : List (Option Addr)),
    g.cells t = some tc → g.cells s = some sc → sc.slots = some ss → ss.length = D →
    sc.degree ≠ 0 → t ≠ s →
    ∃ g', setNode g D t s = .ok g' ∧ kids g'.view t = kids g'.view s ∧ kids g'.view s = kids g.view s

theorem set_node_shares_children_holds : set_node_shares_children := by
  intro T g D t s tc sc ss ht hsc hss hlen hd hts
  have hok : ∃ g', setNode g D t s = .ok g' := by
    obtain ⟨g1, hw1⟩ := heap_write_exists (g := g) (a := t) (by simp [ht])
      { tc with degree := sc.degree, op := sc.op }
    have ht1 : g1.cells t = some { tc with degree := sc.degree, op := sc.op } :=
      (heap_write_ok hw1).1
    obtain ⟨g2, hw2⟩ := heap_write_exists (g := g1) (a := t) (by simp [ht1])
      { tc with degree := sc.degree, op := sc.op, slots := some (slotsOf D ss) }
    refine ⟨g2, ?_⟩
    have hng : ¬ D < ss.length := by omega
    simp [setNode, Heap.read, hsc, ht, bind, Except.bind, hd, hss, hw1, setChildrenRaw, ht1, hw2,
      hng]
  obtain ⟨g', hg'⟩ := hok
  exact ⟨g', hg', set_node_shares_children_ok_holds T g g' D t s sc ss hsc hss hlen hd hts hg'⟩

theorem setValue_exists {g : Graph T} {a : Addr} (ha : (g.cells a).isSome) (v : T) :
    ∃ g', NodeUtils.setValue g a v = .ok g' ∧ ∀ x, (g'.cells x).isSome = (g.cells x).isSome := by
  cases hc : g.cells a with
  | none => rw [hc] at ha; cases ha
  | some c =>
    obtain ⟨g', hw⟩ := heap_write_exists (g := g) (a := a) (by simp [hc]) { c with val := some v }
    refine ⟨g', by simp [NodeUtils.setValue, Heap.read, hc, bind, Except.bind, hw], fun x => ?_⟩
    obtain ⟨h1, h2, _, _⟩ := write_cells hw
    by_cases hx : x = a
    · subst hx; simp [h1, hc]
    · rw [h2 x hx]

theorem setLoop_exists : ∀ (vs : List T) (rs : List Addr) (g : Graph T),
    vs.length = rs.length → (∀ a ∈ rs, (g.cells a).isSome) →
    ∃ g', NodeUtils.setScalarConstantsLoop g vs rs = .ok g' := by
  intro vs
  induction vs with
  | nil =>
    intro rs g hl _
    cases rs with
    | nil => exact ⟨g, rfl⟩
    | cons _ _ => cases hl
  | cons v vs ih =>
    intro rs g hl hrs
    cases rs with
    | nil => cases hl
    | cons a rs =>
      obtain ⟨g1, h1, hpres⟩ := setValue_exists (hrs a (by simp)) v
      obtain ⟨g2, h2⟩ := ih rs g1 (by simpa using hl) (fun b hb => by
        rw [hpres b]; exact hrs b (by simp [hb]))
      exact ⟨g2, by simp [NodeUtils.setScalarConstantsLoop, h1, bind, Except.bind, h2]⟩

/-- `set_scalar_constants!(tree, constants, refs)` (`src/NodeUtils.jl:126-130`)
with as many constants as refs, each ref naming an existing node, succeeds,
writes only value fields, changes no child reference, and keeps every
alias-free tree alias-free. -/
def set_scalar_constants_noalias : Prop :=
  ∀ (T : Type) (g : Graph T) (vs : List T) (rs : List Addr) (r : Addr),
    vs.length = rs.length → (∀ a ∈ rs, (g.cells a).isSome) → NoAlias g r →
    ∃ g', NodeUtils.setScalarConstants g vs rs = .ok g' ∧ NoAlias g' r ∧ ∀ x, kids g' x = kids g x

theorem set_scalar_constants_noalias_holds : set_scalar_constants_noalias := by
  intro T g vs rs r hl hrs hr
  obtain ⟨g', hloop⟩ := setLoop_exists vs rs g hl hrs
  have hok : NodeUtils.setScalarConstants g vs rs = .ok g' := by
    simp only [NodeUtils.setScalarConstants, hl, ↓reduceIte, hloop]
  exact ⟨g', hok, set_scalar_constants_noalias_ok_holds T g g' vs rs r hr hok⟩

example : ∀ a ∈ ([0] : List Addr), ((Heap.empty.alloc (⟨0, true, some 3, 0, 0, []⟩ : Cell Nat)).2.cells a).isSome := by
  intro a ha; simp at ha; subst ha; rfl

/-- `simplify_tree!(tree, operators)` (`src/Simplify.jl:145-149`) on an
alias-free graph that unfolds to a well-formed tree succeeds (success from the
Simplify slice's `simplify_matches_spec`), returns the same root, and leaves
an alias-free tree that contains only objects of the input tree. -/
def simplify_tree_noalias : Prop :=
  ∀ (T : Type) [JlValue T] (o : OpEnum T) (D nf fuel : Nat) (g : Graph T) (a : Addr) (t : Tree T),
    g.unfold fuel a = some t → t.WF D o.nops nf → NoAlias g a →
    ∃ g', Simplify.simplifyTree o fuel g a = .ok (a, g') ∧ NoAlias g' a ∧
      ∀ x, Reachable g' a x → Reachable g a x

theorem simplify_tree_noalias_holds : simplify_tree_noalias := by
  intro T _ o D nf fuel g a t hu hw ha
  obtain ⟨g', hok, -⟩ := Simplify.simplify_matches_spec_proof T o D nf fuel g a t hu hw
  obtain ⟨-, hn, hreach⟩ := simplify_tree_noalias_ok_holds T o fuel g g' a a ha hok
  exact ⟨g', hok, hn, hreach⟩

end DynExpr.NoAlias
