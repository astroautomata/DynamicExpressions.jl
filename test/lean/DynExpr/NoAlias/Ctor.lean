import DynExpr.NoAlias.Core
import DynExpr.NodeBase.Heap

/-!
Alias-freedom of the generic node constructor
`N(; val, feature, op, l, r, children)` (`src/Node.jl:350-430`), using the
NodeBase heap mirror `NodeBase.ctor`, whose objects keep the full children
tuple (`SCell`) and are viewed as `Cell`s through `SGraph.view`.
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

/-! ## Heap facts for the NodeBase mirror -/

theorem view_cells (g : SGraph T) (a : Addr) : g.view.cells a = (g.cells a).map SCell.toCell := rfl

theorem view_kids (g : SGraph T) (a : Addr) : kids g.view a = (g.cells a).map SCell.active := by
  simp only [kids, view_cells]
  cases g.cells a <;> rfl

theorem view_next (g : SGraph T) : g.view.next = g.next := rfl

/-- The second heap only adds objects: existing objects are unchanged. -/
def Ext (g g' : SGraph T) : Prop := g.next ≤ g'.next ∧ ∀ x, x < g.next → g'.cells x = g.cells x

theorem ext_refl (g : SGraph T) : Ext g g := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem ext_trans {g h k : SGraph T} (h1 : Ext g h) (h2 : Ext h k) : Ext g k :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem sameKidsOn_ext {g g' : SGraph T} {a : Addr} (he : Ext g g') (hc : Closed g.view a) :
    SameKidsOn g.view g'.view a := by
  intro x hx
  rw [view_kids, view_kids, he.2 x (closed_lt hc hx)]

/-- A list of input trees: each alias-free and closed. -/
def Trees (g : Graph T) (l : List Addr) : Prop := ∀ b ∈ l, NoAlias g b ∧ Closed g b

/-- Distinct input trees sharing no object. -/
def PairDisj (g : Graph T) (l : List Addr) : Prop :=
  l.Nodup ∧ ∀ b ∈ l, ∀ b' ∈ l, b ≠ b' → Disjoint g b b'

/-- A freshly allocated object whose children are alias-free, closed, distinct,
pairwise disjoint trees is the root of an alias-free closed tree made of
itself and those trees. -/
theorem fresh_node {g G : Graph T} {n : Addr} {K : List Addr}
    (hn : n = g.next) (hoff : ∀ x, x ≠ n → kids G x = kids g x) (hK : kids G n = some K)
    (htr : Trees g K) (hpd : PairDisj g K) :
    NoAlias G n ∧ Closed G n ∧ ∀ x, Reachable G n x → x = n ∨ ∃ b ∈ K, Reachable g b x := by
  have hsame : ∀ b ∈ K, SameKidsOn g G b := by
    intro b hb x hx
    exact hoff x (by rw [hn]; exact Nat.ne_of_lt (closed_lt (htr b hb).2 hx))
  obtain ⟨c, hc, hch⟩ := cell_of_kids hK
  have hreach : ∀ x, Reachable G n x → x = n ∨ ∃ b ∈ K, Reachable g b x := by
    intro x hx
    rcases reach_inv hx with rfl | ⟨c', b, hc', hb, hbx⟩
    · exact Or.inl rfl
    · rw [hc] at hc'; cases hc'
      rw [hch] at hb
      exact Or.inr ⟨b, hb, (reach_transfer (hsame b hb)).mp hbx⟩
  refine ⟨?_, ?_, hreach⟩
  · refine noAlias_node hc (by rw [hch]; exact hpd.1) ?_ ?_ ?_
    · intro b hb; rw [hch] at hb
      exact noAlias_transfer (hsame b hb) (htr b hb).1
    · intro b hb hbn; rw [hch] at hb
      have := closed_lt (htr b hb).2 ((reach_transfer (hsame b hb)).mp hbn)
      rw [hn] at this
      exact Nat.lt_irrefl _ this
    · intro b hb b' hb' hne; rw [hch] at hb hb'
      exact disjoint_transfer (hsame b hb) (hsame b' hb') (hpd.2 b hb b' hb' hne)
  · intro x hx
    rcases hreach x hx with rfl | ⟨b, hb, hbx⟩
    · simp [hc]
    · have hxs := (htr b hb).2 x hbx
      have hlt := closed_lt (htr b hb).2 hbx
      have hk := hoff x (by rw [hn]; exact Nat.ne_of_lt hlt)
      cases hgx : g.cells x with
      | none => simp [hgx] at hxs
      | some cx =>
        rw [kids_some hgx] at hk
        obtain ⟨c', hc', _⟩ := cell_of_kids hk
        simp [hc']

/-! ## The constructor -/

/-- Children passed to the constructor: `(l,)`, `(l, r)` or `children`
(`src/Node.jl:354-362`). -/
def ctorKids (kw : Kw T) : List Addr :=
  match kw.l, kw.r with
  | some l, none => [l]
  | some l, some r => [l, r]
  | none, _ => kw.children.getD []

theorem active_slotsOf (D : Nat) (cs : List Addr) (h : cs.length ≤ D) :
    ((slotsOf D (cs.map some)).take cs.length).filterMap id = cs := by
  have ht : (slotsOf D (cs.map some)).take cs.length = cs.map some := by
    apply List.ext_getElem
    · simp [slotsOf]; omega
    · intro i h1 h2
      simp at h2
      simp [slotsOf, h2]
  rw [ht, List.filterMap_map]
  exact List.filterMap_some

theorem heap_write_ok {α : Type} {g g' : Heap α} {w : Addr} {v : α} (hw : g.write w v = .ok g') :
    g'.cells w = some v ∧ (∀ x, x ≠ w → g'.cells x = g.cells x) ∧ g'.next = g.next := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw
    exact ⟨by simp, fun x hx => by simp [hx], rfl⟩

theorem setChildrenRaw_ok {g g' : SGraph T} {D n : Nat} {cs : List (Option Addr)}
    (h : setChildrenRaw g D n cs = .ok g') :
    ∃ c, g.cells n = some c ∧ g'.cells n = some { c with slots := some (slotsOf D cs) } ∧
      (∀ x, x ≠ n → g'.cells x = g.cells x) ∧ g'.next = g.next := by
  unfold setChildrenRaw at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  cases hc : g.cells n with
  | none => simp [Heap.read, hc, bind, Except.bind] at h
  | some c =>
    simp only [Heap.read, hc, bind, Except.bind] at h
    obtain ⟨h1, h2, h3⟩ := heap_write_ok h
    exact ⟨c, rfl, h1, h2, h3⟩

private theorem leaf_result (g : SGraph T) (c : SCell T) (hs : c.slots = none) (kw : Kw T)
    (hop : kw.op = none) :
    (g.alloc c).2.next = g.next + 1 ∧ (∀ x, x ≠ g.next → (g.alloc c).2.cells x = g.cells x) ∧
      ∃ c', (g.alloc c).2.cells g.next = some c' ∧ ((kw.op = none ∧ c'.active = []) ∨ c'.active = ctorKids kw) :=
  ⟨rfl, fun x hx => by simp [Heap.alloc, hx], c, by simp [Heap.alloc],
    Or.inl ⟨hop, by simp [SCell.active, hs]⟩⟩

private theorem branch_result (g g' : SGraph T) (D o : Nat) (cs : List Addr) (kw : Kw T)
    (hk : ctorKids kw = cs) (hlen : cs.length ≤ D)
    (h : setChildren (g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }).2 D
      g.next cs = .ok g') :
    g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      ∃ c', g'.cells g.next = some c' ∧ ((kw.op = none ∧ c'.active = []) ∨ c'.active = ctorKids kw) := by
  obtain ⟨c, hc, h1, h2, h3⟩ := setChildrenRaw_ok h
  have hc' : c = { (blankCell : SCell T) with degree := cs.length, op := o } := by
    simp [Heap.alloc] at hc; exact hc.symm
  subst hc'
  refine ⟨by rw [h3]; rfl, fun x hx => by rw [h2 x hx]; simp [Heap.alloc, hx], _, h1,
    Or.inr ?_⟩
  rw [hk]
  exact active_slotsOf D cs hlen

private theorem leaf_of_alloc {g g' : SGraph T} {c : SCell T} {n : Addr} (kw : Kw T)
    (hs : c.slots = none) (hop : kw.op = none) (h : g.alloc c = (n, g')) :
    n = g.next ∧ g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      ∃ c, g'.cells g.next = some c ∧ ((kw.op = none ∧ c.active = []) ∨ c.active = ctorKids kw) := by
  have h1 : (g.alloc c).1 = n := by rw [h]
  have h2 : (g.alloc c).2 = g' := by rw [h]
  subst h1 h2
  exact ⟨rfl, leaf_result g c hs kw hop⟩

private theorem branch_of {g g' v : SGraph T} {D o : Nat} {cs : List Addr} {n : Addr} (kw : Kw T)
    (hk : ctorKids kw = cs) (hlen : cs.length ≤ D)
    (hs : setChildren (g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }).2 D
      g.next cs = .ok v)
    (h : ((g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }).1, v) = (n, g')) :
    n = g.next ∧ g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      ∃ c, g'.cells g.next = some c ∧ ((kw.op = none ∧ c.active = []) ∨ c.active = ctorKids kw) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h1 h2
  exact ⟨rfl, branch_result g _ D o cs kw hk hlen hs⟩

private theorem branch_full {g g' : SGraph T} {D o : Nat} {cs : List Addr} {n : Addr} (kw : Kw T)
    (hk : ctorKids kw = cs) (hlen : ¬ cs.length > D)
    (h : (if o > 255 then (throw (JlError.errorException "InexactError: trunc(UInt8, op)") :
        Jl (Addr × SGraph T)) else
      (do
        let (n, g1) := g.alloc { (blankCell : SCell T) with degree := cs.length, op := o }
        let g2 ← setChildren g1 D n cs
        pure (n, g2))) = .ok (n, g')) :
    n = g.next ∧ g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      ∃ c, g'.cells g.next = some c ∧ ((kw.op = none ∧ c.active = []) ∨ c.active = ctorKids kw) := by
  by_cases ho : o > 255
  · simp only [ho, ↓reduceIte] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [ho, ↓reduceIte] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i v hs
      simp only [Except.ok.injEq] at h
      exact branch_of kw hk (by omega) hs h

/-- Every successful constructor call allocates exactly one new object at
`g.next`, leaves all other objects unchanged, and the new object's active
children are either none (leaf) or exactly the passed children. -/
theorem ctor_ok {g g' : SGraph T} {D : Nat} {hasD : Bool} {kw : Kw T} {n : Addr}
    (h : ctor g D hasD kw = .ok (n, g')) :
    n = g.next ∧ g'.next = g.next + 1 ∧ (∀ x, x ≠ g.next → g'.cells x = g.cells x) ∧
      ∃ c, g'.cells g.next = some c ∧ ((kw.op = none ∧ c.active = []) ∨ c.active = ctorKids kw) := by
  obtain ⟨val, feature, op, l, r, children⟩ := kw
  rcases l with _ | l <;> rcases r with _ | r <;> rcases children with _ | cs <;>
    rcases val with _ | v <;> rcases feature with _ | i <;> rcases op with _ | o <;>
    (try simp only [ctor, bind, Except.bind, pure, Except.pure, Option.isSome_none,
      Option.isSome_some, Bool.false_eq_true, ↓reduceIte] at h)
  all_goals repeat (first | (cases h; done) | split at h)
  all_goals try (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
  all_goals try (simp only [Except.ok.injEq] at h; exact leaf_of_alloc _ rfl rfl h)
  all_goals try (exact branch_full _ rfl (by assumption) h)
  all_goals done

/-- A constructor result built from given input trees: only new objects were
added, the result is an alias-free closed tree, and it consists of new objects
and objects of the inputs. -/
structure Built (g g' : SGraph T) (ins : List Addr) (r : Addr) : Prop where
  ext : Ext g g'
  noAlias : NoAlias g'.view r
  closed : Closed g'.view r
  reach : ∀ x, Reachable g'.view r x → g.next ≤ x ∨ ∃ b ∈ ins, Reachable g.view b x

theorem trees_nil (g : Graph T) : Trees g [] := fun _ h => absurd h List.not_mem_nil

theorem pairDisj_nil (g : Graph T) : PairDisj g [] :=
  ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem ctor_built {g g' : SGraph T} {D : Nat} {hasD : Bool} {kw : Kw T} {n : Addr}
    (htr : Trees g.view (ctorKids kw)) (hpd : PairDisj g.view (ctorKids kw))
    (h : ctor g D hasD kw = .ok (n, g')) : n = g.next ∧ Built g g' (ctorKids kw) n := by
  obtain ⟨hn, hnext, hoff, c, hc, hact⟩ := ctor_ok h
  have hoff' : ∀ x, x ≠ n → kids g'.view x = kids g.view x := by
    intro x hx; rw [view_kids, view_kids, hoff x (by rw [← hn]; exact hx)]
  have hK : kids g'.view n = some c.active := by rw [view_kids, hn, hc]; rfl
  have hext : Ext g g' := ⟨by omega, fun x hx => hoff x (Nat.ne_of_lt hx)⟩
  rcases hact with ⟨_, hnil⟩ | hk
  · rw [hnil] at hK
    obtain ⟨h1, h2, h3⟩ := fresh_node (g := g.view) hn hoff' hK (trees_nil _) (pairDisj_nil _)
    refine ⟨hn, hext, h1, h2, fun x hx => ?_⟩
    rcases h3 x hx with rfl | ⟨b, hb, _⟩
    · exact Or.inl (by rw [hn]; exact Nat.le_refl _)
    · exact absurd hb List.not_mem_nil
  · rw [hk] at hK
    obtain ⟨h1, h2, h3⟩ := fresh_node (g := g.view) hn hoff' hK htr hpd
    refine ⟨hn, hext, h1, h2, fun x hx => ?_⟩
    rcases h3 x hx with rfl | hb
    · exact Or.inl (by rw [hn]; exact Nat.le_refl _)
    · exact Or.inr hb

/-! ## Properties -/

/-! ## Success of the constructor on valid keyword combinations -/

/-- Keyword combinations the constructor accepts (`src/Node.jl:350-430`): only
`val`; only `feature` (fitting `UInt16`); or `op` (fitting `UInt8`) with children
given by `l` (and possibly `r`, without `children`) or by `children`, at most
`D` of them. `r` without `l` throws (`src/Node.jl:353`). -/
def ValidKw (D : Nat) (kw : Kw T) : Prop :=
  (kw.val.isSome ∧ kw.feature = none ∧ kw.op = none ∧ kw.l = none ∧ kw.r = none ∧
    kw.children = none) ∨
  (kw.val = none ∧ (∃ i, kw.feature = some i ∧ i ≤ 65535) ∧ kw.op = none ∧ kw.l = none ∧
    kw.r = none ∧ kw.children = none) ∨
  (kw.val = none ∧ kw.feature = none ∧ (∃ o, kw.op = some o ∧ o ≤ 255) ∧
    ((kw.l.isSome ∧ kw.children = none) ∨ (kw.l = none ∧ kw.r = none ∧ kw.children.isSome)) ∧
    (ctorKids kw).length ≤ D)

theorem ctor_val_ok (g : SGraph T) (D : Nat) (hasD : Bool) (v : T) :
    ∃ p, ctor g D hasD { val := some v } = .ok p :=
  let ⟨_, h, _⟩ := ((ctor_nodes_holds T g D hasD).1 v); ⟨_, h⟩

theorem ctor_feature_ok (g : SGraph T) (D : Nat) (hasD : Bool) (i : Nat) (hi : i ≤ 65535) :
    ∃ p, ctor g D hasD { feature := some i } = .ok p :=
  let ⟨_, h, _⟩ := ((ctor_nodes_holds T g D hasD).2.1 i hi); ⟨_, h⟩

theorem ctor_op_ok (g : SGraph T) (D : Nat) (hasD : Bool) (o : Nat) (cs : List Addr)
    (ho : o ≤ 255) (hlen : cs.length ≤ D) :
    ∃ p, ctor g D hasD { op := some o, children := some cs } = .ok p :=
  let ⟨_, h, _⟩ := ((ctor_nodes_holds T g D hasD).2.2.1 o cs ho hlen); ⟨_, h⟩

/-- Every valid keyword combination succeeds (via NodeBase `ctor_nodes`). -/
theorem ctor_success (g : SGraph T) (D : Nat) (hasD : Bool) (kw : Kw T) (hv : ValidKw D kw) :
    ∃ p, ctor g D hasD kw = .ok p := by
  obtain ⟨val, feature, op, l, r, children⟩ := kw
  rcases hv with ⟨hval, hf, hop, hl, hr, hch⟩ | ⟨hval, ⟨i, hf, hi⟩, hop, hl, hr, hch⟩ |
      ⟨hval, hf, ⟨o, hop, ho⟩, hkids, hlen⟩
  · simp only at hval hf hop hl hr hch
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp hval
    subst hf hop hl hr hch
    exact ctor_val_ok g D hasD v
  · simp only at hval hf hop hl hr hch
    subst hval hf hop hl hr hch
    exact ctor_feature_ok g D hasD i hi
  · simp only at hval hf hop
    subst hval hf hop
    rcases hkids with ⟨hl, hch⟩ | ⟨hl, hr, hch⟩
    · simp only at hl hch
      obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp hl
      subst hch
      have hn := (ctor_nodes_holds T g D hasD).2.2.2 o a
      cases r with
      | none =>
        obtain ⟨p, hp⟩ := ctor_op_ok g D hasD o [a] ho (by simpa [ctorKids] using hlen)
        exact ⟨p, (hn a).1.trans hp⟩
      | some b =>
        obtain ⟨p, hp⟩ := ctor_op_ok g D hasD o [a, b] ho (by simpa [ctorKids] using hlen)
        exact ⟨p, ((ctor_nodes_holds T g D hasD).2.2.2 o a b).2.trans hp⟩
    · simp only at hl hr hch
      obtain ⟨cs, rfl⟩ := Option.isSome_iff_exists.mp hch
      subst hl hr
      exact ctor_op_ok g D hasD o cs ho (by simpa [ctorKids] using hlen)

/-! ## Properties -/

/-- Every valid form of the generic constructor `N(; val, feature, op, l, r,
children)` (`src/Node.jl:350-430`) succeeds and returns an alias-free tree when
the passed children are alias-free, distinct and pairwise disjoint: the result
is a new object whose subtrees are exactly the passed trees, and no existing
object changes. -/
def node_ctor_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (hasD : Bool) (kw : Kw T),
    ValidKw D kw → Trees g.view (ctorKids kw) → PairDisj g.view (ctorKids kw) →
    ∃ n g', ctor g D hasD kw = .ok (n, g') ∧
      NoAlias g'.view n ∧ Closed g'.view n ∧ (∀ x, x < g.next → g'.cells x = g.cells x) ∧
      ∀ x, Reachable g'.view n x → x = n ∨ ∃ b ∈ ctorKids kw, Reachable g.view b x

theorem node_ctor_noalias_holds : node_ctor_noalias := by
  intro T g D hasD kw hv htr hpd
  obtain ⟨⟨n, g'⟩, h⟩ := ctor_success g D hasD kw hv
  obtain ⟨hn, hb⟩ := ctor_built htr hpd h
  refine ⟨n, g', h, hb.noAlias, hb.closed, hb.ext.2, fun x hx => ?_⟩
  rcases hb.reach x hx with hle | hin
  · left
    have := closed_lt hb.closed hx
    rw [view_next, (ctor_ok h).2.1] at this
    rw [hn]; exact Nat.le_antisymm (Nat.le_of_lt_succ this) hle
  · exact Or.inr hin

/-- Example heap: one feature leaf `x1` at address 0 (the NodeBase fixture). -/
theorem oneLeaf_leaf : (oneLeaf : SGraph Nat).cells 0 =
    some { (blankCell : SCell Nat) with feature := 1 } := rfl

theorem oneLeaf_tree : NoAlias (oneLeaf : SGraph Nat).view 0 ∧ Closed (oneLeaf : SGraph Nat).view 0 := by
  have hc : (oneLeaf : SGraph Nat).view.cells 0 =
      some (SCell.toCell { (blankCell : SCell Nat) with feature := 1 }) := rfl
  have hleaf : ∀ c, (oneLeaf : SGraph Nat).view.cells 0 = some c → c.children = [] := by
    intro c h; rw [hc] at h; cases h; rfl
  refine ⟨noAlias_leaf hleaf, fun z hz => ?_⟩
  rcases reach_inv hz with rfl | ⟨c, b, hc', hb, _⟩
  · rw [hc]; rfl
  · rw [hleaf c hc'] at hb; exact absurd hb List.not_mem_nil

example : ValidKw 2 ({ op := some 1, l := some 0 } : Kw Nat) ∧
    Trees (oneLeaf : SGraph Nat).view (ctorKids ({ op := some 1, l := some 0 } : Kw Nat)) ∧
    PairDisj (oneLeaf : SGraph Nat).view (ctorKids ({ op := some 1, l := some 0 } : Kw Nat)) := by
  refine ⟨Or.inr (Or.inr ⟨rfl, rfl, ⟨1, rfl, by decide⟩, Or.inl ⟨rfl, rfl⟩, by simp [ctorKids]⟩),
    fun b hb => ?_, ⟨by simp [ctorKids], fun b hb b' hb' hne => ?_⟩⟩
  · simp [ctorKids] at hb; subst hb; exact oneLeaf_tree
  · simp [ctorKids] at hb hb'; subst hb hb'; exact absurd rfl hne

/-- Passing the same alias-free tree twice, as in `Node(op=1, children=(x, x))`
or `Node(1, x, x)`, stores the caller's object in both child slots of one new
node (the aliasing the caller asked for, accepted per QUESTIONS.md Q35), keeps
the shared child alias-free, and changes no existing object. -/
def node_ctor_repeated_child : Prop :=
  ∀ (T : Type) (g : SGraph T) (D : Nat) (hasD : Bool) (o x : Nat),
    o ≤ 255 → 2 ≤ D → NoAlias g.view x → Closed g.view x →
    ∃ n g', ctor g D hasD { op := some o, children := some [x, x] } = .ok (n, g') ∧
      n = g.next ∧ kids g'.view n = some [x, x] ∧ NoAlias g'.view x ∧
      ∀ y, y < g.next → g'.cells y = g.cells y

theorem node_ctor_repeated_child_holds : node_ctor_repeated_child := by
  intro T g D hasD o x ho hD hna hcl
  have hv : ValidKw D ({ op := some o, children := some [x, x] } : Kw T) :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨o, rfl, ho⟩, Or.inr ⟨rfl, rfl, rfl⟩, by simpa [ctorKids] using hD⟩)
  obtain ⟨⟨n, g'⟩, h⟩ := ctor_success g D hasD _ hv
  obtain ⟨hn, hnext, hoff, c, hc, hact⟩ := ctor_ok h
  have hext : Ext g g' := ⟨by omega, fun y hy => hoff y (Nat.ne_of_lt hy)⟩
  refine ⟨n, g', h, hn, ?_, noAlias_transfer (sameKidsOn_ext hext hcl) hna,
    fun y hy => hoff y (Nat.ne_of_lt hy)⟩
  rcases hact with ⟨hop, _⟩ | hk
  · cases hop
  · rw [view_kids, hn, hc]
    simp [hk, ctorKids]

example : (1 : Nat) ≤ 255 ∧ (2 : Nat) ≤ 2 ∧ NoAlias (oneLeaf : SGraph Nat).view 0 ∧
    Closed (oneLeaf : SGraph Nat).view 0 :=
  ⟨by decide, by decide, oneLeaf_tree.1, oneLeaf_tree.2⟩

end DynExpr.NoAlias
