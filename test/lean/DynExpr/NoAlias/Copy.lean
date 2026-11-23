import DynExpr.NoAlias.Operators
import DynExpr.NoAlias.Mutate
import DynExpr.NodeBase.TraverseCopy

/-!
Copies of plain `Node` trees: `copy_node` / `copy` (`src/base.jl:496-524`),
`convert` to another element type (`src/base.jl:535-568`), and the element-type
promotions that convert operands: the typed constructor storing children into
its `Nullable{N{T}}` tuple (`src/Node.jl:407-428,238-252`, `src/Utils.jl:94-96`)
and the generated mixed-type operator converters
(`src/OperatorEnumConstruction.jl:211-233`). The heap copy is NodeBase's
`copyNodeH`/`convertH` and its proven `copy_node_heap`.
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ts : List β}, l.mapM f = some ts → ∀ b ∈ l, ∃ t, f b = some t
  | [], _, _, b, hb => absurd hb List.not_mem_nil
  | x :: xs, ts, h, b, hb => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys =>
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨y, hx⟩
        · exact mapM_some_mem hxs b hb

theorem mapM_congr_opt {α β : Type} (f h : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = h x) → l.mapM f = l.mapM h := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    simp [List.mapM_cons, hx x (by simp), ih (fun y hy => hx y (by simp [hy]))]

/-- A successful unfolding visits only existing objects. -/
theorem closed_of_unfold {g : Graph T} :
    ∀ (fuel : Nat) (a : Addr) (t : Tree T), g.unfold fuel a = some t → Closed g a := by
  intro fuel
  induction fuel with
  | zero => intro a t h; simp [Graph.unfold] at h
  | succ f ih =>
    intro a t h
    simp only [Graph.unfold] at h
    cases hc : g.cells a with
    | none => simp [hc, bind, Option.bind] at h
    | some c =>
      simp only [hc, bind, Option.bind] at h
      have hkids : ∀ b ∈ c.children, ∃ t', g.unfold f b = some t' := by
        intro b hb
        by_cases hlen : c.children.length ≠ c.degree
        · simp [hlen] at h
        · by_cases hd : c.degree = 0
          · have : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
            rw [this] at hb; simp at hb
          · simp only [hlen, hd, ↓reduceIte] at h
            cases hm : c.children.mapM (Graph.unfold g f) with
            | none => simp [hm] at h
            | some ts => exact mapM_some_mem hm b hb
      intro z hz
      rcases reach_inv hz with rfl | ⟨c', b, hc', hb, hbz⟩
      · simp [hc]
      · rw [hc] at hc'; cases hc'
        obtain ⟨t', ht'⟩ := hkids b hb
        exact ih b t' ht' z hbz

/-- Unfolding only reads the objects reachable from the root. -/
theorem unfold_congr {g G : Graph T} :
    ∀ (fuel : Nat) (a : Addr), (∀ x, Reachable g a x → G.cells x = g.cells x) →
      G.unfold fuel a = g.unfold fuel a := by
  intro fuel
  induction fuel with
  | zero => intro a _; rfl
  | succ f ih =>
    intro a h
    have hview : G.cells a = g.cells a := h a (reach_refl g a)
    simp only [Graph.unfold, hview]
    cases hc : g.cells a with
    | none => rfl
    | some c =>
      have hch : ∀ b ∈ c.children, G.unfold f b = g.unfold f b := fun b hb =>
        ih b (fun x hx => h x (reach_trans (reach_mem hc hb) hx))
      simp only [bind, Option.bind]
      rw [mapM_congr_opt _ _ c.children hch]

/-- The NodeBase copy as a build with no inputs: only new objects. -/
theorem copy_built {g : SGraph T} {D fuel root : Nat} {t : Tree T} {bs : Bool}
    (hu : Graph.unfold g.view fuel root = some t) (hw : t.WF D (fun _ => 255) 65535) :
    ∃ r h, copyNodeH g D false bs fuel root = .ok (r, h) ∧ Built g h [] r := by
  obtain ⟨r, h, hc, hpres, hu', hfresh, hna, _⟩ := copy_node_heap_holds T g D fuel root t false bs hu hw
  have hcl : Closed h.view r := closed_of_unfold fuel r t hu'
  have hr : g.next ≤ r := hfresh r (reach_refl _ _)
  have hlt : (r : Nat) < h.next := closed_lt hcl (reach_refl _ _)
  exact ⟨r, h, hc, ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt hr hlt), hpres⟩, hna rfl, hcl, fun x hx => Or.inl (hfresh x hx)⟩

/-! ## `copy_node`, `copy`, `convert` -/

/-- `copy_node(tree)` and `copy(tree)` on a plain `Node` (`src/base.jl:496-524`)
return an alias-free tree made only of new objects (so it shares nothing with
the source or any other existing tree), for every finite well-formed source,
even an aliased one. Existing objects are unchanged. -/
def copy_node_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T) (bs : Bool),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    ∃ r h, copyNodeH g D false bs fuel root = .ok (r, h) ∧ NoAlias h.view r ∧
      (∀ b, Reachable h.view r b → g.next ≤ b) ∧ (∀ a, a < g.next → h.cells a = g.cells a)

theorem copy_node_noalias_holds : copy_node_noalias := by
  intro T g D fuel root t bs hu hw
  obtain ⟨r, h, hc, hb⟩ := copy_built (bs := bs) hu hw
  refine ⟨r, h, hc, hb.noAlias, fun b hbr => ?_, hb.ext.2⟩
  rcases hb.reach b hbr with h1 | ⟨_, hm, _⟩
  · exact h1
  · exact absurd hm List.not_mem_nil

/-- `convert(Node{T1}, tree::Node{T2})` (`src/base.jl:535-568`) to a different
node type returns an alias-free tree of new objects; to the same type it
returns the argument itself (Julia's `convert` convention). -/
def convert_node_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel root : Nat) (t : Tree T),
    Graph.unfold g.view fuel root = some t → t.WF D (fun _ => 255) 65535 →
    (∃ r h, convertH g D false false false fuel root = .ok (r, h) ∧ NoAlias h.view r ∧
      (∀ b, Reachable h.view r b → g.next ≤ b) ∧ (∀ a, a < g.next → h.cells a = g.cells a)) ∧
    convertH g D true false false fuel root = .ok (root, g)

theorem convert_node_noalias_holds : convert_node_noalias := by
  intro T g D fuel root t hu hw
  exact ⟨copy_node_noalias_holds T g D fuel root t true hu hw, rfl⟩

example : Graph.unfold (oneLeaf : SGraph Nat).view 1 0 = some (.feature 1) ∧
    (Tree.feature 1 : Tree Nat).WF 2 (fun _ => 255) 65535 := by
  refine ⟨rfl, ?_⟩
  simp [Tree.WF]

/-! ## Promotions that convert operands -/

/-- An operand together with whether its node type differs from the promoted
type (and is therefore converted by a copy). -/
abbrev Operand := Addr × Bool

/-- Convert each operand to the promoted node type: a `convert` copy when the
type differs, the object itself otherwise (`src/Utils.jl:94-96`,
`src/base.jl:535-541`). Evaluated left to right. -/
def convOperands (D fuel : Nat) : SGraph T → List Operand → Jl (List Addr × SGraph T)
  | g, [] => pure ([], g)
  | g, (a, conv) :: rest => do
    let (b, g1) ← convertH g D (!conv) false false fuel a
    let (bs, g2) ← convOperands D fuel g1 rest
    pure (b :: bs, g2)

/-- `N{T}(; op, children)` with children of other element types
(`src/Node.jl:407-428`): allocate the node, set `degree` and `op`, then
`set_children!` stores the children into the typed tuple field, which converts
each differently-typed child (`src/Node.jl:238-252`, `src/Utils.jl:94-96`). -/
def promotedCtor (g : SGraph T) (D fuel o : Nat) (kids : List Operand) : Jl (Addr × SGraph T) := do
  if kids.length > D then throw (.assertionError "D2 <= max_degree(N)")
  else if o > 255 then throw (.errorException "InexactError: trunc(UInt8, op)")
  else
    let (n, g1) := g.alloc { (blankCell : SCell T) with degree := kids.length, op := o }
    let (cs, g2) ← convOperands D fuel g1 kids
    let g3 ← setChildren g2 D n cs
    pure (n, g3)

/-- Mixed-type binary converter (`src/OperatorEnumConstruction.jl:211-222`):
`f(promote(l, r)...)`, converting the operands left to right and then calling
the same-type binary method. -/
def promoteBinary (g : SGraph T) (D fuel : Nat) (f : T → T → T) (idx : Nat) (l r : Operand) :
    Jl (Addr × SGraph T) := do
  let (l', g1) ← convertH g D (!l.2) false false fuel l.1
  let (r', g2) ← convertH g1 D (!r.2) false false fuel r.1
  opBinary g2 D f idx l' r'

/-- Kept operands, which are inputs of the build. -/
def kept (ops : List Operand) : List Addr := (ops.filter (fun o => !o.2)).map Prod.fst

/-- Operands that are kept are alias-free disjoint input trees; converted
operands may be any finite well-formed tree (copies are fresh). -/
def OperandsOk (g : SGraph T) (D fuel : Nat) (ops : List Operand) : Prop :=
  Trees g.view (kept ops) ∧ PairDisj g.view (kept ops) ∧
  ∀ o ∈ ops, o.2 = true → ∃ t : Tree T, Graph.unfold g.view fuel o.1 = some t ∧
    t.WF D (fun _ => 255) 65535

/-- Children of an object in the view of a NodeBase heap. -/
abbrev kids' (g : SGraph T) (a : Addr) : Option (List Addr) := kids g.view a

theorem unfold_ext {g g' : SGraph T} (he : Ext g g') (fuel : Nat) (a : Addr) (t : Tree T)
    (hu : Graph.unfold g.view fuel a = some t) : Graph.unfold g'.view fuel a = some t := by
  have hcl := closed_of_unfold fuel a t hu
  rw [unfold_congr (g := g.view) (G := g'.view) fuel a
    (fun x hx => by rw [view_cells, view_cells, he.2 x (closed_lt hcl hx)])]
  exact hu

/-- Converting the operands one after another keeps the invariant of
`Inv`: kept operands are inputs, converted ones are new objects. -/
theorem convOperands_inv {D fuel : Nat} :
    ∀ (ops : List Operand) (g0 h h' : SGraph T) (ins rs bs : List Addr),
      Inv g0 h ins rs → Trees g0.view (ins ++ kept ops) → PairDisj g0.view (ins ++ kept ops) →
      (∀ o ∈ ops, o.2 = true → ∃ t : Tree T, Graph.unfold g0.view fuel o.1 = some t ∧
        t.WF D (fun _ => 255) 65535) →
      convOperands D fuel h ops = .ok (bs, h') → Inv g0 h' (ins ++ kept ops) (rs ++ bs) := by
  intro ops
  induction ops with
  | nil =>
    intro g0 h h' ins rs bs hi _ _ _ hc
    simp only [convOperands, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simpa [kept] using hi
  | cons o ops ih =>
    intro g0 h h' ins rs bs hi ht hp hconv hc
    obtain ⟨a, cv⟩ := o
    simp only [convOperands] at hc
    obtain ⟨⟨b, h1⟩, hb, hc⟩ := bind_ok hc
    obtain ⟨⟨bs', h2⟩, hbs, hc⟩ := bind_ok hc
    have hc' : bs = b :: bs' ∧ h' = h2 := by
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
      exact ⟨hc.1.symm, hc.2.symm⟩
    rw [hc'.1, hc'.2]
    cases cv with
    | false =>
      simp only [Bool.not_false, convertH, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hb
      have hk : kept ((a, false) :: ops) = a :: kept ops := by simp [kept]
      rw [hk] at ht hp
      have hta : Trees g0.view [a] := fun x hx => ht x (by simp at hx; simp [hx])
      have hpd := pairDisj_append (l := ins) (l' := a :: kept ops) hp
      have hbuilt : Built h h1 [a] b := by
        rw [← hb.1, ← hb.2]; exact built_input (trees_ext hi.ext hta)
      have i1 := inv_step hi hbuilt hta
        (fun x hx y hy => hpd.2.2 x hx y (by simp at hy; simp [hy]))
      have := ih g0 h1 h2 (ins ++ [a]) (rs ++ [b]) bs' i1 (by simpa using ht) (by simpa using hp)
        (fun o ho hco => hconv o (by simp [ho]) hco) hbs
      rw [hk]; simpa using this
    | true =>
      simp only [Bool.not_true, Bool.not_false, convertH, Bool.false_eq_true, ↓reduceIte] at hb
      obtain ⟨t, hu, hw⟩ := hconv (a, true) (by simp) rfl
      obtain ⟨r, h1', hc1, hbuilt⟩ := copy_built (bs := true) (unfold_ext hi.ext fuel a t hu) hw
      rw [hc1] at hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at hb
      have hbuilt' : Built h h1 [] b := by rw [← hb.1, ← hb.2]; exact hbuilt
      have hk : kept ((a, true) :: ops) = kept ops := by simp [kept]
      rw [hk] at ht hp
      have i1 := inv_step hi hbuilt' (trees_nil _) (fun _ _ _ h => absurd h List.not_mem_nil)
      have := ih g0 h1 h2 (ins ++ []) (rs ++ [b]) bs' i1 (by simpa using ht) (by simpa using hp)
        (fun o ho hco => hconv o (by simp [ho]) hco) hbs
      rw [hk]; simpa using this

/-- The typed constructor `N{T}(; op, children)` with converted children
(`src/Node.jl:407-428`) returns an alias-free tree when its kept children are
alias-free, distinct and disjoint; converted children are fresh copies.
In particular `Node{Float64}(; op, children=(x32, x32))` is alias-free. -/
def promoted_ctor_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D fuel o : Nat) (kids : List Operand) (n : Addr),
    OperandsOk g D fuel kids → promotedCtor g D fuel o kids = .ok (n, g') → NoAlias g'.view n

theorem promoted_ctor_noalias_ok_holds : promoted_ctor_noalias_ok := by
  intro T g g' D fuel o kids n ⟨ht, hp, hconv⟩ h
  unfold promotedCtor at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  generalize hal : (Heap.alloc g _ : Addr × SGraph T) = p at h
  obtain ⟨n0, g1⟩ := p
  have hn0 : n0 = g.next := by have := congrArg Prod.fst hal; exact this.symm
  have hg1 := congrArg Prod.snd hal
  simp only at hg1
  dsimp only at h
  obtain ⟨⟨cs, g2⟩, hcs, h⟩ := bind_ok h
  obtain ⟨g3, hset, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hnn, hgg⟩ := h
  rw [← hnn, ← hgg, hn0]
  rw [hn0] at hset
  have hext1 : Ext g g1 := by
    rw [← hg1]
    exact ⟨by simp [Heap.alloc], fun x hx => by simp [Heap.alloc, show x ≠ g.next from Nat.ne_of_lt hx]⟩
  have hcell1 : ∃ c1, g1.cells g.next = some c1 ∧ c1.slots = none := by
    rw [← hg1]
    exact ⟨{ (blankCell : SCell T) with degree := kids.length, op := o }, by simp [Heap.alloc], rfl⟩
  have hnext1 : g1.next = g.next + 1 := by rw [← hg1]; rfl
  have hconv1 : ∀ o ∈ kids, o.2 = true → ∃ t : Tree T,
      Graph.unfold (SGraph.view g1) fuel o.1 = some t ∧ t.WF D (fun _ => 255) 65535 := by
    intro o ho hco
    obtain ⟨t, hu, hw⟩ := hconv o ho hco
    exact ⟨t, unfold_ext hext1 fuel o.1 t hu, hw⟩
  have hi := convOperands_inv kids g1 g1 g2 [] [] cs (inv_nil _)
    (by simpa using trees_ext hext1 ht) (by simpa using pairDisj_ext hext1 ht hp) hconv1 hcs
  simp only [List.nil_append] at hi
  have hnot : ∀ b ∈ cs, ∀ x, Reachable g2.view b x → x ≠ g.next := by
    intro b hb x hx hxn
    rcases hi.within b hb x hx with h1 | ⟨a, ha, hax⟩
    · rw [hxn, hnext1] at h1; exact Nat.not_succ_le_self _ h1
    · have hcl := (ht a ha).2
      have hax' := (reach_ext hext1 hcl).mp hax
      have := closed_lt hcl hax'
      rw [hxn] at this
      exact Nat.lt_irrefl _ this
  obtain ⟨c1, hc1, hs1⟩ := hcell1
  obtain ⟨c, hc, hc3, hoff, _⟩ := setChildrenRaw_ok hset
  have hc2 : g2.cells g.next = some c1 := by
    rw [hi.ext.2 g.next (by rw [hnext1]; exact Nat.lt_succ_self _), hc1]
  rw [hc2] at hc
  cases hc
  have hK : kids' g3 g.next = some (((slotsOf D (cs.map some)).take c1.degree).filterMap id) := by
    rw [kids', view_kids, hc3]; rfl
  have hsub : List.Sublist (((slotsOf D (cs.map some)).take c1.degree).filterMap id) cs := by
    have h1 := active_slots_sublist D c1.degree (cs.map some)
    have h2 : ((cs.map some).take c1.degree).filterMap id = cs.take c1.degree := by
      rw [← List.map_take, List.filterMap_map]; exact List.filterMap_some
    rw [h2] at h1
    exact h1.trans (List.take_sublist _ _)
  have hleaf : NoAlias g2.view g.next := by
    apply noAlias_leaf
    intro c' h'
    rw [view_cells, hc2] at h'
    cases h'
    simp [SCell.toCell, SCell.active, hs1]
  exact noAlias_set_kids (view_kids_off hoff) hleaf hK (hsub.nodup hi.disj.1)
    (fun b hb => (hi.trees b (hsub.subset hb)).1)
    (fun b hb hr => hnot b (hsub.subset hb) _ hr rfl) (fun _ _ x _ h => h)
    (fun b hb b' hb' hne => hi.disj.2 b (hsub.subset hb) b' (hsub.subset hb') hne)

example : OperandsOk (oneLeaf : SGraph Nat) 2 1 [(0, true), (0, true)] := by
  refine ⟨by simp [kept, trees_nil], by simp [kept, pairDisj_nil], fun o ho _ => ⟨.feature 1, ?_, ?_⟩⟩
  · simp at ho; rcases ho with rfl | rfl <;> rfl
  · simp [Tree.WF]

/-- The mixed-type operator converter `f(l::Node{T1}, r::Node{T2})`
(`src/OperatorEnumConstruction.jl:211-222`) returns an alias-free tree when
kept operands are alias-free, distinct and disjoint; converted operands are
fresh copies. -/
def promote_binary_noalias_ok : Prop :=
  ∀ (T : Type) (g g' : SGraph T) (D fuel idx : Nat) (f : T → T → T) (l r : Operand) (n : Addr),
    OperandsOk g D fuel [l, r] → promoteBinary g D fuel f idx l r = .ok (n, g') → NoAlias g'.view n

theorem promote_binary_noalias_ok_holds : promote_binary_noalias_ok := by
  intro T g g' D fuel idx f l r n ⟨ht, hp, hconv⟩ h
  unfold promoteBinary at h
  obtain ⟨⟨l', g1⟩, hl, h⟩ := bind_ok h
  obtain ⟨⟨r', g2⟩, hr, h⟩ := bind_ok h
  have hc : convOperands D fuel g [l, r] = .ok ([l', r'], g2) := by
    obtain ⟨a, ca⟩ := l
    obtain ⟨b, cb⟩ := r
    simp only [convOperands, hl, hr, bind, Except.bind, pure, Except.pure]
  have hi := convOperands_inv [l, r] g g g2 [] [] [l', r'] (inv_nil g)
    (by simpa using ht) (by simpa using hp) hconv hc
  simp only [List.nil_append] at hi
  exact (opBinary_built hi.trees hi.disj h).noAlias

/-! ## Registered promotion properties: success from input conditions -/

theorem ext_alloc (g : SGraph T) (c : SCell T) : Ext g (g.alloc c).2 :=
  ⟨by simp [Heap.alloc], fun x hx => by simp [Heap.alloc, show x ≠ g.next from Nat.ne_of_lt hx]⟩

/-- Converting operands succeeds when every converted operand unfolds to a
well-formed tree; one result per operand; only new objects are added. -/
theorem convOperands_exists {D fuel : Nat} (g0 : SGraph T) :
    ∀ (ops : List Operand) (h : SGraph T), Ext g0 h →
      (∀ o ∈ ops, o.2 = true → ∃ t : Tree T, Graph.unfold g0.view fuel o.1 = some t ∧
        t.WF D (fun _ => 255) 65535) →
      ∃ bs h', convOperands D fuel h ops = .ok (bs, h') ∧ bs.length = ops.length ∧ Ext h h' := by
  intro ops
  induction ops with
  | nil => intro h _ _; exact ⟨[], h, rfl, rfl, ext_refl h⟩
  | cons o ops ih =>
    intro h he hconv
    obtain ⟨a, cv⟩ := o
    have hrest : ∀ o ∈ ops, o.2 = true → ∃ t : Tree T, Graph.unfold g0.view fuel o.1 = some t ∧
        t.WF D (fun _ => 255) 65535 := fun o ho hco => hconv o (by simp [ho]) hco
    cases cv with
    | false =>
      obtain ⟨bs, h', hc, hl, he'⟩ := ih h he hrest
      refine ⟨a :: bs, h', ?_, by simp [hl], he'⟩
      simp [convOperands, convertH, bind, Except.bind, hc, pure, Except.pure]
    | true =>
      obtain ⟨t, hu, hw⟩ := hconv (a, true) (by simp) rfl
      obtain ⟨r, h1, hc1, hb1⟩ := copy_built (bs := true) (unfold_ext he fuel a t hu) hw
      obtain ⟨bs, h', hc, hl, he'⟩ := ih h1 (ext_trans he hb1.ext) hrest
      refine ⟨r :: bs, h', ?_, by simp [hl], ext_trans hb1.ext he'⟩
      simp only [convOperands, Bool.not_true, Bool.not_false, convertH, Bool.false_eq_true, ↓reduceIte, hc1,
        bind, Except.bind, hc, pure, Except.pure]

/-- The typed constructor `N{T}(; op, children)` with converted children
(`src/Node.jl:407-428`, `src/Utils.jl:94-96`) with at most `D` children and an
operator index fitting `UInt8` succeeds and returns an alias-free tree when its
kept children are alias-free, distinct and disjoint; converted children (any
finite well-formed tree) are fresh copies. In particular
`Node{Float64}(; op, children=(x32, x32))` is alias-free. -/
def promoted_ctor_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel o : Nat) (kids : List Operand),
    kids.length ≤ D → o ≤ 255 → OperandsOk g D fuel kids →
    ∃ n g', promotedCtor g D fuel o kids = .ok (n, g') ∧ NoAlias g'.view n

theorem promoted_ctor_noalias_holds : promoted_ctor_noalias := by
  intro T g D fuel o kids hlen ho hok
  let c0 : SCell T := { (blankCell : SCell T) with degree := kids.length, op := o }
  have he1 : Ext g (g.alloc c0).2 := ext_alloc g c0
  obtain ⟨cs, g2, hc, hcl, he2⟩ := convOperands_exists (D := D) (fuel := fuel) g kids
    (g.alloc c0).2 he1 hok.2.2
  have hn2 : g2.cells g.next = some c0 := by
    rw [he2.2 g.next (by simp [Heap.alloc])]; simp [Heap.alloc]
  obtain ⟨g3, hset, -⟩ := set_children_holds T g2 D g.next cs c0 hn2 (by omega)
  have hrun : promotedCtor g D fuel o kids = .ok (g.next, g3) := by
    unfold promotedCtor
    have h1 : ¬ kids.length > D := by omega
    have h2 : ¬ o > 255 := by omega
    simp only [h1, h2, ↓reduceIte]
    show (convOperands D fuel (g.alloc c0).2 kids >>= fun p =>
      setChildren p.2 D (g.alloc c0).1 p.1 >>= fun g3 => pure ((g.alloc c0).1, g3)) = _
    rw [hc]
    show (setChildren g2 D g.next cs >>= fun g3 => pure (g.next, g3)) = _
    rw [hset]
    rfl
  exact ⟨g.next, g3, hrun, promoted_ctor_noalias_ok_holds T g g3 D fuel o kids g.next hok hrun⟩

theorem isConstNode_eq {g : SGraph T} {a : Addr} {c : SCell T} (hc : g.cells a = some c) :
    isConstNode g a = .ok (c.degree == 0 && c.constant) := by
  simp [isConstNode, Heap.read, hc, bind, Except.bind, pure, Except.pure]

theorem valNode_eq {g : SGraph T} {a : Addr} {c : SCell T} {v : T} (hc : g.cells a = some c)
    (hv : c.val = some v) : valNode g a = .ok v := by
  simp [valNode, Heap.read, hc, hv, bind, Except.bind, pure, Except.pure]

/-- An existing node whose constant leaf (if it is one) holds a value. -/
def ConstValNode (g : SGraph T) (a : Addr) : Prop :=
  ∃ c, g.cells a = some c ∧ (c.degree = 0 → c.constant = true → c.val.isSome)

theorem opBinary_exists (g : SGraph T) (D : Nat) (f : T → T → T) (idx l r : Nat)
    (hidx : idx ≤ 255) (hD : 2 ≤ D) (hl : ConstValNode g l) (hr : ConstValNode g r) :
    ∃ p, opBinary g D f idx l r = .ok p := by
  obtain ⟨cl, hcl, hvl⟩ := hl
  obtain ⟨cr, hcr, hvr⟩ := hr
  have hop := ctor_op_ok g D false idx [l, r] hidx (by simp; omega)
  unfold opBinary
  rw [isConstNode_eq hcl]
  cases hbl : (cl.degree == 0 && cl.constant)
  · simpa only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte] using hop
  · rw [isConstNode_eq hcr]
    cases hbr : (cr.degree == 0 && cr.constant)
    · simpa only [bind, Except.bind, Bool.false_eq_true, ↓reduceIte] using hop
    · have h1 : cl.degree = 0 ∧ cl.constant = true := by simpa using hbl
      have h2 : cr.degree = 0 ∧ cr.constant = true := by simpa using hbr
      obtain ⟨vl, hvl'⟩ := Option.isSome_iff_exists.mp (hvl h1.1 h1.2)
      obtain ⟨vr, hvr'⟩ := Option.isSome_iff_exists.mp (hvr h2.1 h2.2)
      simp only [bind, Except.bind, ↓reduceIte, valNode_eq hcl hvl', valNode_eq hcr hvr']
      exact ctor_val_ok g D false (f vl vr)

theorem unfold_constValNode {g : SGraph T} {fuel : Nat} {a : Addr} {t : Tree T}
    (hu : Graph.unfold g.view fuel a = some t) : ConstValNode g a := by
  cases fuel with
  | zero => simp [Graph.unfold] at hu
  | succ f =>
    cases hc : g.cells a with
    | none => simp [Graph.unfold, view_cells, hc, bind, Option.bind] at hu
    | some c =>
      refine ⟨c, hc, fun hd hk => ?_⟩
      cases hv : c.val with
      | some v => rfl
      | none =>
        exfalso
        simp [Graph.unfold, view_cells, hc, SCell.toCell, SCell.active, hd, hk, hv, bind,
          Option.bind] at hu

/-- One operand conversion step (`convert` or the object itself). -/
theorem convert_step {D fuel : Nat} {g0 h : SGraph T} (he : Ext g0 h) (a : Addr) (cv : Bool)
    (t : Tree T) (hu : Graph.unfold g0.view fuel a = some t) (hw : t.WF D (fun _ => 255) 65535) :
    ∃ b h', convertH h D (!cv) false false fuel a = .ok (b, h') ∧ Ext h h' ∧
      Graph.unfold h'.view fuel b = some t := by
  cases cv with
  | false => exact ⟨a, h, rfl, ext_refl h, unfold_ext he fuel a t hu⟩
  | true =>
    obtain ⟨r, h1, hc, -, hu1, -⟩ :=
      copy_node_heap_holds T h D fuel a t false true (unfold_ext he fuel a t hu) hw
    obtain ⟨r', h', hc', hb⟩ := copy_built (bs := true) (unfold_ext he fuel a t hu) hw
    rw [hc] at hc'
    cases hc'
    exact ⟨r, h1, by simpa [convertH] using hc, hb.ext, hu1⟩

/-- The mixed-type operator converter `f(l::Node{T1}, r::Node{T2})`
(`src/OperatorEnumConstruction.jl:211-222`) with an operator index fitting
`UInt8`, `D ≥ 2`, and operands that unfold to well-formed finite trees
succeeds and returns an alias-free tree when kept operands are alias-free,
distinct and disjoint; converted operands are fresh copies. -/
def promote_binary_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (D fuel idx : Nat) (f : T → T → T) (l r : Operand),
    idx ≤ 255 → 2 ≤ D →
    (∀ o ∈ [l, r], ∃ t : Tree T, Graph.unfold g.view fuel o.1 = some t ∧ t.WF D (fun _ => 255) 65535) →
    Trees g.view (kept [l, r]) → PairDisj g.view (kept [l, r]) →
    ∃ n g', promoteBinary g D fuel f idx l r = .ok (n, g') ∧ NoAlias g'.view n

theorem promote_binary_noalias_holds : promote_binary_noalias := by
  intro T g D fuel idx f l r hidx hD hall ht hp
  obtain ⟨tl, hul, hwl⟩ := hall l (by simp)
  obtain ⟨tr, hur, hwr⟩ := hall r (by simp)
  obtain ⟨l', g1, hcl, he1, hul'⟩ := convert_step (ext_refl g) l.1 l.2 tl hul hwl
  obtain ⟨r', g2, hcr, he2, hur'⟩ := convert_step he1 r.1 r.2 tr hur hwr
  have hul2 := unfold_ext he2 fuel l' tl hul'
  obtain ⟨⟨n, g'⟩, hb⟩ := opBinary_exists g2 D f idx l' r' hidx hD
    (unfold_constValNode hul2) (unfold_constValNode hur')
  have hrun : promoteBinary g D fuel f idx l r = .ok (n, g') := by
    simp only [promoteBinary, hcl, hcr, bind, Except.bind, hb]
  have hok : OperandsOk g D fuel [l, r] :=
    ⟨ht, hp, fun o ho _ => hall o ho⟩
  exact ⟨n, g', hrun, promote_binary_noalias_ok_holds T g g' D fuel idx f l r n hok hrun⟩

example : ∀ o ∈ ([(0, true), (0, true)] : List Operand), ∃ t : Tree Nat,
    Graph.unfold (oneLeaf : SGraph Nat).view 1 o.1 = some t ∧ t.WF 2 (fun _ => 255) 65535 := by
  intro o ho
  simp at ho
  subst ho
  exact ⟨.feature 1, rfl, by simp [Tree.WF]⟩

end DynExpr.NoAlias
