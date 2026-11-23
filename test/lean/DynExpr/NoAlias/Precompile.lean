import DynExpr.NoAlias.Ctor
import DynExpr.NodeBase.TraverseCopy

/-!
The tree built by the precompile workload `test_functions_on_trees`
(`src/precompile.jl:92-141`), on the NodeBase heap, and the `copy_node` that
consumes it (`src/precompile.jl:127`).
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

/-- One iteration of the loop in `test_functions_on_trees`
(`src/precompile.jl:99-125`) with `nu` unary and `nb` binary operators:
the leaves `x` and `c`, the nodes `a1`..`a8` and the final `tree`, each built
with `Node(T1; ...)`, `Node(i, l)` or `Node(i, l, r)`. -/
def workloadTree (g : SGraph T) (one : T) (nu nb : Nat) : Jl (Addr × SGraph T) := do
  let (x, g) ← ctor g 2 false { feature := some 1 }
  let (c, g) ← ctor g 2 false { val := some one }
  let iu := 1
  let ib := 1
  let (a1, g) ← ctor g 2 false { op := some iu, l := some x }
  let iu := iu % nu + 1
  let (a2, g) ← ctor g 2 false { op := some ib, l := some c, r := some a1 }
  let ib := ib % nb + 1
  let (a3, g) ← ctor g 2 false { op := some ib, l := some x, r := some c }
  let ib := ib % nb + 1
  let (a4, g) ← ctor g 2 false { op := some ib, l := some a3, r := some a2 }
  let ib := ib % nb + 1
  let (a5, g) ← ctor g 2 false { op := some ib, l := some x, r := some x }
  let ib := ib % nb + 1
  let (a6, g) ← ctor g 2 false { op := some iu, l := some a5 }
  let iu := iu % nu + 1
  let (a7, g) ← ctor g 2 false { op := some iu, l := some a6 }
  let iu := iu % nu + 1
  let (a8, g) ← ctor g 2 false { op := some iu, l := some a4 }
  ctor g 2 false { op := some ib, l := some a8, r := some a7 }

/-- The expression `Node(b4, Node(u3, Node(b2, Node(b1, x1, 1), Node(1, 1,
Node(1, x1)))), Node(u2, Node(u1, Node(b3, x1, x1))))` that the loop in
`test_functions_on_trees` (`src/precompile.jl:100-124`) intends to build, with
unary operator indices `u1 u2 u3` and binary operator indices `b1`..`b4`. -/
def workloadShape (one : T) (u1 u2 u3 b1 b2 b3 b4 : Nat) : Tree T :=
  .branch b4
    [.branch u3 [.branch b2 [.branch b1 [.feature 1, .const one],
      .branch 1 [.const one, .branch 1 [.feature 1]]]],
     .branch u2 [.branch u1 [.branch b3 [.feature 1, .feature 1]]]]

/-! ## Unfolding through constructor calls -/

/-- The body of `Graph.unfold` at an existing object with fuel `f + 1`. -/
def preBody (G : Graph T) (f : Nat) (c : Cell T) : Option (Tree T) :=
  if c.children.length ≠ c.degree then none
  else if c.degree = 0 then
    (if c.constant then c.val.bind (fun v => some (.const v)) else some (.feature c.feature))
  else (c.children.mapM (Graph.unfold G f)).bind (fun ts => some (.branch c.op ts))

theorem pre_unfold_succ (G : Graph T) (f : Nat) (a : Addr) :
    Graph.unfold G (f + 1) a = (G.cells a).bind (preBody G f) := rfl

theorem pre_mapM_some {α β : Type} {f h : α → Option β} :
    ∀ {l : List α} {ts : List β}, l.mapM f = some ts →
      (∀ x ∈ l, ∀ t, f x = some t → h x = some t) → l.mapM h = some ts
  | [], ts, hf, _ => by rw [List.mapM_nil] at hf ⊢; exact hf
  | x :: xs, ts, hf, hfh => by
    rw [List.mapM_cons] at hf ⊢
    cases hx : f x with
    | none => simp [hx] at hf
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at hf
      | some ys =>
        simp [hx, hxs] at hf
        rw [hfh x (by simp) y hx, pre_mapM_some hxs (fun z hz => hfh z (by simp [hz]))]
        subst hf
        rfl

theorem pre_body_trans {G G' : Graph T} {f f' : Nat} {c : Cell T} {t : Tree T}
    (hch : ∀ b ∈ c.children, ∀ t, Graph.unfold G f b = some t → Graph.unfold G' f' b = some t)
    (h : preBody G f c = some t) : preBody G' f' c = some t := by
  unfold preBody at h ⊢
  by_cases hlen : c.children.length ≠ c.degree
  · rw [ite_eq_left hlen] at h; cases h
  · rw [ite_eq_right hlen] at h ⊢
    by_cases hd : c.degree = 0
    · rw [ite_eq_left hd] at h ⊢; exact h
    · rw [ite_eq_right hd] at h ⊢
      cases hm : c.children.mapM (Graph.unfold G f) with
      | none => rw [hm] at h; simp at h
      | some ts => rw [hm] at h; rw [pre_mapM_some hm hch]; exact h

/-- More fuel never changes a successful unfolding. -/
theorem pre_unfold_mono {G : Graph T} :
    ∀ {f : Nat} {a : Addr} {t : Tree T}, Graph.unfold G f a = some t → Graph.unfold G (f + 1) a = some t
  | 0, _, _, h => by simp [Graph.unfold] at h
  | f + 1, a, t, h => by
    rw [pre_unfold_succ] at h ⊢
    cases hc : G.cells a with
    | none => rw [hc] at h; simp at h
    | some c => rw [hc] at h; exact pre_body_trans (fun _ _ _ ht => pre_unfold_mono ht) h

theorem pre_unfold_le {G : Graph T} {f f' : Nat} {a : Addr} {t : Tree T} (hf : f ≤ f')
    (h : Graph.unfold G f a = some t) : Graph.unfold G f' a = some t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hf
  induction k with
  | zero => exact h
  | succ k ih => exact pre_unfold_mono (ih (Nat.le_add_right f k))

/-- Adding objects never changes a successful unfolding. -/
theorem pre_unfold_ext {g g' : SGraph T} (he : Ext g g') :
    ∀ {f : Nat} {a : Addr} {t : Tree T},
      Graph.unfold g.view f a = some t → Graph.unfold g'.view f a = some t
  | 0, _, _, h => by simp [Graph.unfold] at h
  | f + 1, a, t, h => by
    rw [pre_unfold_succ] at h ⊢
    cases hc : g.view.cells a with
    | none => rw [hc] at h; simp at h
    | some c =>
      have ha : a < g.next := Nat.lt_of_not_le fun hle => by
        simp [view_cells, g.fresh a hle] at hc
      have hc' : g'.view.cells a = some c := by rw [view_cells, he.2 a ha, ← view_cells]; exact hc
      rw [hc] at h
      rw [hc']
      exact pre_body_trans (fun _ _ _ ht => pre_unfold_ext he ht) h

theorem pre_lift {g h : SGraph T} {f f' : Nat} {a : Addr} {t : Tree T} (he : Ext g h)
    (hf : f ≤ f') (hu : Graph.unfold g.view f a = some t) : Graph.unfold h.view f' a = some t :=
  pre_unfold_ext he (pre_unfold_le hf hu)

theorem pre_body_branch {G : Graph T} {f : Nat} {c : Cell T} {o : Nat} {cs : List Addr}
    {ts : List (Tree T)} (hch : c.children = cs) (hdg : c.degree = cs.length) (hop : c.op = o)
    (hne : cs ≠ []) (hm : cs.mapM (Graph.unfold G f) = some ts) :
    preBody G f c = some (.branch o ts) := by
  unfold preBody
  rw [hch, hdg, hop, ite_eq_right (show ¬ (cs.length ≠ cs.length) from fun h => h rfl),
    ite_eq_right (show ¬ cs.length = 0 from fun h => hne (List.eq_nil_of_length_eq_zero h)), hm] <;> rfl

/-! ## Constructor steps -/

theorem pre_val_step (g : SGraph T) (D : Nat) (hasD : Bool) (v : T) :
    ∃ g', ctor g D hasD { val := some v } = .ok (g.next, g') ∧ Ext g g' ∧
      Graph.unfold g'.view 1 g.next = some (.const v) := by
  obtain ⟨g', h, hgc, hu⟩ := (ctor_nodes_holds T g D hasD).1 v
  exact ⟨g', h, ⟨by have := (ctor_ok h).2.1; omega, hgc⟩, hu⟩

theorem pre_feature_step (g : SGraph T) (D : Nat) (hasD : Bool) (i : Nat) (hi : i ≤ 65535) :
    ∃ g', ctor g D hasD { feature := some i } = .ok (g.next, g') ∧ Ext g g' ∧
      Graph.unfold g'.view 1 g.next = some (.feature i) := by
  obtain ⟨g', h, hgc, hu⟩ := (ctor_nodes_holds T g D hasD).2.1 i hi
  exact ⟨g', h, ⟨by have := (ctor_ok h).2.1; omega, hgc⟩, hu⟩

theorem pre_op_step (g : SGraph T) (D : Nat) (hasD : Bool) (o : Nat) {cs : List Addr}
    {f : Nat} {ts : List (Tree T)} (ho : o ≤ 255) (hlen : cs.length ≤ D) (hne : cs ≠ [])
    (hm : cs.mapM (Graph.unfold g.view f) = some ts) :
    ∃ g', ctor g D hasD { op := some o, children := some cs } = .ok (g.next, g') ∧ Ext g g' ∧
      Graph.unfold g'.view (f + 1) g.next = some (.branch o ts) := by
  obtain ⟨g', hctor, hgc, _, c, hc, hdeg, hop⟩ := (ctor_nodes_holds T g D hasD).2.2.1 o cs ho hlen
  obtain ⟨_, hnext, _, c2, hc2, hact⟩ := ctor_ok hctor
  rw [hc] at hc2
  cases hc2
  have hk : c.active = cs := by
    rcases hact with ⟨hn, _⟩ | hk
    · simp at hn
    · exact hk
  have he : Ext g g' := ⟨by omega, hgc⟩
  refine ⟨g', hctor, he, ?_⟩
  have hcv : g'.view.cells g.next = some c.toCell := by rw [view_cells, hc]; rfl
  rw [pre_unfold_succ, hcv]
  exact pre_body_branch hk hdeg hop hne (pre_mapM_some hm (fun _ _ _ ht => pre_unfold_ext he ht))

theorem pre_un_step (g : SGraph T) (D : Nat) (hasD : Bool) (o : Nat) {a f : Nat} {t : Tree T}
    (ho : o ≤ 255) (hD : 1 ≤ D) (ha : Graph.unfold g.view f a = some t) :
    ∃ g', ctor g D hasD { op := some o, l := some a } = .ok (g.next, g') ∧ Ext g g' ∧
      Graph.unfold g'.view (f + 1) g.next = some (.branch o [t]) := by
  rw [((ctor_nodes_holds T g D hasD).2.2.2 o a a).1]
  exact pre_op_step g D hasD o ho (by simpa using hD) (by simp) (by simp [List.mapM_cons, ha])

theorem pre_bin_step (g : SGraph T) (D : Nat) (hasD : Bool) (o : Nat) {a b f : Nat}
    {ta tb : Tree T} (ho : o ≤ 255) (hD : 2 ≤ D) (ha : Graph.unfold g.view f a = some ta)
    (hb : Graph.unfold g.view f b = some tb) :
    ∃ g', ctor g D hasD { op := some o, l := some a, r := some b } = .ok (g.next, g') ∧
      Ext g g' ∧ Graph.unfold g'.view (f + 1) g.next = some (.branch o [ta, tb]) := by
  rw [((ctor_nodes_holds T g D hasD).2.2.2 o a b).2]
  exact pre_op_step g D hasD o ho (by simpa using hD) (by simp)
    (by simp [List.mapM_cons, ha, hb])

theorem pre_cyc (k n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 255) : 1 ≤ k % n + 1 ∧ k % n + 1 ≤ 255 :=
  ⟨Nat.le_add_left 1 (k % n),
    Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt k (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)) h2)⟩

theorem pre_shape_wf (one : T) {u1 u2 u3 b1 b2 b3 b4 : Nat} (hu1 : 1 ≤ u1 ∧ u1 ≤ 255)
    (hu2 : 1 ≤ u2 ∧ u2 ≤ 255) (hu3 : 1 ≤ u3 ∧ u3 ≤ 255) (hb1 : 1 ≤ b1 ∧ b1 ≤ 255)
    (hb2 : 1 ≤ b2 ∧ b2 ≤ 255) (hb3 : 1 ≤ b3 ∧ b3 ≤ 255) (hb4 : 1 ≤ b4 ∧ b4 ≤ 255) :
    (workloadShape one u1 u2 u3 b1 b2 b3 b4).WF 2 (fun _ => 255) 65535 := by
  simp [workloadShape, Tree.WF] <;> omega

/-! ## Properties -/

/-- For every heap, value and operator counts `1 ≤ nu, nb ≤ 255`, the
precompile workload succeeds and builds the intended expression (operator
indices cycled by `i % n + 1`, `src/precompile.jl:108-124`), and the
`copy_node(tree)` that consumes it (`src/precompile.jl:127`, plain `Node`, so
no identity map) returns an alias-free tree for the same expression. The
preceding `convert(Node{T}, tree)` (`src/precompile.jl:126`) returns its
argument when `T` is the loop's last element type. The workload tree itself
is aliased (`a5 = Node(i_bin, x, x)`, `src/precompile.jl:118`, the
repeated-child constructor behaviour of `node_ctor_repeated_child`); this
shows its only consumer removes the aliasing. -/
def precompile_workload_copy_noalias : Prop :=
  ∀ (T : Type) (g : SGraph T) (one : T) (nu nb : Nat),
    1 ≤ nu → nu ≤ 255 → 1 ≤ nb → nb ≤ 255 →
    ∃ r g', workloadTree g one nu nb = .ok (r, g') ∧
      Graph.unfold g'.view 6 r = some (workloadShape one
        (1 % nu + 1) ((1 % nu + 1) % nu + 1) (((1 % nu + 1) % nu + 1) % nu + 1)
        (1 % nb + 1) ((1 % nb + 1) % nb + 1) (((1 % nb + 1) % nb + 1) % nb + 1)
        ((((1 % nb + 1) % nb + 1) % nb + 1) % nb + 1)) ∧
      ∃ r' h, copyNodeH g' 2 false false 6 r = .ok (r', h) ∧ NoAlias h.view r' ∧
        Graph.unfold h.view 6 r' = some (workloadShape one
          (1 % nu + 1) ((1 % nu + 1) % nu + 1) (((1 % nu + 1) % nu + 1) % nu + 1)
          (1 % nb + 1) ((1 % nb + 1) % nb + 1) (((1 % nb + 1) % nb + 1) % nb + 1)
          ((((1 % nb + 1) % nb + 1) % nb + 1) % nb + 1))

theorem precompile_workload_copy_noalias_holds : precompile_workload_copy_noalias := by
  intro T g one nu nb hnu1 hnu2 hnb1 hnb2
  have cu := fun k => pre_cyc k nu hnu1 hnu2
  have cb := fun k => pre_cyc k nb hnb1 hnb2
  -- x, c
  obtain ⟨g1, h1, _, u1⟩ := pre_feature_step g 2 false 1 (by decide)
  obtain ⟨g2, h2, e2, u2⟩ := pre_val_step g1 2 false one
  -- a1 = Node(1, x)
  obtain ⟨g3, h3, e3, u3⟩ :=
    pre_un_step g2 2 false 1 (by decide) (by decide) (pre_lift e2 (Nat.le_refl 1) u1)
  -- a2 = Node(1, c, a1)
  obtain ⟨g4, h4, e4, u4⟩ := pre_bin_step g3 2 false 1 (by decide) (by decide)
    (pre_lift e3 (by decide : 1 ≤ 2) u2) (pre_lift (ext_refl g3) (Nat.le_refl 2) u3)
  -- a3 = Node(b1, x, c)
  obtain ⟨g5, h5, e5, u5⟩ := pre_bin_step g4 2 false (1 % nb + 1) (cb 1).2 (by decide)
    (pre_lift (ext_trans e2 (ext_trans e3 e4)) (Nat.le_refl 1) u1)
    (pre_lift (ext_trans e3 e4) (Nat.le_refl 1) u2)
  -- a4 = Node(b2, a3, a2)
  obtain ⟨g6, h6, e6, u6⟩ := pre_bin_step g5 2 false ((1 % nb + 1) % nb + 1) (cb _).2 (by decide)
    (pre_lift (ext_refl g5) (by decide : 2 ≤ 3) u5) (pre_lift e5 (Nat.le_refl 3) u4)
  -- a5 = Node(b3, x, x)
  have ux6 := pre_lift (ext_trans e2 (ext_trans e3 (ext_trans e4 (ext_trans e5 e6))))
    (Nat.le_refl 1) u1
  obtain ⟨g7, h7, e7, u7⟩ :=
    pre_bin_step g6 2 false (((1 % nb + 1) % nb + 1) % nb + 1) (cb _).2 (by decide) ux6 ux6
  -- a6 = Node(u1, a5)
  obtain ⟨g8, h8, e8, u8⟩ := pre_un_step g7 2 false (1 % nu + 1) (cu 1).2 (by decide) u7
  -- a7 = Node(u2, a6)
  obtain ⟨g9, h9, e9, u9⟩ := pre_un_step g8 2 false ((1 % nu + 1) % nu + 1) (cu _).2 (by decide) u8
  -- a8 = Node(u3, a4)
  obtain ⟨g10, h10, e10, u10⟩ := pre_un_step g9 2 false (((1 % nu + 1) % nu + 1) % nu + 1)
    (cu _).2 (by decide) (pre_lift (ext_trans e7 (ext_trans e8 e9)) (Nat.le_refl 4) u6)
  -- tree = Node(b4, a8, a7)
  obtain ⟨g11, h11, _, u11⟩ := pre_bin_step g10 2 false
    ((((1 % nb + 1) % nb + 1) % nb + 1) % nb + 1) (cb _).2 (by decide)
    (pre_lift (ext_refl g10) (Nat.le_refl 5) u10) (pre_lift e10 (by decide : 4 ≤ 5) u9)
  have hwf := pre_shape_wf one (cu 1) (cu (1 % nu + 1)) (cu ((1 % nu + 1) % nu + 1)) (cb 1)
    (cb (1 % nb + 1)) (cb ((1 % nb + 1) % nb + 1)) (cb (((1 % nb + 1) % nb + 1) % nb + 1))
  obtain ⟨r', h, hc, _, hu', _, hna, _⟩ :=
    copy_node_heap_holds T g11 2 6 g10.next _ false false u11 hwf
  refine ⟨g10.next, g11, ?_, u11, r', h, hc, hna rfl, hu'⟩
  simp only [workloadTree, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, bind, Except.bind]

example : ∃ nu nb : Nat, 1 ≤ nu ∧ nu ≤ 255 ∧ 1 ≤ nb ∧ nb ≤ 255 := ⟨1, 1, by decide⟩

end DynExpr.NoAlias
