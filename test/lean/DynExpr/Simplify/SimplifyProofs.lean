import DynExpr.Simplify.SimplifyTree

/-!
Proofs of the `simplify_tree!` properties stated in `SimplifyTree.lean`
(src/Simplify.jl:131-149), for graphs that may contain aliased subtrees.

Every write performed by `combine_children!` replaces a node whose current
unfold is a foldable branch with constant children by the folded constant
leaf. Such a write leaves `simplifyPure` of every unfold unchanged, never
changes a subtree that has no foldable branch, and only removes child
references. Hence subtrees already simplified stay simplified while later
siblings (possibly sharing nodes with them) are processed.
-/

namespace DynExpr.Simplify

open DynExpr DynExpr.Graph

variable {T : Type}

/-! ## Monad and list helpers -/

private theorem ok_bind (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

private theorem pure_ok (x : α) : (pure x : Except ε α) = Except.ok x := rfl

private theorem some_bind' (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

private theorem ite_t {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

private theorem ite_f {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

/-- Pointwise relation between two lists of equal length. -/
private def F2 (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ F2 R as bs
  | _, _ => False

private theorem F2_length {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, F2 R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨_, h2⟩ := h
    simp [F2_length h2]
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

private theorem F2_mem {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, F2 R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | [], [], _, _, hy => by simp at hy
  | x :: _, _ :: _, h, y, hy => by
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, by simp, h1⟩
    · obtain ⟨x', hx', hr⟩ := F2_mem h2 y hy
      exact ⟨x', by simp [hx'], hr⟩
  | [], _ :: _, h, _, _ => False.elim h
  | _ :: _, [], h, _, _ => False.elim h

private theorem F2_map_eq {R : α → β → Prop} {k : α → γ} {k' : β → γ}
    (hk : ∀ x y, R x y → k' y = k x) :
    ∀ {xs : List α} {ys : List β}, F2 R xs ys → ys.map k' = xs.map k
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    obtain ⟨h1, h2⟩ := h
    simp [hk _ _ h1, F2_map_eq hk h2]
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

private theorem F2_eq {R : α → α → Prop} :
    ∀ {xs ys : List α}, F2 R xs ys → (∀ x ∈ xs, ∀ y, R x y → y = x) → ys = xs
  | [], [], _, _ => rfl
  | x :: _, _ :: _, h, he => by
    obtain ⟨h1, h2⟩ := h
    rw [he x (by simp) _ h1, F2_eq h2 (fun x' hx' => he x' (by simp [hx']))]
  | [], _ :: _, h, _ => False.elim h
  | _ :: _, [], h, _ => False.elim h

private theorem mapM_cons_some {f : α → Option β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = some ys) :
    ∃ y ys', f x = some y ∧ xs.mapM f = some ys' ∧ ys = y :: ys' := by
  rw [List.mapM_cons] at h
  cases hx : f x with
  | none => simp [hx] at h
  | some y =>
    cases hxs : xs.mapM f with
    | none => simp [hx, hxs] at h
    | some ys' =>
      simp [hx, hxs] at h
      exact ⟨y, ys', rfl, rfl, h.symm⟩

private theorem mapM_nil_some {f : α → Option β} {ys : List β}
    (h : ([] : List α).mapM f = some ys) : ys = [] := by
  cases ys with
  | nil => rfl
  | cons _ _ => simp at h

private theorem mapM_length {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length
  | [], _, h => by rw [mapM_nil_some h]; rfl
  | _ :: _, _, h => by
    obtain ⟨_, _, _, hys, rfl⟩ := mapM_cons_some h
    simp [mapM_length hys]

private theorem mapM_getElem {f : α → Option β} :
    ∀ {xs : List α} {ys : List β} {i : Nat} {x : α}, xs.mapM f = some ys → xs[i]? = some x →
      ∃ y, ys[i]? = some y ∧ f x = some y
  | [], _, _, _, _, hx => by simp at hx
  | _ :: _, _, i, _, h, hx => by
    obtain ⟨y, _, hy, hys, rfl⟩ := mapM_cons_some h
    cases i with
    | zero =>
      simp at hx
      subst hx
      exact ⟨y, rfl, hy⟩
    | succ i =>
      simp at hx
      obtain ⟨z, hz, hfz⟩ := mapM_getElem hys hx
      exact ⟨z, by simpa using hz, hfz⟩

private theorem mapM_mem {f : α → Option β} {xs : List α} {ys : List β} {x : α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ y ∈ ys, f x = some y := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨y, hy, hfy⟩ := mapM_getElem h hi
  exact ⟨y, List.mem_of_getElem? hy, hfy⟩

private theorem mapM_transfer {f : α → Option β} {h : α → Option γ} {R : β → γ → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → ∃ z, h x = some z ∧ R y z) →
      ∃ zs, xs.mapM h = some zs ∧ F2 R ys zs
  | [], _, hm, _ => by
    rw [mapM_nil_some hm]
    exact ⟨[], rfl, trivial⟩
  | x :: xs, _, hm, hr => by
    obtain ⟨y, ys', hy, hys, rfl⟩ := mapM_cons_some hm
    obtain ⟨z, hz, hR⟩ := hr x (by simp) y hy
    obtain ⟨zs, hzs, hF⟩ := mapM_transfer hys (fun x' hx' => hr x' (by simp [hx']))
    exact ⟨z :: zs, by simp [List.mapM_cons, hz, hzs], hR, hF⟩

private theorem mapM_map_of {f h : α → Option β} {k : β → β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → h x = some (k y)) → xs.mapM h = some (ys.map k)
  | [], _, hm, _ => by rw [mapM_nil_some hm]; rfl
  | x :: xs, _, hm, hr => by
    obtain ⟨y, ys', hy, hys, rfl⟩ := mapM_cons_some hm
    have hx := hr x (by simp) y hy
    have hxs := mapM_map_of hys (fun x' hx' => hr x' (by simp [hx']))
    simp [List.mapM_cons, hx, hxs]

private theorem mapM_det {f h : α → Option β} :
    ∀ {xs : List α} {ys zs : List β}, xs.mapM f = some ys → xs.mapM h = some zs →
      (∀ x ∈ xs, ∀ y z, f x = some y → h x = some z → y = z) → ys = zs
  | [], _, _, h1, h2, _ => by rw [mapM_nil_some h1, mapM_nil_some h2]
  | x :: xs, _, _, h1, h2, he => by
    obtain ⟨y, ys', hy, hys, rfl⟩ := mapM_cons_some h1
    obtain ⟨z, zs', hz, hzs, rfl⟩ := mapM_cons_some h2
    rw [he x (by simp) y z hy hz,
      mapM_det hys hzs (fun x' hx' => he x' (by simp [hx']))]

private theorem map_eq_self {f : α → α} :
    ∀ xs : List α, (∀ x ∈ xs, f x = x) → xs.map f = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp [h x (by simp), map_eq_self xs (fun y hy => h y (by simp [hy]))]

private theorem mapM_map_congr {f : β → Option γ} {g : α → Option γ} {k : α → β} :
    ∀ xs : List α, (∀ x ∈ xs, f (k x) = g x) → (xs.map k).mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.mapM_cons, h x (by simp),
      mapM_map_congr xs (fun y hy => h y (by simp [hy]))]

private theorem foldr_max_map_le {k : α → α} {d : α → Nat} :
    ∀ xs : List α, (∀ x ∈ xs, d (k x) ≤ d x) →
      ((xs.map k).map d).foldr max 0 ≤ (xs.map d).foldr max 0
  | [], _ => Nat.le_refl _
  | x :: xs, h => by
    simp only [List.map_cons, List.foldr_cons]
    exact Nat.max_le.2 ⟨Nat.le_trans (h x (by simp)) (Nat.le_max_left _ _),
      Nat.le_trans (foldr_max_map_le xs (fun y hy => h y (by simp [hy])))
        (Nat.le_max_right _ _)⟩

/-! ## Pure specification lemmas -/

section Pure

variable [JlValue T]

/-- One bottom-up folding step on already simplified children. -/
private def node (o : OpEnum T) (op : Nat) (ss : List (Tree T)) : Tree T :=
  match foldValue o op ss with
  | some v => .const v
  | none => .branch op ss

private theorem node_some {o : OpEnum T} {op : Nat} {ss : List (Tree T)} {v : T}
    (h : foldValue o op ss = some v) : node o op ss = .const v := by
  simp [node, h]

private theorem node_none {o : OpEnum T} {op : Nat} {ss : List (Tree T)}
    (h : foldValue o op ss = none) : node o op ss = .branch op ss := by
  simp [node, h]

private theorem forest_eq_map (o : OpEnum T) :
    ∀ cs : List (Tree T), simplifyForestPure o cs = cs.map (simplifyPure o)
  | [] => by simp [simplifyForestPure]
  | c :: cs => by simp [simplifyForestPure, forest_eq_map o cs]

private theorem simplifyPure_const (o : OpEnum T) (v : T) :
    simplifyPure o (.const v) = .const v := by simp [simplifyPure]

private theorem simplifyPure_feature (o : OpEnum T) (i : Nat) :
    simplifyPure o (.feature i : Tree T) = .feature i := by simp [simplifyPure]

private theorem simplifyPure_branch (o : OpEnum T) (op : Nat) (cs : List (Tree T)) :
    simplifyPure o (.branch op cs) = node o op (cs.map (simplifyPure o)) := by
  simp only [simplifyPure, forest_eq_map]
  rfl

private theorem hasFoldable_branch (o : OpEnum T) (op : Nat) (cs : List (Tree T)) :
    HasFoldable o (.branch op cs) ↔ (foldValue o op cs).isSome ∨ ∃ c ∈ cs, HasFoldable o c := by
  have hf : ∀ cs : List (Tree T), HasFoldableForest o cs ↔ ∃ c ∈ cs, HasFoldable o c := by
    intro cs
    induction cs with
    | nil => simp [HasFoldableForest]
    | cons c cs ih => simp [HasFoldableForest, ih]
  simp only [HasFoldable, hf]

omit [JlValue T] in
private theorem hasConst_branch (v : T) (op : Nat) (cs : List (Tree T)) :
    HasConst v (.branch op cs) ↔ ∃ c ∈ cs, HasConst v c := by
  have hf : ∀ cs : List (Tree T), HasConstForest v cs ↔ ∃ c ∈ cs, HasConst v c := by
    intro cs
    induction cs with
    | nil => simp [HasConstForest]
    | cons c cs ih => simp [HasConstForest, ih]
  simp only [HasConst, hf]

private theorem foldValue_none_of {o : OpEnum T} {op : Nat} {cs : List (Tree T)}
    (hv : cs.mapM leafVal? = none) : foldValue o op cs = none := by
  unfold foldValue
  rw [hv]
  rfl

private theorem foldValue_of {o : OpEnum T} {op : Nat} {cs : List (Tree T)} {vals : List T}
    (hv : cs.mapM leafVal? = some vals) :
    foldValue o op cs =
      if vals.all JlValue.valid = true then
        (o.lookup cs.length op).bind fun f =>
          if JlValue.valid (f vals) = true then some (f vals) else none
      else none := by
  unfold foldValue
  rw [hv]
  simp only [some_bind']
  cases vals.all JlValue.valid <;> cases o.lookup cs.length op <;> rfl

private theorem foldValue_some {o : OpEnum T} {op : Nat} {cs : List (Tree T)} {out : T}
    (h : foldValue o op cs = some out) :
    ∃ vals f, cs.mapM leafVal? = some vals ∧ vals.all JlValue.valid = true ∧
      o.lookup cs.length op = some f ∧ f vals = out ∧ JlValue.valid out = true := by
  cases hv : cs.mapM leafVal? with
  | none => rw [foldValue_none_of hv] at h; cases h
  | some vals =>
    rw [foldValue_of hv] at h
    cases hval : vals.all JlValue.valid
    · rw [hval] at h; cases h
    · rw [hval, ite_t rfl] at h
      cases hf : o.lookup cs.length op with
      | none => rw [hf] at h; cases h
      | some f =>
        rw [hf] at h
        change (if JlValue.valid (f vals) = true then some (f vals) else none) = some out at h
        by_cases ho : JlValue.valid (f vals) = true
        · rw [ite_t ho] at h
          cases h
          exact ⟨vals, f, rfl, hval, rfl, rfl, ho⟩
        · rw [ite_f ho] at h
          cases h

omit [JlValue T] in
private theorem leafVal_eq {t : Tree T} {v : T} (h : leafVal? t = some v) : t = .const v := by
  cases t with
  | const w =>
    simp [leafVal?] at h
    rw [h]
  | feature i => simp [leafVal?] at h
  | branch op cs => simp [leafVal?] at h

omit [JlValue T] in
private theorem mapM_leafVal_const :
    ∀ {ts : List (Tree T)} {vals : List T}, ts.mapM leafVal? = some vals → ts = vals.map .const
  | [], _, h => by rw [mapM_nil_some h]; rfl
  | _ :: _, _, h => by
    obtain ⟨v, vs, hv, hvs, rfl⟩ := mapM_cons_some h
    rw [leafVal_eq hv, mapM_leafVal_const hvs]
    rfl

private theorem map_simplifyPure_consts (o : OpEnum T) :
    ∀ vals : List T, (vals.map Tree.const).map (simplifyPure o) = vals.map Tree.const
  | [] => rfl
  | v :: vs => by simp [simplifyPure_const, map_simplifyPure_consts o vs]

private theorem simplifyPure_fold {o : OpEnum T} {op : Nat} {cs : List (Tree T)} {out : T}
    (h : foldValue o op cs = some out) : simplifyPure o (.branch op cs) = .const out := by
  obtain ⟨vals, _, hv, -⟩ := foldValue_some h
  have hmap : cs.map (simplifyPure o) = cs := by
    rw [mapM_leafVal_const hv, map_simplifyPure_consts]
  rw [simplifyPure_branch, hmap, node_some h]

omit [JlValue T] in
private theorem mapM_denote_consts (o : OpEnum T) (x : Nat → Option T) :
    ∀ vals : List T, (vals.map Tree.const).mapM (Tree.denote o x) = some vals
  | [] => rfl
  | v :: vs => by simp [List.mapM_cons, Tree.denote, mapM_denote_consts o x vs]

private theorem denote_simplifyPure (o : OpEnum T) (x : Nat → Option T) (t : Tree T) :
    (simplifyPure o t).denote o x = t.denote o x := by
  induction t using Tree.induction with
  | hc v => rw [simplifyPure_const]
  | hf i => rw [simplifyPure_feature]
  | hb op cs ih =>
    have hmap : (cs.map (simplifyPure o)).mapM (Tree.denote o x) = cs.mapM (Tree.denote o x) :=
      mapM_map_congr cs (fun c hc => ih c hc)
    rw [simplifyPure_branch]
    cases hfv : foldValue o op (cs.map (simplifyPure o)) with
    | none =>
      rw [node_none hfv]
      simp only [Tree.denote, List.length_map, hmap]
    | some out =>
      rw [node_some hfv]
      obtain ⟨vals, f, hv, -, hf, rfl, -⟩ := foldValue_some hfv
      rw [mapM_leafVal_const hv, mapM_denote_consts] at hmap
      rw [List.length_map] at hf
      simp [Tree.denote, hf, ← hmap]

private theorem wf_simplifyPure (o : OpEnum T) {D nf : Nat} (t : Tree T) :
    t.WF D o.nops nf → (simplifyPure o t).WF D o.nops nf := by
  induction t using Tree.induction with
  | hc v => intro h; rw [simplifyPure_const]; exact h
  | hf i => intro h; rw [simplifyPure_feature]; exact h
  | hb op cs ih =>
    intro h
    rw [simplifyPure_branch]
    cases hfv : foldValue o op (cs.map (simplifyPure o)) with
    | some v => rw [node_some hfv]; simp [Tree.WF]
    | none =>
      rw [node_none hfv]
      simp only [Tree.WF, List.length_map] at h ⊢
      refine ⟨h.1, h.2.1, fun c hc => ?_⟩
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      exact ih c0 hc0 (h.2.2 c0 hc0)

private theorem depth_simplifyPure (o : OpEnum T) (t : Tree T) :
    (simplifyPure o t).depth ≤ t.depth := by
  induction t using Tree.induction with
  | hc v => rw [simplifyPure_const]; exact Nat.le_refl _
  | hf i => rw [simplifyPure_feature]; exact Nat.le_refl _
  | hb op cs ih =>
    rw [simplifyPure_branch]
    cases hfv : foldValue o op (cs.map (simplifyPure o)) with
    | some v =>
      rw [node_some hfv]
      simp only [Tree.depth]
      omega
    | none =>
      rw [node_none hfv]
      simp only [Tree.depth]
      have := foldr_max_map_le (k := simplifyPure o) (d := Tree.depth) cs ih
      omega

private theorem not_hasFoldable_simplifyPure (o : OpEnum T) (t : Tree T) :
    ¬ HasFoldable o (simplifyPure o t) := by
  induction t using Tree.induction with
  | hc v => rw [simplifyPure_const]; simp [HasFoldable]
  | hf i => rw [simplifyPure_feature]; simp [HasFoldable]
  | hb op cs ih =>
    rw [simplifyPure_branch]
    cases hfv : foldValue o op (cs.map (simplifyPure o)) with
    | some v => rw [node_some hfv]; simp [HasFoldable]
    | none =>
      rw [node_none hfv, hasFoldable_branch]
      rintro (h | ⟨c, hc, h⟩)
      · simp [hfv] at h
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
        exact ih c0 hc0 h

private theorem simplifyPure_of_nf (o : OpEnum T) (t : Tree T) :
    ¬ HasFoldable o t → simplifyPure o t = t := by
  induction t using Tree.induction with
  | hc v => intro _; rw [simplifyPure_const]
  | hf i => intro _; rw [simplifyPure_feature]
  | hb op cs ih =>
    intro hn
    rw [hasFoldable_branch] at hn
    have hmap : cs.map (simplifyPure o) = cs :=
      map_eq_self cs (fun c hc => ih c hc (fun h => hn (Or.inr ⟨c, hc, h⟩)))
    have hfv : foldValue o op cs = none := by
      cases h : foldValue o op cs with
      | none => rfl
      | some v => exact absurd (Or.inl (by simp [h])) hn
    rw [simplifyPure_branch, hmap, node_none hfv]

private theorem simplifyPure_idem (o : OpEnum T) (t : Tree T) :
    simplifyPure o (simplifyPure o t) = simplifyPure o t :=
  simplifyPure_of_nf o _ (not_hasFoldable_simplifyPure o t)

private theorem hasConst_simplifyPure (o : OpEnum T) (t : Tree T) :
    ∀ v, HasConst v (simplifyPure o t) → JlValue.valid v = true ∨ HasConst v t := by
  induction t using Tree.induction with
  | hc w => intro v h; rw [simplifyPure_const] at h; exact Or.inr h
  | hf i => intro v h; rw [simplifyPure_feature] at h; exact Or.inr h
  | hb op cs ih =>
    intro v h
    rw [simplifyPure_branch] at h
    cases hfv : foldValue o op (cs.map (simplifyPure o)) with
    | some out =>
      rw [node_some hfv] at h
      obtain ⟨_, _, _, _, _, _, hvalid⟩ := foldValue_some hfv
      simp only [HasConst] at h
      subst h
      exact Or.inl hvalid
    | none =>
      rw [node_none hfv, hasConst_branch] at h
      obtain ⟨c, hc, h⟩ := h
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
      rcases ih c0 hc0 v h with hv | hv
      · exact Or.inl hv
      · exact Or.inr ((hasConst_branch v op cs).2 ⟨c0, hc0, hv⟩)

end Pure

/-! ## Unfolding the heap -/

private theorem unfold_cell {g : Graph T} {a : Addr} {c : Cell T} (n : Nat)
    (hc : g.cells a = some c) :
    g.unfold (n + 1) a =
      (if c.children.length ≠ c.degree then none
      else if c.degree = 0 then
        if c.constant then (do return .const (← c.val))
        else some (.feature c.feature)
      else (do return .branch c.op (← c.children.mapM (g.unfold n)))) := by
  first
    | (simp only [unfold, hc]; rfl)
    | (rw [unfold, hc]; rfl)
    | simp [unfold, hc]

private theorem unfold_inv {g : Graph T} {n : Nat} {a : Addr} {u : Tree T}
    (h : g.unfold (n + 1) a = some u) :
    ∃ c, g.cells a = some c ∧ c.children.length = c.degree ∧
      ((c.degree = 0 ∧ c.constant = true ∧ ∃ v, c.val = some v ∧ u = .const v) ∨
       (c.degree = 0 ∧ c.constant = false ∧ u = .feature c.feature) ∨
       (c.degree ≠ 0 ∧ ∃ us, c.children.mapM (g.unfold n) = some us ∧
          u = .branch c.op us)) := by
  cases hc : g.cells a with
  | none => simp [unfold, hc] at h
  | some c =>
    rw [unfold_cell n hc] at h
    refine ⟨c, rfl, ?_⟩
    split at h
    · cases h
    · rename_i hl
      refine ⟨by simpa using hl, ?_⟩
      split at h
      · rename_i hd
        split at h
        · rename_i hk
          left
          cases hv : c.val with
          | none => simp [hv] at h
          | some v =>
            simp [hv] at h
            subst h
            exact ⟨hd, hk, v, rfl, rfl⟩
        · rename_i hk
          right; left
          simp at h
          subst h
          exact ⟨hd, by simpa using hk, rfl⟩
      · rename_i hd
        right; right
        cases hm : c.children.mapM (g.unfold n) with
        | none => simp [hm] at h
        | some us =>
          simp [hm] at h
          subst h
          exact ⟨hd, us, rfl, rfl⟩

private theorem unfold_const {g : Graph T} {a : Addr} {c : Cell T} {v : T} (n : Nat)
    (hc : g.cells a = some c) (hd : c.degree = 0) (hch : c.children = [])
    (hk : c.constant = true) (hv : c.val = some v) :
    g.unfold (n + 1) a = some (.const v) := by
  rw [unfold_cell n hc]
  simp [hd, hch, hk, hv]

private theorem unfold_feature {g : Graph T} {a : Addr} {c : Cell T} (n : Nat)
    (hc : g.cells a = some c) (hd : c.degree = 0) (hch : c.children = [])
    (hk : c.constant = false) :
    g.unfold (n + 1) a = some (.feature c.feature) := by
  rw [unfold_cell n hc]
  simp [hd, hch, hk]

private theorem unfold_branch {g : Graph T} {a : Addr} {c : Cell T} {us : List (Tree T)}
    (n : Nat) (hc : g.cells a = some c) (hl : c.children.length = c.degree)
    (hd : c.degree ≠ 0) (hm : c.children.mapM (g.unfold n) = some us) :
    g.unfold (n + 1) a = some (.branch c.op us) := by
  rw [unfold_cell n hc]
  simp [hl, hd, hm]

private theorem unfold_det {g : Graph T} :
    ∀ {n m : Nat} {a : Addr} {u v : Tree T},
      g.unfold n a = some u → g.unfold m a = some v → u = v
  | 0, _, _, _, _, h, _ => by simp [unfold] at h
  | _ + 1, 0, _, _, _, _, h => by simp [unfold] at h
  | n + 1, m + 1, a, u, v, hu, hv => by
    obtain ⟨c, hc, _, hu'⟩ := unfold_inv hu
    obtain ⟨c', hc', _, hv'⟩ := unfold_inv hv
    rw [hc] at hc'
    cases hc'
    rcases hu' with ⟨hd, hk, w, hw, rfl⟩ | ⟨hd, hk, rfl⟩ | ⟨hd, us, hus, rfl⟩
    · rcases hv' with ⟨_, _, w', hw', rfl⟩ | ⟨_, hk', _⟩ | ⟨hd', _⟩
      · rw [hw] at hw'
        cases hw'
        rfl
      · rw [hk] at hk'
        cases hk'
      · exact absurd hd hd'
    · rcases hv' with ⟨_, hk', _⟩ | ⟨_, _, rfl⟩ | ⟨hd', _⟩
      · rw [hk] at hk'
        cases hk'
      · rfl
      · exact absurd hd hd'
    · rcases hv' with ⟨hd', _⟩ | ⟨hd', _⟩ | ⟨_, vs, hvs, rfl⟩
      · exact absurd hd' hd
      · exact absurd hd' hd
      · rw [mapM_det hus hvs (fun x _ y z hy hz => unfold_det hy hz)]

private theorem path_lt {g : Graph T} {x y : Addr} {q : List Nat} (hp : Path g x q y) :
    ∀ {n : Nat} {u : Tree T}, g.unfold n x = some u → q.length < n := by
  induction hp with
  | nil a =>
    intro n u h
    cases n with
    | zero => simp [unfold] at h
    | succ n => simp
  | cons hc hi _ ih =>
    intro n u h
    cases n with
    | zero => simp [unfold] at h
    | succ n =>
      obtain ⟨c', hc', hl, hu⟩ := unfold_inv h
      rw [hc] at hc'
      cases hc'
      rcases hu with ⟨hd, -⟩ | ⟨hd, -⟩ | ⟨-, us, hus, -⟩
      · have : _ = [] := List.eq_nil_of_length_eq_zero (hl.trans hd)
        simp [this] at hi
      · have : _ = [] := List.eq_nil_of_length_eq_zero (hl.trans hd)
        simp [this] at hi
      · obtain ⟨y, -, hy⟩ := mapM_getElem hus hi
        have := ih hy
        simp
        omega

private theorem path_rep {g : Graph T} {a : Addr} {q : List Nat} (hq : Path g a q a) :
    ∀ k : Nat, ∃ r, Path g a r a ∧ r.length = k * q.length
  | 0 => ⟨[], Path.nil a, by simp⟩
  | k + 1 => by
    obtain ⟨r, hr, hl⟩ := path_rep hq k
    refine ⟨q ++ r, hq.append hr, ?_⟩
    rw [List.length_append, hl, Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem no_cycle {g : Graph T} {a : Addr} {n : Nat} {u : Tree T}
    (h : g.unfold n a = some u) {q : List Nat} (hq : Path g a q a) : q = [] := by
  cases q with
  | nil => rfl
  | cons i q' =>
    obtain ⟨r, hr, hl⟩ := path_rep hq n
    have h1 := path_lt hr h
    have h2 : n ≤ n * (i :: q').length := Nat.le_mul_of_pos_right n (by simp)
    rw [hl] at h1
    exact absurd (Nat.lt_of_le_of_lt h2 h1) (Nat.lt_irrefl _)

private theorem child_index {c : Cell T} {ch : Addr} (h : ch ∈ c.children) :
    ∃ i : Nat, c.children[i]? = some ch :=
  List.mem_iff_getElem?.1 h

private theorem child_not_reach {g : Graph T} {a ch : Addr} {c : Cell T} {n : Nat}
    {u : Tree T} (hu : g.unfold n a = some u) (hc : g.cells a = some c)
    (hch : ch ∈ c.children) : ¬ Reachable g ch a := by
  rintro ⟨q, hq⟩
  obtain ⟨i, hi⟩ := child_index hch
  have := no_cycle hu (Path.cons hc hi hq)
  cases this

private theorem reach_child {g : Graph T} {a ch b : Addr} {c : Cell T}
    (hc : g.cells a = some c) (hch : ch ∈ c.children) (h : Reachable g ch b) :
    Reachable g a b := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨i, hi⟩ := child_index hch
  exact ⟨i :: q, Path.cons hc hi hq⟩

/-! ## Heap invariants -/

section Heap

variable [JlValue T]

/-- `u'` is obtained from `u` by folding some constant-children branches. -/
private def Q (o : OpEnum T) (u u' : Tree T) : Prop :=
  simplifyPure o u' = simplifyPure o u ∧ (¬ HasFoldable o u → u' = u) ∧
    ∀ D nf, u.WF D o.nops nf → u'.WF D o.nops nf

/-- Every successful unfold of `g` is related by `Q` to the unfold of `g'`. -/
private def Pres (o : OpEnum T) (g g' : Graph T) : Prop :=
  ∀ n b u, g.unfold n b = some u → ∃ u', g'.unfold n b = some u' ∧ Q o u u'

/-- Every child path of `g'` is a child path of `g`. -/
private def PathsBack (g g' : Graph T) : Prop :=
  ∀ x q y, Path g' x q y → Path g x q y

/-- Cells unreachable from `a` are unchanged. -/
private def Frame (g g' : Graph T) (a : Addr) : Prop :=
  ∀ b, ¬ Reachable g a b → g'.cells b = g.cells b

private theorem Q_refl (o : OpEnum T) (u : Tree T) : Q o u u :=
  ⟨rfl, fun _ => rfl, fun _ _ h => h⟩

private theorem Q_trans {o : OpEnum T} {u v w : Tree T} (h1 : Q o u v) (h2 : Q o v w) :
    Q o u w :=
  ⟨h2.1.trans h1.1,
    fun hn => by rw [h2.2.1 (by rw [h1.2.1 hn]; exact hn), h1.2.1 hn],
    fun D nf h => h2.2.2 D nf (h1.2.2 D nf h)⟩

private theorem Q_branch {o : OpEnum T} {op : Nat} {us us' : List (Tree T)}
    (hF : F2 (Q o) us us') : Q o (.branch op us) (.branch op us') := by
  have hmap : us'.map (simplifyPure o) = us.map (simplifyPure o) :=
    F2_map_eq (fun _ _ h => h.1) hF
  refine ⟨?_, ?_, ?_⟩
  · rw [simplifyPure_branch, simplifyPure_branch, hmap]
  · intro hn
    rw [hasFoldable_branch] at hn
    rw [F2_eq hF (fun x hx y hxy => hxy.2.1 (fun h => hn (Or.inr ⟨x, hx, h⟩)))]
  · intro D nf hw
    simp only [Tree.WF] at hw ⊢
    have hlen := F2_length hF
    refine ⟨by rw [← hlen]; exact hw.1, by rw [← hlen]; exact hw.2.1, fun c hc => ?_⟩
    obtain ⟨x, hx, hq⟩ := F2_mem hF c hc
    exact hq.2.2 D nf (hw.2.2 x hx)

private theorem Pres_refl (o : OpEnum T) (g : Graph T) : Pres o g g :=
  fun _ _ u h => ⟨u, h, Q_refl o u⟩

private theorem Pres_trans {o : OpEnum T} {g h k : Graph T} (h1 : Pres o g h)
    (h2 : Pres o h k) : Pres o g k := by
  intro n b u hu
  obtain ⟨v, hv, q1⟩ := h1 n b u hu
  obtain ⟨w, hw, q2⟩ := h2 n b v hv
  exact ⟨w, hw, Q_trans q1 q2⟩

omit [JlValue T] in
private theorem write_ok (G : Graph T) (p : Addr) (c v : Cell T) (hc : G.cells p = some c) :
    ∃ G', G.write p v = .ok G' ∧ ∀ b, G'.cells b = if b = p then some v else G.cells b := by
  unfold Heap.write
  split
  · rename_i h
    rw [hc] at h
    cases h
  · exact ⟨_, rfl, fun _ => rfl⟩

/-- Replacing a foldable constant-children branch by its folded leaf. -/
private theorem write_pres (o : OpEnum T) {G G' : Graph T} {p : Addr} {N op : Nat}
    {us : List (Tree T)} {out : T} {v : Cell T}
    (hG : G.unfold N p = some (.branch op us)) (hf : foldValue o op us = some out)
    (hv : v.degree = 0 ∧ v.constant = true ∧ v.val = some out ∧ v.children = [])
    (hG' : ∀ b, G'.cells b = if b = p then some v else G.cells b) : Pres o G G' := by
  intro n
  induction n with
  | zero => intro b u h; simp [unfold] at h
  | succ n ih =>
    intro b u h
    by_cases hb : b = p
    · subst hb
      have hu : u = .branch op us := unfold_det h hG
      subst hu
      have hcell : G'.cells b = some v := by rw [hG']; simp
      refine ⟨.const out, unfold_const n hcell hv.1 hv.2.2.2 hv.2.1 hv.2.2.1, ?_, ?_, ?_⟩
      · rw [simplifyPure_fold hf, simplifyPure_const]
      · intro hn
        exact absurd ((hasFoldable_branch o op us).2 (Or.inl (by simp [hf]))) hn
      · intro D nf _
        simp [Tree.WF]
    · obtain ⟨c, hc, hl, hu⟩ := unfold_inv h
      have hc' : G'.cells b = some c := by rw [hG']; simp [hb, hc]
      rcases hu with ⟨hd, hk, w, hw, rfl⟩ | ⟨hd, hk, rfl⟩ | ⟨hd, us', hus, rfl⟩
      · exact ⟨_, unfold_const n hc' hd (List.eq_nil_of_length_eq_zero (hl.trans hd)) hk hw,
          Q_refl o _⟩
      · exact ⟨_, unfold_feature n hc' hd (List.eq_nil_of_length_eq_zero (hl.trans hd)) hk,
          Q_refl o _⟩
      · obtain ⟨zs, hzs, hF⟩ := mapM_transfer hus (fun x _ y hy => ih x y hy)
        exact ⟨_, unfold_branch n hc' hl hd hzs, Q_branch hF⟩

omit [JlValue T] in
private theorem write_pathsBack {G G' : Graph T} {p : Addr} {v : Cell T}
    (hv : v.children = [])
    (hG' : ∀ b, G'.cells b = if b = p then some v else G.cells b) : PathsBack G G' := by
  intro x q y hp
  induction hp with
  | nil a => exact Path.nil a
  | @cons a b z i r c hc hi _ ih =>
    rw [hG'] at hc
    by_cases ha : a = p
    · simp [ha] at hc
      subst hc
      simp [hv] at hi
    · simp [ha] at hc
      exact Path.cons hc hi ih

/-! ## `combine_children!` -/

omit [JlValue T] in
private theorem elem_cell {G : Graph T} {m : Nat} {r : Addr} {s : Tree T}
    (h : G.unfold (m + 1) r = some s) :
    ∃ cell, G.cells r = some cell ∧ cellConst cell = (leafVal? s).isSome ∧
      ∀ v, leafVal? s = some v → cell.val = some v := by
  obtain ⟨c, hc, _, hs⟩ := unfold_inv h
  refine ⟨c, hc, ?_⟩
  rcases hs with ⟨hd, hk, w, hw, rfl⟩ | ⟨hd, hk, rfl⟩ | ⟨hd, us, _, rfl⟩
  · simp [cellConst, leafVal?, hd, hk, hw]
  · simp [cellConst, leafVal?, hd, hk]
  · simp [cellConst, leafVal?, hd]

omit [JlValue T] in
private theorem children_cells (G : Graph T) (m : Nat) :
    ∀ (rs : List Addr) (ss : List (Tree T)), rs.mapM (G.unfold (m + 1)) = some ss →
      ∃ cells, rs.mapM G.read = .ok cells ∧ cells.all cellConst = (ss.mapM leafVal?).isSome ∧
        ∀ vals, ss.mapM leafVal? = some vals → rs.mapM (valOf G) = .ok vals
  | [], ss, h => by
    rw [mapM_nil_some h]
    refine ⟨[], rfl, rfl, fun vals hv => ?_⟩
    rw [mapM_nil_some hv]
    rfl
  | r :: rs, ss, h => by
    obtain ⟨s, ss', hs, hss, rfl⟩ := mapM_cons_some h
    obtain ⟨cell, hcell, hconst, hval⟩ := elem_cell hs
    obtain ⟨cells, hcells, hall, hvals⟩ := children_cells G m rs ss' hss
    refine ⟨cell :: cells, ?_, ?_, ?_⟩
    · simp [List.mapM_cons, Heap.read, hcell, hcells, ok_bind, pure_ok]
    · rw [List.all_cons, hconst, hall]
      cases h1 : leafVal? s <;> cases h2 : ss'.mapM leafVal? <;> simp [List.mapM_cons, h1, h2]
    · intro vals hv
      obtain ⟨v, vs, hv1, hvs, rfl⟩ := mapM_cons_some hv
      simp [List.mapM_cons, valOf, Heap.read, hcell, hval v hv1, hvals vs hvs, ok_bind,
        pure_ok]

private theorem combine_ok (o : OpEnum T) {G : Graph T} {a : Addr} {c : Cell T} {m : Nat}
    {ss : List (Tree T)} (hc : G.cells a = some c) (hl : c.children.length = c.degree)
    (hd : c.degree ≠ 0) (hss : c.children.mapM (G.unfold (m + 1)) = some ss)
    (hop : ∃ f, o.lookup c.children.length c.op = some f) :
    ∃ G', combineChildren o G a c.children = .ok G' ∧
      G'.unfold (m + 2) a = some (node o c.op ss) ∧ Pres o G G' ∧ PathsBack G G' ∧
      ∀ b, b ≠ a → G'.cells b = G.cells b := by
  obtain ⟨cells, hcells, hall, hvals⟩ := children_cells G m c.children ss hss
  have hunf : G.unfold (m + 2) a = some (.branch c.op ss) := unfold_branch (m + 1) hc hl hd hss
  have hlen : ss.length = c.children.length := mapM_length hss
  obtain ⟨f, hf⟩ := hop
  have hread : G.read a = .ok c := by simp [Heap.read, hc]
  have keep : combineChildren o G a c.children = .ok G → foldValue o c.op ss = none →
      ∃ G', combineChildren o G a c.children = .ok G' ∧
        G'.unfold (m + 2) a = some (node o c.op ss) ∧ Pres o G G' ∧ PathsBack G G' ∧
        ∀ b, b ≠ a → G'.cells b = G.cells b := fun h1 h2 =>
    ⟨G, h1, by rw [node_none h2]; exact hunf, Pres_refl o G, fun _ _ _ h => h, fun _ _ => rfl⟩
  cases hv : ss.mapM leafVal? with
  | none =>
    have hallF : cells.all cellConst = false := by rw [hall, hv]; rfl
    apply keep
    · unfold combineChildren
      simp only [hcells, ok_bind, hallF] <;> rfl
    · exact foldValue_none_of hv
  | some vals =>
    have hallT : cells.all cellConst = true := by rw [hall, hv]; rfl
    have hvals' := hvals vals hv
    by_cases hval : vals.all JlValue.valid = true
    · by_cases hout : JlValue.valid (f vals) = true
      · obtain ⟨G', hw, hG'⟩ := write_ok G a c
          { c with degree := 0, constant := true, val := some (f vals), children := [] } hc
        have hfold : foldValue o c.op ss = some (f vals) := by
          rw [foldValue_of hv, hval, ite_t rfl, hlen, hf]
          exact ite_t hout _ _
        have hcell : G'.cells a =
            some { c with degree := 0, constant := true, val := some (f vals), children := [] } := by
          rw [hG']; simp
        refine ⟨G', ?_, ?_, write_pres o hunf hfold ⟨rfl, rfl, rfl, rfl⟩ hG',
          write_pathsBack rfl hG', fun b hb => by rw [hG']; simp [hb]⟩
        · unfold combineChildren
          simp only [hcells, ok_bind, hallT, hvals', hval, hread, hf, pure_bind, hout, hw] <;> rfl
        · rw [node_some hfold]
          exact unfold_const (m + 1) hcell rfl rfl rfl rfl
      · have houtF : JlValue.valid (f vals) = false := by
          cases h : JlValue.valid (f vals) with
          | false => rfl
          | true => exact absurd h hout
        apply keep
        · unfold combineChildren
          simp only [hcells, ok_bind, hallT, hvals', hval, hread, hf, pure_bind, houtF] <;> rfl
        · rw [foldValue_of hv, hval, ite_t rfl, hlen, hf]
          exact ite_f hout _ _
    · have hvalF : vals.all JlValue.valid = false := by
        cases h : vals.all JlValue.valid with
        | false => rfl
        | true => exact absurd h hval
      apply keep
      · unfold combineChildren
        simp only [hcells, ok_bind, hallT, hvals', hvalF] <;> rfl
      · rw [foldValue_of hv, hvalF]
        rfl

/-! ## `simplify_tree!` -/

/-- The per-child step of the traversal in `simplifyTree`. -/
private def stepFn (o : OpEnum T) (n : Nat) :
    List Addr × Graph T → Addr → Jl (List Addr × Graph T) :=
  fun acc ch => do
    let (r, g') ← simplifyTree o n acc.2 ch
    pure (acc.1 ++ [r], g')

private theorem simplifyTree_succ (o : OpEnum T) (n : Nat) (g : Graph T) (a : Addr) :
    simplifyTree o (n + 1) g a = (do
      let c ← g.read a
      if c.degree = 0 then return (a, g)
      let cs ← childrenOf c
      let (rs, g) ← cs.foldlM (stepFn o n) ([], g)
      let g ← combineChildren o g a rs
      return (a, g)) := rfl

omit [JlValue T] in
private theorem childrenOf_ok {c : Cell T} (hl : c.children.length = c.degree) :
    childrenOf c = .ok c.children := by
  simp [childrenOf, ← hl]
  rfl

private theorem loop (o : OpEnum T) (D nf n : Nat) (g : Graph T) (a : Addr) (c : Cell T)
    (hc : g.cells a = some c) (hcyc : ∀ ch ∈ c.children, ¬ Reachable g ch a)
    (step : List Addr × Graph T → Addr → Jl (List Addr × Graph T))
    (hstep : ∀ acc G ch uc, G.unfold n ch = some uc → uc.WF D o.nops nf →
      ∃ G1, step (acc, G) ch = .ok (acc ++ [ch], G1) ∧
        G1.unfold n ch = some (simplifyPure o uc) ∧ Pres o G G1 ∧ PathsBack G G1 ∧
        Frame G G1 ch) :
    ∀ (rest acc : List Addr) (G : Graph T),
      (∀ ch ∈ rest, ch ∈ c.children ∧ ∃ uc, g.unfold n ch = some uc ∧ uc.WF D o.nops nf) →
      Pres o g G → PathsBack g G → Frame g G a → G.cells a = g.cells a →
      (∀ r ∈ acc, ∃ uc, g.unfold n r = some uc ∧ G.unfold n r = some (simplifyPure o uc)) →
      ∃ G', rest.foldlM step (acc, G) = .ok (acc ++ rest, G') ∧ Pres o g G' ∧
        PathsBack g G' ∧ Frame g G' a ∧ G'.cells a = g.cells a ∧
        ∀ r ∈ acc ++ rest, ∃ uc, g.unfold n r = some uc ∧
          G'.unfold n r = some (simplifyPure o uc) := by
  intro rest
  induction rest with
  | nil =>
    intro acc G _ hp hb hf ha hacc
    exact ⟨G, by simp [pure_ok], hp, hb, hf, ha, by simpa using hacc⟩
  | cons ch rest ih =>
    intro acc G hrest hp hb hf ha hacc
    obtain ⟨hmem, uc, huc, hwf⟩ := hrest ch (by simp)
    obtain ⟨uc', huc', hq⟩ := hp n ch uc huc
    obtain ⟨G1, hrun, hu1, hp1, hb1, hf1⟩ := hstep acc G ch uc' huc' (hq.2.2 D nf hwf)
    have hnr : ∀ b, Reachable G ch b → Reachable g a b := fun b ⟨q, hq'⟩ =>
      reach_child hc hmem ⟨q, hb _ _ _ hq'⟩
    obtain ⟨G', hfold, hp', hb', hf', ha', hall⟩ := ih (acc ++ [ch]) G1
      (fun ch' h' => hrest ch' (by simp [h'])) (Pres_trans hp hp1)
      (fun x q y h => hb x q y (hb1 x q y h))
      (fun b hb0 => by rw [hf1 b (fun h => hb0 (hnr b h)), hf b hb0])
      (by rw [hf1 a (fun ⟨q, hq'⟩ => hcyc ch hmem ⟨q, hb _ _ _ hq'⟩), ha])
      (by
        intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · obtain ⟨ur, h1, h2⟩ := hacc r hr
          obtain ⟨w, hw, hqw⟩ := hp1 n r _ h2
          exact ⟨ur, h1, by rw [hw, hqw.2.1 (not_hasFoldable_simplifyPure o ur)]⟩
        · simp at hr
          subst hr
          exact ⟨uc, huc, by rw [hu1, hq.1]⟩)
    refine ⟨G', ?_, hp', hb', hf', ha', by simpa using hall⟩
    rw [List.foldlM_cons, hrun, ok_bind]
    simpa using hfold

private theorem main (o : OpEnum T) (D nf : Nat) :
    ∀ (fuel : Nat) (g : Graph T) (a : Addr) (u : Tree T),
      g.unfold fuel a = some u → u.WF D o.nops nf →
      ∃ g', simplifyTree o fuel g a = .ok (a, g') ∧
        g'.unfold fuel a = some (simplifyPure o u) ∧
        Pres o g g' ∧ PathsBack g g' ∧ Frame g g' a := by
  intro fuel
  induction fuel with
  | zero => intro g a u h; simp [unfold] at h
  | succ n ih =>
    intro g a u hu hwf
    obtain ⟨c, hc, hl, hshape⟩ := unfold_inv hu
    have hread : g.read a = .ok c := by simp [Heap.read, hc]
    rcases hshape with ⟨hd, hk, w, hw, rfl⟩ | ⟨hd, hk, rfl⟩ | ⟨hd, us, hus, rfl⟩
    · refine ⟨g, ?_, by rw [simplifyPure_const]; exact hu, Pres_refl o g,
        fun _ _ _ h => h, fun _ _ => rfl⟩
      simp [simplifyTree_succ, hread, hd, ok_bind, pure_ok]
    · refine ⟨g, ?_, by rw [simplifyPure_feature]; exact hu, Pres_refl o g,
        fun _ _ _ h => h, fun _ _ => rfl⟩
      simp [simplifyTree_succ, hread, hd, ok_bind, pure_ok]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero =>
          cases hch : c.children with
          | nil =>
            rw [hch] at hl
            exact absurd hl.symm hd
          | cons ch rest =>
            rw [hch] at hus
            obtain ⟨y, _, hy, _, _⟩ := mapM_cons_some hus
            simp [unfold] at hy
        | succ m => exact ⟨m, rfl⟩
      simp only [Tree.WF] at hwf
      obtain ⟨-, ⟨hop1, hop2, -⟩, hcs⟩ := hwf
      have huslen : us.length = c.children.length := mapM_length hus
      have hop : ∃ f, o.lookup c.children.length c.op = some f :=
        (o.lookup_some_iff _ _).2 ⟨hop1, huslen ▸ hop2⟩
      have hstep : ∀ acc G ch uc, G.unfold (m + 1) ch = some uc → uc.WF D o.nops nf →
          ∃ G1, stepFn o (m + 1) (acc, G) ch = .ok (acc ++ [ch], G1) ∧
            G1.unfold (m + 1) ch = some (simplifyPure o uc) ∧ Pres o G G1 ∧
            PathsBack G G1 ∧ Frame G G1 ch := by
        intro acc G ch uc h1 h2
        obtain ⟨G1, hrun, hu1, hp1, hb1, hf1⟩ := ih G ch uc h1 h2
        exact ⟨G1, by simp [stepFn, hrun, ok_bind, pure_ok], hu1, hp1, hb1, hf1⟩
      have hkids : ∀ ch ∈ c.children, ch ∈ c.children ∧
          ∃ uc, g.unfold (m + 1) ch = some uc ∧ uc.WF D o.nops nf := by
        intro ch hch
        obtain ⟨y, hy, hfy⟩ := mapM_mem hus hch
        exact ⟨hch, y, hfy, hcs y hy⟩
      obtain ⟨G, hfold, hpG, hbG, hfG, hcG, hrs⟩ :=
        loop o D nf (m + 1) g a c hc (fun ch hch => child_not_reach hu hc hch)
          (stepFn o (m + 1)) hstep c.children [] g hkids (Pres_refl o g)
          (fun _ _ _ h => h) (fun _ _ => rfl) rfl (by simp)
      have hss : c.children.mapM (G.unfold (m + 1)) = some (us.map (simplifyPure o)) :=
        mapM_map_of hus (fun x hx y hy => by
          obtain ⟨uc, h1, h2⟩ := hrs x (by simpa using hx)
          rw [h1] at hy
          cases hy
          exact h2)
      obtain ⟨G', hcomb, hunf', hpG', hbG', hfG'⟩ :=
        combine_ok o (show G.cells a = some c by rw [hcG, hc]) hl hd hss hop
      refine ⟨G', ?_, ?_, Pres_trans hpG hpG', fun x q y h => hbG x q y (hbG' x q y h), ?_⟩
      · simp only [List.nil_append] at hfold
        simp [simplifyTree_succ, hread, hd, childrenOf_ok hl, hfold, hcomb, ok_bind, pure_ok]
      · rw [simplifyPure_branch]
        exact hunf'
      · intro b hb
        have hba : b ≠ a := fun h => hb (h ▸ ⟨[], Path.nil b⟩)
        rw [hfG' b hba, hfG b hb]

end Heap

/-! ## Properties -/

/-- Constant folding leaves unreachable cells unchanged and only removes child links. -/
theorem simplifyTree_frame [JlValue T] (o : OpEnum T) (D nf fuel : Nat)
    {g h : Graph T} {root result : Addr} {t : Tree T} (hu : g.unfold fuel root = some t)
    (hw : t.WF D o.nops nf) (run : simplifyTree o fuel g root = .ok (result, h)) :
    result = root ∧
    (∀ a, ¬ Reachable g root a → h.cells a = g.cells a) ∧
    (∀ a, Reachable h result a → Reachable g root a) := by
  obtain ⟨g', he, _, _, paths, frame⟩ := main o D nf fuel g root t hu hw
  rw [run] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj he)
  exact ⟨rfl, frame, fun a ⟨p, hp⟩ => ⟨p, paths _ p a hp⟩⟩

theorem simplify_matches_spec_proof : simplify_matches_spec := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf, -⟩ := main o D nf fuel g root t hu hwf
  exact ⟨g', hrun, hunf⟩

theorem simplify_preserves_denote_proof : simplify_preserves_denote := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf⟩ := simplify_matches_spec_proof T o D nf fuel g root t hu hwf
  exact ⟨g', _, hrun, hunf, fun x => denote_simplifyPure o x t⟩

theorem simplify_wf_proof : simplify_wf := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf⟩ := simplify_matches_spec_proof T o D nf fuel g root t hu hwf
  exact ⟨g', _, hrun, hunf, wf_simplifyPure o t hwf, depth_simplifyPure o t⟩

theorem simplify_fully_folds_proof : simplify_fully_folds := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf⟩ := simplify_matches_spec_proof T o D nf fuel g root t hu hwf
  exact ⟨g', _, hrun, hunf, not_hasFoldable_simplifyPure o t⟩

theorem simplify_no_invalid_fold_proof : simplify_no_invalid_fold := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf⟩ := simplify_matches_spec_proof T o D nf fuel g root t hu hwf
  exact ⟨g', _, hrun, hunf, hasConst_simplifyPure o t⟩

theorem simplify_idempotent_proof : simplify_idempotent := by
  intro T _ o D nf fuel g root t hu hwf
  obtain ⟨g', hrun, hunf⟩ := simplify_matches_spec_proof T o D nf fuel g root t hu hwf
  obtain ⟨g'', hrun', hunf'⟩ := simplify_matches_spec_proof T o D nf fuel g' root
    (simplifyPure o t) hunf (wf_simplifyPure o t hwf)
  exact ⟨g', g'', _, hrun, hunf, hrun', by rw [hunf', simplifyPure_idem]⟩

theorem simplify_preserves_noalias_proof : simplify_preserves_noalias := by
  intro T _ o D nf fuel g root t hu hwf hna
  obtain ⟨g', hrun, -, -, hback, -⟩ := main o D nf fuel g root t hu hwf
  exact ⟨g', hrun, fun p q a hp hq => hna p q a (hback _ _ _ hp) (hback _ _ _ hq)⟩

/-! ## Satisfiable hypotheses -/

/-- One binary operator: addition. -/
private def exOps : OpEnum JF := ⟨[[], [fun vs => vs.foldl (· + ·) (JF.fin 0)]]⟩

/-- `1 + (x1 + 2)`: well formed with two features allowed. -/
private def exTree : Tree JF := .branch 1 [.const (.fin 1), .branch 1 [.feature 1, .const (.fin 2)]]

private def exG : Graph JF := (Graph.ofTree (Heap.empty : Graph JF) exTree).2
private def exRoot : Addr := (Graph.ofTree (Heap.empty : Graph JF) exTree).1

private theorem ex_unfold : exG.unfold 3 exRoot = some exTree :=
  Graph.unfold_ofTree _ _ (by simp [exTree, Tree.Representable]) 3 (by simp [exTree, Tree.depth])

private theorem ex_wf : exTree.WF 2 exOps.nops 1 := by
  simp [exTree, Tree.WF, exOps, OpEnum.nops]

private theorem ex_noAlias : Graph.NoAlias exG exRoot := Graph.noAlias_ofTree _ _

example : ∃ g', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some (simplifyPure exOps exTree) :=
  simplify_matches_spec_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g' t', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some t' ∧ ∀ x, t'.denote exOps x = exTree.denote exOps x :=
  simplify_preserves_denote_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g' t', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some t' ∧ t'.WF 2 exOps.nops 1 ∧ t'.depth ≤ exTree.depth :=
  simplify_wf_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g' t', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some t' ∧ ¬ HasFoldable exOps t' :=
  simplify_fully_folds_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g' t', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some t' ∧
    ∀ v, HasConst v t' → JlValue.valid v = true ∨ HasConst v exTree :=
  simplify_no_invalid_fold_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g' g'' t', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧
    g'.unfold 3 exRoot = some t' ∧
    simplifyTree exOps 3 g' exRoot = .ok (exRoot, g'') ∧ g''.unfold 3 exRoot = some t' :=
  simplify_idempotent_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf

example : ∃ g', simplifyTree exOps 3 exG exRoot = .ok (exRoot, g') ∧ Graph.NoAlias g' exRoot :=
  simplify_preserves_noalias_proof JF exOps 2 1 3 exG exRoot exTree ex_unfold ex_wf ex_noAlias

end DynExpr.Simplify
