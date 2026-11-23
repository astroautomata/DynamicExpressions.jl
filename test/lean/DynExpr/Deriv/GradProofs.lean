import DynExpr.Deriv.GradSpec

namespace DynExpr.Deriv

@[simp] private theorem okBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem okPure (a : α) : (pure a : Jl α) = .ok a := rfl
@[simp] private theorem okMap (a : α) (f : α → β) :
    (Except.ok a : Jl α).map f = .ok (f a) := rfl

/-! ## List and leaf lemmas -/

theorem bang_eq_getD {α : Type} [Inhabited α] (l : List α) (j : Nat) :
    l[j]! = l.getD j default := by
  simp [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

theorem getD_replicate {α : Type} (n : Nat) (a d : α) (j : Nat) (h : j < n) :
    (List.replicate n a).getD j d = a := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (d : α) (j : Nat) (h : j < n) :
    ((List.range n).map f).getD j d = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem all_of_getD {α : Type} (l : List α) (p : α → Bool) (d : α)
    (h : ∀ j < l.length, p (l.getD j d) = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have := h i hi
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem firstIncomplete_none (rs : List GradResult) :
    firstIncomplete rs = none ↔ ∀ r ∈ rs, r.complete = true := by
  simp [firstIncomplete, List.find?_eq_none]

theorem firstIncomplete_single (r : GradResult) (h : r.complete = false) :
    firstIncomplete [r] = some r := by
  simp [firstIncomplete, List.find?, h]

theorem checkResult_primal (r : GradResult) : (checkResult r).primal = r.primal := by
  unfold checkResult; split <;> rfl
theorem checkResult_gradient (r : GradResult) : (checkResult r).gradient = r.gradient := by
  unfold checkResult; split <;> rfl

theorem primal_lookup (o : DEnum) (d i : Nat) :
    o.primal.lookup d i = (o.lookup d i).map DOp.primal := by
  unfold OpEnum.lookup DEnum.lookup DEnum.primal
  split
  · rfl
  · cases h : o.ops[d - 1]? <;> simp [List.getElem?_map, h]

theorem lookup_exists (o : DEnum) (n idx : Nat) (hn : 1 ≤ n) (h1 : 1 ≤ idx)
    (h2 : idx ≤ o.nops n) : ∃ op, o.lookup n idx = some op := by
  unfold DEnum.nops at h2
  unfold DEnum.lookup
  split
  · omega
  · exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- Leaf gradient column for a one-hot row, src/EvaluateDerivative.jl:380-406. -/
def leafColumn (ng : Nat) (row? : Option Nat) : List JF :=
  match row? with
  | none => List.replicate ng zero
  | some row => (List.replicate ng zero).zipIdx.map fun (v, i) => if i + 1 = row then one else v

theorem leafColumn_length (ng : Nat) (row? : Option Nat) : (leafColumn ng row?).length = ng := by
  cases row? <;> simp [leafColumn]

theorem leafColumn_getD (ng : Nat) (row? : Option Nat) (k : Nat) (hk : k < ng) :
    (leafColumn ng row?).getD k zero = if row? = some (k + 1) then one else zero := by
  cases row? with
  | none => simp [leafColumn, List.getD_eq_getElem?_getD, hk]
  | some row =>
    simp only [leafColumn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx,
      List.getElem?_replicate, hk, ite_true, Option.map_some, Option.getD_some, Option.some.injEq]
    by_cases h : k + 1 = row
    · simp [h]
    · simp [h, Ne.symm h]

theorem leafColumn_valid (ng : Nat) (row? : Option Nat) :
    (leafColumn ng row?).all JF.valid = true := by
  apply all_of_getD _ _ zero
  intro k hk
  rw [leafColumn_length] at hk
  rw [leafColumn_getD _ _ _ hk]
  split <;> rfl

theorem leafIndex_feature (m : Mode) (nf i : Nat) : leafIndex m nf false i = featRow m i := by
  cases m <;> rfl

theorem leafIndex_const (m : Mode) (nf start : Nat) (h : start + nf < 65536) :
    leafIndex m nf true (start % 65536) = constRow m nf start := by
  have hs : start < 65536 := by omega
  have hn : nf < 65536 := by omega
  cases m with
  | features => rfl
  | constants => simp [leafIndex, constRow, Nat.mod_eq_of_lt hs]
  | both =>
    show some ((start % 65536 + nf % 65536) % 65536) = some (nf + start)
    rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h, Nat.add_comm]

/-- The leaf result with its one-hot column, src/EvaluateDerivative.jl:371-407. -/
def leafRes (ng : Nat) (values : List JF) (row? : Option Nat) : GradResult :=
  ⟨values, ⟨ng, values.length, List.replicate values.length (leafColumn ng row?)⟩, true⟩

theorem leaf_eval (s : Storage) (m : Mode) (nf ng : Nat) (values : List JF) (c : Bool)
    (idx : Nat) (hb : ∀ row, leafIndex m nf c idx = some row → 1 ≤ row ∧ row ≤ ng) :
    grad_deg0_eval s m nf ng values c idx = .ok (leafRes ng values (leafIndex m nf c idx)) := by
  unfold grad_deg0_eval
  simp only [zeroMatrix]
  cases hrow : leafIndex m nf c idx with
  | none => rfl
  | some row =>
    have := hb row hrow
    simp [this, leafRes, leafColumn, List.map_replicate]

theorem leafRes_shape (ns ng : Nat) (values : List JF) (row? : Option Nat)
    (h : values.length = ns) : GradShape ns ng (checkResult (leafRes ng values row?)) := by
  unfold GradShape
  rw [checkResult_primal, checkResult_gradient]
  refine ⟨h, rfl, h, by simp [leafRes, h], ?_⟩
  intro col hcol
  simp only [leafRes] at hcol
  rw [(List.mem_replicate.1 hcol).2, leafColumn_length]

theorem leafRes_complete (ng : Nat) (values : List JF) (row? : Option Nat) :
    (checkResult (leafRes ng values row?)).complete = values.all JF.valid := by
  simp only [checkResult, leafRes, Bool.not_true, Bool.false_eq_true, ite_false]
  have : (List.replicate values.length (leafColumn ng row?)).all
      (fun col => col.all JF.valid) = true := by
    simp [leafColumn_valid]
  simp only [this, Bool.and_true]

theorem leafRes_entry (ng : Nat) (values : List JF) (row? : Option Nat) (j k : Nat)
    (hj : j < values.length) (hk : k < ng) :
    entry (checkResult (leafRes ng values row?)) j k = if row? = some (k + 1) then one else zero := by
  simp only [entry, checkResult_gradient, leafRes]
  rw [bang_eq_getD, getD_replicate _ _ _ _ hj, leafColumn_getD _ _ _ hk]

theorem featRow_bound (m : Mode) (nf nc i row : Nat) (h : featRow m i = some row)
    (hi : 1 ≤ i ∧ i ≤ nf) : 1 ≤ row ∧ row ≤ nGradients m nf nc := by
  cases m <;> simp [featRow, nGradients] at h ⊢ <;> omega

theorem constRow_bound (m : Mode) (nf nc c row : Nat) (h : constRow m nf c = some row)
    (hc : 1 ≤ c ∧ c ≤ nc) : 1 ≤ row ∧ row ≤ nGradients m nf nc := by
  cases m <;> simp [constRow, nGradients] at h ⊢ <;> omega

theorem sampleX_row (X : JMat JF) (i j : Nat) (vals : JVec JF) (h : X.row i = .ok vals) :
    sampleX X j i = vals.toList[j]? := by
  simp [sampleX, h]

theorem getElem?_bang {α : Type} [Inhabited α] (l : List α) (j : Nat) (h : j < l.length) :
    l[j]? = some l[j]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Fused kernel output when every child has the full shape,
src/EvaluateDerivative.jl:344-368. -/
theorem kernel_eval (op : DOp) (ns ng : Nat) (rs : List GradResult) (hne : rs ≠ [])
    (hshape : ∀ r ∈ rs, GradShape ns ng r) :
    gradKernel op ns rs = .ok ⟨(List.range ns).map (fun j => op.primal (rs.map fun r => r.primal[j]!)),
      ⟨ng, ns, (List.range ns).map fun j => (List.range ng).map fun k =>
        addTerms (rs.zipIdx.map fun (r, i) =>
          op.deriv i (rs.map fun r => r.primal[j]!) * ((r.gradient.columns[j]!).getD k zero))⟩,
      true⟩ := by
  obtain ⟨r0, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := hshape r0 (by simp)
  have hany : ((r0 :: rest).any fun r => decide (r.gradient.ncols < ns) ||
      decide (r.gradient.nrows < ng)) = false := by
    rw [List.any_eq_false]
    intro r hr
    have := hshape r hr
    simp [this.2.1, this.2.2.1]
  unfold gradKernel
  simp only [List.getElem!_cons_zero, h0.2.1, h0.2.2.1, hany, Bool.false_eq_true, and_false,
    ite_false]
  rfl

theorem kernel_props (op : DOp) (ns ng : Nat) (rs : List GradResult) (hne : rs ≠ [])
    (hshape : ∀ r ∈ rs, GradShape ns ng r) :
    ∃ r0, gradKernel op ns rs = .ok r0 ∧ r0.complete = true ∧ GradShape ns ng r0 ∧
      ∀ j < ns, r0.primal[j]! = op.primal (rs.map fun r => r.primal[j]!) ∧
        ∀ k < ng, entry r0 j k = addTerms (rs.zipIdx.map fun (r, i) =>
          op.deriv i (rs.map fun r => r.primal[j]!) * ((r.gradient.columns[j]!).getD k zero)) := by
  refine ⟨_, kernel_eval op ns ng rs hne hshape, rfl, ?_, ?_⟩
  · refine ⟨by simp, rfl, rfl, by simp, ?_⟩
    intro col hcol
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hcol
    simp
  · intro j hj
    refine ⟨?_, ?_⟩
    · rw [bang_eq_getD]
      exact getD_map_range _ _ _ _ hj
    · intro k hk
      simp only [entry]
      rw [bang_eq_getD, getD_map_range _ _ _ _ hj, getD_map_range _ _ _ _ hk]

theorem shape_checkResult (ns ng : Nat) (r : GradResult) (h : GradShape ns ng r) :
    GradShape ns ng (checkResult r) := by
  simpa only [GradShape, checkResult_primal, checkResult_gradient] using h

theorem entry_checkResult (r : GradResult) (j k : Nat) :
    entry (checkResult r) j k = entry r j k := by
  simp only [entry, checkResult_gradient]

/-- A finite specification makes the final check of a matching result pass. -/
theorem checkResult_valid (o : DEnum) (X : JMat JF) (m : Mode) (ng start : Nat) (t : Tree JF)
    (r : GradResult) (hc : r.complete = true) (hs : GradShape X.ncols ng (checkResult r))
    (hm : RowsMatch o X m ng start t (checkResult r)) (hv : SpecValid o X m ng start t) :
    (checkResult r).complete = true := by
  have hp := checkResult_primal r
  have hg := checkResult_gradient r
  obtain ⟨hpl, _, _, hcl, hcols⟩ := hs
  rw [hp] at hpl
  rw [hg] at hcl hcols
  have hmr := hm
  simp only [checkResult, hc, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [Bool.and_eq_true]
  constructor
  · apply all_of_getD _ _ zero
    intro j hj
    rw [hpl] at hj
    obtain ⟨w, hw, hwv⟩ := (hv j hj).1
    rw [(hmr j hj).1, hp, bang_eq_getD] at hw
    cases hw
    exact hwv
  · apply all_of_getD _ _ []
    intro j hj
    rw [hcl] at hj
    have hmem : r.gradient.columns.getD j [] ∈ r.gradient.columns := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    apply all_of_getD _ _ zero
    intro k hk
    rw [hcols _ hmem] at hk
    obtain ⟨v, d, hd, hdv⟩ := (hv j hj).2 k hk
    rw [(hmr j hj).2 k hk] at hd
    simp only [entry, hg, bang_eq_getD, Option.some.injEq, Prod.mk.injEq] at hd
    rw [← hd.2] at hdv
    exact hdv

/-! ## Main induction -/

/-- Everything proven about one gradient call. -/
def GradGood (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (ng start : Nat)
    (t : Tree JF) (r : GradResult) : Prop :=
  gradTree s m o X ng start t = .ok r ∧ GradShape X.ncols ng r ∧
    (r.complete = true → RowsMatch o X m ng start t r) ∧
    (AllValid o X m ng start t → r.complete = true)

theorem children_good (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (nc ng D : Nat)
    (cs : List (Tree JF))
    (ih : ∀ c ∈ cs, ∀ start, c.WF D o.nops X.nrows → 1 ≤ start →
      start + (scalarConstants c).length ≤ nc + 1 → ∃ r, GradGood s m o X ng start c r) :
    ∀ start, (∀ c ∈ cs, c.WF D o.nops X.nrows) → 1 ≤ start →
      start + (cs.flatMap scalarConstants).length ≤ nc + 1 →
      ∃ rs, collectChildren (gradTreeList s m o X ng start cs) = .ok rs ∧
        (∀ r ∈ rs, GradShape X.ncols ng r) ∧
        ((∃ r, rs = [r] ∧ r.complete = false) ∨
          ((∀ r ∈ rs, r.complete = true) ∧ rs.length = cs.length ∧ ∀ j < X.ncols,
            cs.mapM (Tree.denote o.primal (sampleX X j)) = some (rs.map fun r => r.primal[j]!) ∧
            ∀ k < ng, denoteSeedList o (sampleX X j) (rowSeedF m (k + 1))
              (rowSeedC m X.nrows (k + 1)) start cs =
                some (rs.map fun r => (r.primal[j]!, entry r j k)))) ∧
        (AllValidList o X m ng start cs → ∀ r ∈ rs, r.complete = true) := by
  induction cs with
  | nil =>
    intro start _ _ _
    refine ⟨[], rfl, by simp, Or.inr ⟨by simp, rfl, fun j _ => ⟨rfl, fun k _ => rfl⟩⟩,
      fun _ => by simp⟩
  | cons c cs ihl =>
    intro start hwf h1 hb
    simp only [List.flatMap_cons, List.length_append] at hb
    obtain ⟨r, hr, hshape, hmatch, hvalid⟩ :=
      ih c (by simp) start (hwf c (by simp)) h1 (by omega)
    obtain ⟨rs, hrs, hshapes, hcases, hvalids⟩ :=
      ihl (fun c' hc' => ih c' (by simp [hc'])) (start + (scalarConstants c).length)
        (fun c' hc' => hwf c' (by simp [hc'])) (by omega) (by omega)
    simp only [gradTreeList, collectChildren, hr, okBind]
    cases hcomp : r.complete with
    | false =>
      refine ⟨[r], by simp, by simpa using hshape, Or.inl ⟨r, rfl, hcomp⟩, ?_⟩
      intro hv
      simp only [AllValidList] at hv
      rw [hvalid hv.1] at hcomp
      cases hcomp
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, hrs, okBind]
      rcases hcases with ⟨r', rfl, hr'⟩ | ⟨hall, hlen, hfacts⟩
      · rw [firstIncomplete_single r' hr']
        refine ⟨[r'], rfl, hshapes, Or.inl ⟨r', rfl, hr'⟩, ?_⟩
        intro hv
        simp only [AllValidList] at hv
        have := hvalids hv.2 r' (by simp)
        rw [hr'] at this
        cases this
      · rw [(firstIncomplete_none rs).2 hall]
        refine ⟨r :: rs, rfl, ?_, Or.inr ⟨?_, by simp [hlen], ?_⟩, ?_⟩
        · intro r'' h''
          rcases List.mem_cons.1 h'' with rfl | h''
          · exact hshape
          · exact hshapes r'' h''
        · intro r'' h''
          rcases List.mem_cons.1 h'' with rfl | h''
          · exact hcomp
          · exact hall r'' h''
        · intro j hj
          have hm := hmatch hcomp j hj
          have hf := hfacts j hj
          refine ⟨?_, ?_⟩
          · simp [List.mapM_cons, hm.1, hf.1]
          · intro k hk
            simp [denoteSeedList, (hm.2 k hk), (hf.2 k hk)]
        · intro _ r'' h''
          rcases List.mem_cons.1 h'' with rfl | h''
          · exact hcomp
          · exact hall r'' h''

theorem gradTree_good (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (nc ng D : Nat)
    (hng : ng = nGradients m X.nrows nc) (hcap : X.nrows + nc ≤ 65535) :
    ∀ t start, t.WF D o.nops X.nrows → 1 ≤ start →
      start + (scalarConstants t).length ≤ nc + 1 → ∃ r, GradGood s m o X ng start t r := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro start _ h1 hb
    simp only [scalarConstants, List.length_singleton] at hb
    have hrow := leafIndex_const m X.nrows start (by omega)
    have hleaf := leaf_eval s m X.nrows ng (List.replicate X.ncols v) true (start % 65536)
      (by intro row h; rw [hrow] at h; rw [hng]; exact constRow_bound m _ nc _ _ h ⟨h1, by omega⟩)
    rw [hrow] at hleaf
    refine ⟨checkResult (leafRes ng (List.replicate X.ncols v) (constRow m X.nrows start)),
      by rw [gradTree_const, hleaf]; rfl, leafRes_shape _ _ _ _ (by simp), ?_, ?_⟩
    · intro _ j hj
      have hv : (checkResult (leafRes ng (List.replicate X.ncols v) (constRow m X.nrows start))).primal[j]! = v := by
        rw [checkResult_primal]
        simp [leafRes, hj]
      refine ⟨by rw [hv]; simp [Tree.denote], ?_⟩
      intro k hk
      rw [hv, leafRes_entry _ _ _ _ _ (by simpa using hj) hk]
      simp [denoteSeed, rowSeedC]
    · intro hvalid
      rw [leafRes_complete]
      apply all_of_getD _ _ zero
      intro j hj
      simp only [List.length_replicate] at hj
      obtain ⟨w, hw, hwv⟩ := ((show SpecValid o X m ng start (.const v) from hvalid) j hj).1
      simp only [Tree.denote, Option.some.injEq] at hw
      rw [getD_replicate _ _ _ _ hj, hw]
      exact hwv
  | hf i =>
    intro start hwf _ _
    simp only [Tree.WF] at hwf
    obtain ⟨vals, hvals, hsize⟩ := X.row_exists i hwf.1 hwf.2.1
    have hlen : vals.toList.length = X.ncols := by simpa using hsize
    have hleaf := leaf_eval s m X.nrows ng vals.toList false i
      (by intro row h; rw [leafIndex_feature] at h; rw [hng]
          exact featRow_bound m _ nc _ _ h ⟨hwf.1, hwf.2.1⟩)
    rw [leafIndex_feature] at hleaf
    refine ⟨checkResult (leafRes ng vals.toList (featRow m i)),
      by rw [gradTree_feature, hvals]; simp only [okBind, hleaf, okMap],
      leafRes_shape _ _ _ _ hlen, ?_, ?_⟩
    · intro _ j hj
      have hx : sampleX X j i = some (checkResult (leafRes ng vals.toList (featRow m i))).primal[j]! := by
        rw [checkResult_primal, sampleX_row X i j vals hvals]
        exact getElem?_bang _ _ (by omega)
      refine ⟨by simp only [Tree.denote]; exact hx, ?_⟩
      intro k hk
      simp only [denoteSeed, hx, Option.map_some]
      rw [leafRes_entry _ _ _ _ _ (by omega) hk]
      simp [rowSeedF]
    · intro hvalid
      rw [leafRes_complete]
      apply all_of_getD _ _ zero
      intro j hj
      obtain ⟨w, hw, hwv⟩ := ((show SpecValid o X m ng start (.feature i) from hvalid) j (by omega)).1
      simp only [Tree.denote, sampleX_row X i j vals hvals,
        List.getElem?_eq_getElem hj, Option.some.injEq] at hw
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, hw]
      exact hwv
  | hb idx cs ih =>
    intro start hwf h1 hb
    simp only [Tree.WF] at hwf
    simp only [scalarConstants] at hb
    obtain ⟨rs, hrs, hshapes, hcases, hvalids⟩ :=
      children_good s m o X nc ng D cs ih start hwf.2.2 h1 hb
    rcases hcases with ⟨r', rfl, hr'⟩ | ⟨hall, hlen, hfacts⟩
    · refine ⟨r', ?_, hshapes r' (by simp), ⟨fun h => absurd (hr'.symm.trans h) Bool.false_ne_true, ?_⟩⟩
      · rw [gradTree_branch, hrs]
        simp only [okBind, firstIncomplete_single r' hr', okPure]
      · intro hv
        have := hvalids (show AllValid o X m ng start (.branch idx cs) from hv).2 r' (by simp)
        rw [hr'] at this
        cases this
    · obtain ⟨op, hop⟩ := lookup_exists o cs.length idx hwf.1.1 hwf.2.1.1 hwf.2.1.2.1
      have hne : rs ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      obtain ⟨r0, hk, hc0, hs0, hv0⟩ := kernel_props op X.ncols ng rs hne hshapes
      have hrm : RowsMatch o X m ng start (.branch idx cs) (checkResult r0) := by
        intro j hj
        have hf := hfacts j hj
        have hpj := (hv0 j hj).1
        rw [checkResult_primal]
        refine ⟨?_, ?_⟩
        · rw [hpj]
          simp [Tree.denote, primal_lookup, hop, hf.1]
        · intro k hk
          rw [hpj, entry_checkResult, (hv0 j hj).2 k hk]
          simp only [denoteSeed, hf.2 k hk, hop, Option.bind_eq_bind, Option.bind_some,
            List.map_map, List.zipIdx_map]
          rfl
      refine ⟨checkResult r0, ?_, shape_checkResult _ _ _ hs0, ⟨fun _ => hrm, ?_⟩⟩
      · rw [gradTree_branch, hrs]
        simp only [okBind, (firstIncomplete_none rs).2 hall, hop, hk, okMap]
      · intro hv
        exact checkResult_valid o X m ng start _ r0 hc0 (shape_checkResult _ _ _ hs0) hrm
          (show AllValid o X m ng start (.branch idx cs) from hv).1

/-! ## Seeds and the public properties -/

/-- The seeded derivative depends on feature seeds only at well-formed feature
indices and on constant seeds only from `start` on. -/
theorem denoteSeed_congr (o : DEnum) (x : Nat → Option JF) (fs fs' cseed cseed' : Nat → JF)
    (nf D : Nat) (hf : ∀ i, 1 ≤ i → i ≤ nf → fs i = fs' i) :
    ∀ t start, t.WF D o.nops nf → (∀ c, start ≤ c → cseed c = cseed' c) →
      denoteSeed o x fs cseed start t = denoteSeed o x fs' cseed' start t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro start _ hc; simp [denoteSeed, hc start (Nat.le_refl _)]
  | hf i =>
    intro start hw _
    simp only [Tree.WF] at hw
    simp [denoteSeed, hf i hw.1 hw.2.1]
  | hb idx cs ih =>
    intro start hw hc
    simp only [Tree.WF] at hw
    have hl : ∀ l : List (Tree JF), (∀ c ∈ l, c ∈ cs) → ∀ st, start ≤ st →
        denoteSeedList o x fs cseed st l = denoteSeedList o x fs' cseed' st l := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons c l ihl =>
        intro hsub st hst
        have hcs := hsub c (by simp)
        simp only [denoteSeedList]
        rw [ih c hcs st (hw.2.2 c hcs) (fun k hk => hc k (by omega)),
          ihl (fun c' h => hsub c' (by simp [h])) _ (by omega)]
    simp only [denoteSeed]
    rw [hl cs (fun c h => h) start (Nat.le_refl _)]

/-- Feature seeds one-hot at `d` and zero constant seeds give `Tree.denoteDeriv`. -/
theorem denoteSeed_deriv (o : DEnum) (x : Nat → Option JF) (d : Nat) :
    ∀ t start, denoteSeed o x (fun i => if i = d then one else zero) (fun _ => zero) start t =
      t.denoteDeriv o x d := by
  intro t
  induction t using Tree.induction with
  | hc v => intro; simp [denoteSeed, Tree.denoteDeriv]
  | hf i => intro; simp [denoteSeed, Tree.denoteDeriv]
  | hb idx cs ih =>
    intro start
    have hl : ∀ l : List (Tree JF), (∀ c ∈ l, c ∈ cs) → ∀ st,
        denoteSeedList o x (fun i => if i = d then one else zero) (fun _ => zero) st l =
          l.mapM (Tree.denoteDeriv o x d) := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons c l ihl =>
        intro hsub st
        simp only [denoteSeedList, List.mapM_cons]
        rw [ih c (hsub c (by simp)) st, ihl (fun c' h => hsub c' (by simp [h]))]
    simp only [denoteSeed, Tree.denoteDeriv]
    rw [hl cs (fun c h => h) start]

theorem constLeaves_order :
    ∀ (t : Tree JF) (start : Nat), constLeaves start t = (scalarConstants t).zipIdx start := by
  intro t
  induction t using Tree.induction with
  | hc v => intro; simp [constLeaves, scalarConstants]
  | hf i => intro; simp [constLeaves, scalarConstants]
  | hb idx cs ih =>
    intro start
    have hl : ∀ l : List (Tree JF), (∀ c ∈ l, c ∈ cs) → ∀ st,
        constLeavesList st l = (l.flatMap scalarConstants).zipIdx st := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons c l ihl =>
        intro hsub st
        simp only [constLeavesList, List.flatMap_cons, List.zipIdx_append]
        rw [ih c (hsub c (by simp)) st, ihl (fun c' h => hsub c' (by simp [h]))]
    simp only [constLeaves, scalarConstants]
    exact hl cs (fun c h => h) start

theorem constantOrdering_proof : constantOrdering := constLeaves_order
example : constLeaves 1 (.branch 1 [.const one, .feature 1, .const zero] : Tree JF) =
    [(one, 1), (zero, 2)] := by simp [constLeaves, constLeavesList, scalarConstants]

/-- Feature rows of a matching gradient are `Tree.denoteDeriv`. -/
theorem rows_feature (o : DEnum) (X : JMat JF) (m : Mode) (nc D : Nat) (t : Tree JF)
    (r : GradResult) (hwf : t.WF D o.nops X.nrows)
    (hm : RowsMatch o X m (nGradients m X.nrows nc) 1 t r) (hmode : m ≠ .constants)
    (j : Nat) (hj : j < X.ncols) (q : Nat) (hq1 : 1 ≤ q) (hqn : q ≤ X.nrows) :
    t.denoteDeriv o (sampleX X j) q = some (r.primal[j]!, entry r j (q - 1)) := by
  have hlt : q - 1 < nGradients m X.nrows nc := by
    cases m <;> simp [nGradients] at hmode ⊢ <;> omega
  have h := (hm j hj).2 (q - 1) hlt
  rw [show q - 1 + 1 = q by omega] at h
  rw [← denoteSeed_deriv o (sampleX X j) q t 1]
  rw [denoteSeed_congr o (sampleX X j) _ (rowSeedF m q) _ (rowSeedC m X.nrows q) X.nrows D
    (by intro i _ _; cases m <;> simp [rowSeedF, featRow] at hmode ⊢) t 1 hwf
    (by intro c hc; cases m <;> simp [rowSeedC, constRow] at hmode ⊢ <;> omega)]
  exact h

/-- Constant rows of a matching gradient are the constant partials. -/
theorem rows_const (o : DEnum) (X : JMat JF) (m : Mode) (nc D : Nat) (t : Tree JF)
    (r : GradResult) (hwf : t.WF D o.nops X.nrows)
    (hm : RowsMatch o X m (nGradients m X.nrows nc) 1 t r)
    (j : Nat) (hj : j < X.ncols) (c row : Nat) (hc1 : 1 ≤ c) (hcn : c ≤ nc)
    (hrow : constRow m X.nrows c = some row) :
    constPartial o (sampleX X j) c t = some (r.primal[j]!, entry r j (row - 1)) := by
  have hb := constRow_bound m X.nrows nc c row hrow ⟨hc1, hcn⟩
  have h := (hm j hj).2 (row - 1) (by omega)
  rw [show row - 1 + 1 = row by omega] at h
  unfold constPartial
  rw [denoteSeed_congr o (sampleX X j) _ (rowSeedF m row) _ (rowSeedC m X.nrows row) X.nrows D
    (by intro i _ hi; cases m <;> simp [constRow] at hrow <;> simp [rowSeedF, featRow] <;> omega)
    t 1 hwf
    (by intro n _; cases m <;> simp [constRow] at hrow <;> subst hrow <;> simp [rowSeedC, constRow])]
  exact h

/-! ## Finite inputs give finite intermediates -/

theorem valid_add {a b : JF} (ha : a.valid = true) (hb : b.valid = true) :
    (JF.add a b).valid = true := by
  cases a <;> cases b <;> simp_all [JF.add, JF.valid]

theorem valid_mul {a b : JF} (ha : a.valid = true) (hb : b.valid = true) :
    (a * b).valid = true := by
  show (JF.mul a b).valid = true
  cases a <;> cases b <;> simp_all [JF.mul, JF.valid]

theorem valid_foldl (l : List JF) :
    ∀ acc, acc.valid = true → (∀ x ∈ l, x.valid = true) → (l.foldl JF.add acc).valid = true := by
  induction l with
  | nil => intro acc h _; exact h
  | cons a l ih =>
    intro acc h hl
    exact ih _ (valid_add h (hl a (by simp))) (fun x hx => hl x (by simp [hx]))

theorem valid_addTerms (l : List JF) (h : ∀ x ∈ l, x.valid = true) : (addTerms l).valid = true := by
  cases l with
  | nil => rfl
  | cons a l => exact valid_foldl l a (h a (by simp)) (fun x hx => h x (by simp [hx]))

theorem row_finite (X : JMat JF) (hX : FiniteMatrix X) (k : Nat) (vals : JVec JF)
    (h : X.row k = .ok vals) : ∀ v ∈ vals.toList, v.valid = true := by
  intro v hv
  unfold JMat.row at h
  split at h
  · cases h
    rw [Array.toList_ofFn, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact hX _ (Array.getElem_mem _)
  · cases h

/-- Every in-range feature of an in-range sample is bound to a finite value. -/
theorem sampleX_good (X : JMat JF) (hX : FiniteMatrix X) (j : Nat) (hj : j < X.ncols) :
    ∀ k, 1 ≤ k → k ≤ X.nrows → ∃ w, sampleX X j k = some w ∧ w.valid = true := by
  intro k h1 h2
  obtain ⟨vals, hvals, hsize⟩ := X.row_exists k h1 h2
  have hlen : j < vals.toList.length := by simpa [hsize] using hj
  refine ⟨vals.toList[j]!, ?_, ?_⟩
  · rw [sampleX_row X k j vals hvals]
    exact getElem?_bang _ _ hlen
  · apply row_finite X hX k vals hvals
    exact List.mem_of_getElem? (getElem?_bang _ _ hlen)

theorem finiteConstants_child {idx : Nat} {cs : List (Tree JF)} {c : Tree JF}
    (h : FiniteConstants (.branch idx cs)) (hc : c ∈ cs) : FiniteConstants c := by
  intro v hv
  apply h
  simp only [scalarConstants]
  exact List.mem_flatMap.2 ⟨c, hc, hv⟩

theorem kernel_valid (op : DOp)
    (hop : ∀ xs : List JF, (∀ x ∈ xs, x.valid = true) →
      (op.primal xs).valid = true ∧ ∀ n, (op.deriv n xs).valid = true)
    (children : List (JF × JF)) (hch : ∀ p ∈ children, p.1.valid = true ∧ p.2.valid = true) :
    (op.primal (children.map Prod.fst)).valid = true ∧
      (addTerms (children.zipIdx.map fun (child, i) =>
        op.deriv i (children.map Prod.fst) * child.2)).valid = true := by
  have hxs : ∀ x ∈ children.map Prod.fst, x.valid = true := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (hch p hp).1
  refine ⟨(hop _ hxs).1, valid_addTerms _ ?_⟩
  intro x hx
  obtain ⟨⟨child, i⟩, hp, rfl⟩ := List.mem_map.1 hx
  exact valid_mul ((hop _ hxs).2 i) (hch child (List.fst_mem_of_mem_zipIdx hp)).2

/-- For finite inputs, constants and seeds, and finiteness-preserving operators,
the seeded derivative and the denotation are defined and finite. -/
theorem seed_valid (o : DEnum) (x : Nat → Option JF) (fseed cseed : Nat → JF) (nf D : Nat)
    (hx : ∀ k, 1 ≤ k → k ≤ nf → ∃ w, x k = some w ∧ w.valid = true)
    (hfs : ∀ i, (fseed i).valid = true) (hcs : ∀ c, (cseed c).valid = true)
    (hops : FiniteOps o) :
    ∀ t start, t.WF D o.nops nf → FiniteConstants t →
      ∃ v d, denoteSeed o x fseed cseed start t = some (v, d) ∧
        Tree.denote o.primal x t = some v ∧ v.valid = true ∧ d.valid = true := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro start _ hc
    exact ⟨v, cseed start, by simp [denoteSeed], by simp [Tree.denote],
      hc v (by simp [scalarConstants]), hcs start⟩
  | hf i =>
    intro start hw _
    simp only [Tree.WF] at hw
    obtain ⟨w, hw', hwv⟩ := hx i hw.1 hw.2.1
    exact ⟨w, fseed i, by simp [denoteSeed, hw'], by simp [Tree.denote, hw'], hwv, hfs i⟩
  | hb idx cs ih =>
    intro start hw hc
    simp only [Tree.WF] at hw
    have hl : ∀ l : List (Tree JF), (∀ c ∈ l, c ∈ cs) → ∀ st, ∃ ps,
        denoteSeedList o x fseed cseed st l = some ps ∧
        l.mapM (Tree.denote o.primal x) = some (ps.map Prod.fst) ∧
        ∀ p ∈ ps, p.1.valid = true ∧ p.2.valid = true := by
      intro l
      induction l with
      | nil => intro _ _; exact ⟨[], rfl, rfl, by simp⟩
      | cons c l ihl =>
        intro hsub st
        have hcs := hsub c (by simp)
        obtain ⟨v, d, h1, h2, hv, hd⟩ := ih c hcs st (hw.2.2 c hcs) (finiteConstants_child hc hcs)
        obtain ⟨ps, hps, hmap, hval⟩ :=
          ihl (fun c' h => hsub c' (by simp [h])) (st + (scalarConstants c).length)
        refine ⟨(v, d) :: ps, by simp [denoteSeedList, h1, hps],
          by simp [List.mapM_cons, h2, hmap], ?_⟩
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hv, hd⟩
        · exact hval p hp
    obtain ⟨ps, hps, hmap, hval⟩ := hl cs (fun c h => h) start
    obtain ⟨op, hop⟩ := lookup_exists o cs.length idx hw.1.1 hw.2.1.1 hw.2.1.2.1
    have hk := kernel_valid op (hops _ _ op hop) ps hval
    refine ⟨op.primal (ps.map Prod.fst), addTerms (ps.zipIdx.map fun (child, i) =>
      op.deriv i (ps.map Prod.fst) * child.2), ?_, ?_, hk.1, hk.2⟩
    · simp [denoteSeed, hps, hop]
    · simp [Tree.denote, primal_lookup, hop, hmap]

theorem allValid_of_finite (o : DEnum) (X : JMat JF) (m : Mode) (ng D : Nat)
    (hX : FiniteMatrix X) (hops : FiniteOps o) :
    ∀ t start, t.WF D o.nops X.nrows → FiniteConstants t → AllValid o X m ng start t := by
  have hspec : ∀ t start, t.WF D o.nops X.nrows → FiniteConstants t →
      SpecValid o X m ng start t := by
    intro t start hw hc j hj
    have hx := sampleX_good X hX j hj
    obtain ⟨v, _, _, h2, hv, _⟩ := seed_valid o _ (fun _ => zero) (fun _ => zero) _ D hx
      (fun _ => rfl) (fun _ => rfl) hops t start hw hc
    refine ⟨⟨v, h2, hv⟩, ?_⟩
    intro k _
    obtain ⟨v', d', h1', _, _, hd'⟩ := seed_valid o _ (rowSeedF m (k + 1))
      (rowSeedC m X.nrows (k + 1)) _ D hx (by intro i; unfold rowSeedF; split <;> rfl)
      (by intro c; unfold rowSeedC; split <;> rfl) hops t start hw hc
    exact ⟨v', d', h1', hd'⟩
  intro t
  induction t using Tree.induction with
  | hc v => intro start hw hc; exact hspec _ start hw hc
  | hf i => intro start hw hc; exact hspec _ start hw hc
  | hb idx cs ih =>
    intro start hw hc
    have hsp := hspec _ start hw hc
    simp only [Tree.WF] at hw
    have hl : ∀ l : List (Tree JF), (∀ c ∈ l, c ∈ cs) → ∀ st, AllValidList o X m ng st l := by
      intro l
      induction l with
      | nil => intros; exact trivial
      | cons c l ihl =>
        intro hsub st
        have hcs := hsub c (by simp)
        exact ⟨ih c hcs st (hw.2.2 c hcs) (finiteConstants_child hc hcs),
          ihl (fun c' h => hsub c' (by simp [h])) _⟩
    exact ⟨hsp, hl cs (fun c h => h) start⟩

theorem gradientModes_proof : gradientModes := by
  intro s m o X t D
  dsimp only
  intro hwf hcap
  obtain ⟨r, hr, hs, hm, hv⟩ := gradTree_good s m o X (scalarConstants t).length
    (nGradients m X.nrows (scalarConstants t).length) D rfl hcap t 1 hwf
    (Nat.le_refl _) (by omega)
  refine ⟨r, by unfold eval_grad_tree_array; exact hr, hs,
    fun hX hct hops => hv (allValid_of_finite o X m _ D hX hops t 1 hwf hct), ?_⟩
  intro hc j hj
  exact ⟨(hm hc j hj).1,
    fun hmode q hq1 hqn => rows_feature o X m _ D t r hwf (hm hc) hmode j hj q hq1 hqn,
    fun c row hc1 hcn hrow => rows_const o X m _ D t r hwf (hm hc) j hj c row hc1 hcn hrow⟩

theorem pullbackEndToEnd_proof : pullbackEndToEnd := by
  intro o X t D dY dComplete
  dsimp only
  intro hwf hcap hdy hns
  obtain ⟨r, hr, hs, hm, hv⟩ := gradTree_good .dense .both o X (scalarConstants t).length
    (X.nrows + (scalarConstants t).length) D rfl hcap t 1 hwf
    (Nat.le_refl _) (by omega)
  obtain ⟨_, hnr, hnc, hcl, hcols⟩ := hs
  have hgrad : eval_grad_tree_array .dense .both o X t = .ok r := by
    unfold eval_grad_tree_array; exact hr
  have hne : dY.isEmpty = false := by
    cases dY with
    | nil => simp at hdy; omega
    | cons _ _ => rfl
  by_cases hc : r.complete = true
  · have hmatch := hm hc
    have hdyl : dY.length = r.gradient.ncols := by omega
    unfold EvalPullback.call
    simp only [hgrad, okBind, hc, ite_true, constantPullback, featurePullback, hdyl, ne_eq,
      not_true_eq_false, ite_false, hne, Bool.false_eq_true, okPure, hnr, Nat.add_sub_cancel_left,
      eq_self_iff_true, ↓reduceIte]
    refine ⟨_, rfl, rfl, rfl, rfl, by simp [extract_gradient], rfl, hnc,
      by simp [hcl], fun _ _ _ => ⟨?_, ?_⟩⟩
    · simp only [extract_gradient]
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      congr 1
      apply List.map_congr_left
      intro p hp
      obtain ⟨dy, j⟩ := p
      have hj := (List.mem_zipIdx hp).2.1
      have := rows_const o X .both _ D t r hwf hmatch j (by omega) (k + 1)
        (X.nrows + (k + 1)) (by omega) (by omega) rfl
      simp only [this, Option.map_some, Option.getD_some, entry]
      rw [show X.nrows + (k + 1) - 1 = X.nrows + k by omega]
    · intro j hj q hq1 hqn
      have hjc : j < r.gradient.columns.length := by omega
      have hcol := hcols _ (List.getElem_mem hjc)
      have := rows_feature o X .both _ D t r hwf hmatch (by decide) j hj q hq1 hqn
      simp only [this, Option.map_some, Option.getD_some, entry]
      simp only [bang_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_zipIdx, List.getElem?_eq_getElem hjc, Option.map_some, Option.getD_some,
        Nat.zero_add, List.getElem?_take_of_lt (show q - 1 < X.nrows by omega),
        List.getElem?_eq_getElem (show q - 1 < r.gradient.columns[j].length by omega)]
  · have hf : r.complete = false := by simpa using hc
    have hdyl : dY.length = (invalidateMatrix r.gradient).ncols := by
      simp only [invalidateMatrix]; omega
    unfold EvalPullback.call
    simp only [hgrad, okBind, hf, Bool.false_eq_true, ite_false, constantPullback,
      featurePullback, hdyl, ne_eq, not_true_eq_false, hne, okPure, eq_self_iff_true, ite_true,
      ↓reduceIte]
    refine ⟨_, rfl, rfl, rfl, rfl, by simp [extract_gradient, invalidateMatrix, hnr], rfl,
      by simp [invalidateMatrix, hnc],
      by simp [invalidateMatrix, hcl], ?_⟩
    intro hX hct hops
    have := hv (allValid_of_finite o X .both _ D hX hops t 1 hwf hct)
    rw [hf] at this
    cases this

/-- One feature, one sample; with `x1 = 1`, the constant tree `1`, the empty
operator enum and `dY = [1]` it satisfies the hypotheses of deriv-gradient-modes
and deriv-pullback-end-to-end. -/
def oneSample : JMat JF := ⟨1, 1, #[one], by decide⟩

example : (Tree.const one : Tree JF).WF 2 (DEnum.nops ⟨[]⟩) oneSample.nrows ∧
    oneSample.nrows + (scalarConstants (Tree.const one : Tree JF)).length ≤ 65535 ∧
    [one].length = oneSample.ncols ∧ 0 < oneSample.ncols ∧
    FiniteMatrix oneSample ∧ FiniteConstants (.const one) ∧ FiniteOps ⟨[]⟩ := by
  refine ⟨by simp [Tree.WF], by simp [scalarConstants, oneSample], rfl, by decide, ?_, ?_, ?_⟩
  · intro v hv
    simp [oneSample] at hv
    subst hv
    rfl
  · intro v hv
    simp [scalarConstants] at hv
    subst hv
    rfl
  · intro d i op h
    simp [DEnum.lookup] at h

end DynExpr.Deriv
