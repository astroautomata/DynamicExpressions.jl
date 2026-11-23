import DynExpr.Deriv.Companions
import DynExpr.Runtime.Heap

/-! Object-identity mirror of `eval_grad_tree_array` and of the rrule pullback.
Arrays live on a heap: leaves allocate their value and gradient arrays, fused
kernels overwrite the arrays of their first child in place, and the input
matrix and cotangent are heap objects read by the evaluator. The numeric work
is done by the same mirror functions as `gradTree`, so each result is proven
equal to the pure mirror. src/EvaluateDerivative.jl:197-409,
src/ChainRules.jl:57-80. -/

namespace DynExpr.Deriv

@[simp] private theorem hBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem hPure (a : α) : (pure a : Jl α) = .ok a := rfl

/-- Heap objects used by the derivative evaluators: the input matrix `cX`,
vectors (values, cotangents, constant gradients) and gradient matrices. -/
inductive Obj where
  | input (X : JMat JF)
  | vec (v : List JF)
  | mat (g : GradMatrix)

/-- Identities of a result's value and gradient arrays and its `ok` flag
(`ResultOk2`, src/Utils.jl:81-85). -/
structure HRes where
  va : Nat
  ga : Nat
  complete : Bool

/-- Reading the input matrix object. -/
def readInput (h : Heap Obj) (xa : Nat) : Jl (JMat JF) := do
  let o ← h.read xa
  match o with
  | .input X => pure X
  | _ => .error (.methodError "matrix input expected")

/-- Reading the cotangent vector object. -/
def readVec (h : Heap Obj) (a : Nat) : Jl (List JF) := do
  let o ← h.read a
  match o with
  | .vec v => pure v
  | _ => .error (.methodError "vector expected")

/-- Reading a child's cumulators `x_cumulator_i`, `d_cumulator_i`,
src/EvaluateDerivative.jl:316-317,348-351. -/
def readGrad (h : Heap Obj) (r : HRes) : Jl GradResult := do
  let v ← h.read r.va
  let g ← h.read r.ga
  match v, g with
  | .vec v, .mat g => pure ⟨v, g, true⟩
  | _, _ => .error (.methodError "cumulator arrays expected")

/-- A leaf allocates its value array (`deg0_eval` with a fresh `EvalContext()`:
`fill` or the copy `X[feature, :]`) and then its gradient array
(`fill_similar` or the adjoint of `hcat`), src/EvaluateDerivative.jl:378-384,
src/Evaluate.jl:90-99. -/
def allocPair (a b : Obj) (complete : Bool) (h : Heap Obj) : HRes × Heap Obj :=
  let p := h.alloc a
  let q := p.2.alloc b
  (⟨p.1, q.1, complete⟩, q.2)

/-- The fused kernel writes its results into the first child's arrays and
returns them, src/EvaluateDerivative.jl:353-367. -/
def fusedWrite (c : GradResult) (rs : List HRes) (h : Heap Obj) : Jl (HRes × Heap Obj) :=
  match rs with
  | [] => .error (.undefinedBehavior "no cumulator")
  | r1 :: _ => do
      let h2 ← h.write r1.va (.vec c.primal)
      let h3 ← h2.write r1.ga (.mat c.gradient)
      pure (⟨r1.va, r1.ga, c.complete⟩, h3)

mutual
/-- Heap mirror of the recursive `eval_grad_tree_array` (with its finite check)
and `_eval_grad_tree_array`, src/EvaluateDerivative.jl:234-409. -/
def gradTreeH (s : Storage) (m : Mode) (o : DEnum) (xa : Nat) (ng start : Nat) :
    Tree JF → Heap Obj → Jl (HRes × Heap Obj)
  | .const v, h => do
      let X ← readInput h xa
      let r ← grad_deg0_eval s m X.nrows ng (List.replicate X.ncols v) true (start % 65536)
      let c := checkResult r
      pure (allocPair (.vec c.primal) (.mat c.gradient) c.complete h)
  | .feature k, h => do
      let X ← readInput h xa
      let vals ← X.row k
      let r ← grad_deg0_eval s m X.nrows ng vals.toList false k
      let c := checkResult r
      pure (allocPair (.vec c.primal) (.mat c.gradient) c.complete h)
  | .branch idx cs, h => do
      let (res, h1) ← gradListH s m o xa ng start cs h
      match res with
      | .inl e => pure (e, h1)
      | .inr rs =>
          match o.lookup cs.length idx with
          | none => .error (.undefinedBehavior "generated operator dispatch has no matching arm")
          | some op => do
              let X ← readInput h1 xa
              let grs ← rs.mapM (readGrad h1)
              let out ← gradKernel op X.ncols grs
              fusedWrite (checkResult out) rs h1

/-- The children loop with its early exit, src/EvaluateDerivative.jl:302-315. -/
def gradListH (s : Storage) (m : Mode) (o : DEnum) (xa : Nat) (ng start : Nat) :
    List (Tree JF) → Heap Obj → Jl ((HRes ⊕ List HRes) × Heap Obj)
  | [], h => pure (.inr [], h)
  | c :: cs, h => do
      let (r, h1) ← gradTreeH s m o xa ng start c h
      if !r.complete then pure (.inl r, h1)
      else do
        let (rest, h2) ← gradListH s m o xa ng (start + (scalarConstants c).length) cs h1
        match rest with
        | .inl e => pure (.inl e, h2)
        | .inr rs => pure (.inr (r :: rs), h2)
end

/-- Public `eval_grad_tree_array` on heap objects, src/EvaluateDerivative.jl:197-232. -/
def evalGradH (s : Storage) (m : Mode) (o : DEnum) (xa : Nat) (t : Tree JF)
    (h : Heap Obj) : Jl (HRes × Heap Obj) := do
  let X ← readInput h xa
  gradTreeH s m o xa (nGradients m X.nrows (scalarConstants t).length) 1 t h

/-- The pullback on heap objects. It reads `X` and `dY`, recomputes the
gradient, overwrites it with NaN by `set_invalid!` when incomplete, and
allocates the constant gradient (`fill_similar` or `sum`) and the input
gradient (broadcast), src/ChainRules.jl:57-81. Returns the identities of
`dtree.gradient` and `dX`. -/
def pullbackH (o : DEnum) (t : Tree JF) (xa ya : Nat) (h : Heap Obj) :
    Jl ((Nat × Nat) × Heap Obj) := do
  let X ← readInput h xa
  let dY ← readVec h ya
  let (res, h1) ← evalGradH .dense .both o xa t h
  let g ← readGrad h1 res
  let (a, h2) ← (if res.complete then pure (g.gradient, h1) else do
      let a := invalidateMatrix g.gradient
      let h2 ← h1.write res.ga (.mat a)
      pure (a, h2))
  let constants ← constantPullback X.nrows a dY
  let features ← featurePullback X.nrows a dY
  let p := h2.alloc (.vec constants)
  let q := p.2.alloc (.mat features)
  pure ((p.1, q.1), q.2)

/-! ## Heap lemmas -/

theorem read_lt (h : Heap Obj) (a : Nat) (v : Obj) (hr : h.read a = .ok v) : a < h.next := by
  apply Classical.byContradiction
  intro hc
  have := h.fresh a (by omega)
  simp [Heap.read, this] at hr

theorem write_next (h h' : Heap Obj) (a : Nat) (v : Obj) (hw : h.write a v = .ok h') :
    h'.next = h.next := by
  unfold Heap.write at hw
  split at hw
  · cases hw
  · cases hw; rfl

theorem write_exists (h : Heap Obj) (a : Nat) (v w : Obj) (hr : h.read a = .ok w) :
    ∃ h', h.write a v = .ok h' := by
  unfold Heap.write
  split
  · rename_i hn
    simp [Heap.read, hn] at hr
  · exact ⟨_, rfl⟩

theorem readInput_of (h : Heap Obj) (xa : Nat) (X : JMat JF) (hx : h.read xa = .ok (.input X)) :
    readInput h xa = .ok X := by
  simp [readInput, hx]

theorem allocPair_va (a b : Obj) (c : Bool) (h : Heap Obj) : (allocPair a b c h).1.va = h.next := rfl
theorem allocPair_ga (a b : Obj) (c : Bool) (h : Heap Obj) :
    (allocPair a b c h).1.ga = h.next + 1 := rfl
theorem allocPair_next (a b : Obj) (c : Bool) (h : Heap Obj) :
    (allocPair a b c h).2.next = h.next + 2 := rfl
theorem allocPair_read_va (a b : Obj) (c : Bool) (h : Heap Obj) :
    (allocPair a b c h).2.read h.next = .ok a := by
  simp [allocPair, Heap.alloc, Heap.read]
theorem allocPair_read_ga (a b : Obj) (c : Bool) (h : Heap Obj) :
    (allocPair a b c h).2.read (h.next + 1) = .ok b := by
  simp [allocPair, Heap.alloc, Heap.read]
theorem allocPair_keep (a b : Obj) (c : Bool) (h : Heap Obj) (p : Nat) (hp : p < h.next) :
    (allocPair a b c h).2.read p = h.read p := by
  have h1 : p ≠ h.next := by omega
  have h2 : p ≠ h.next + 1 := by omega
  simp [allocPair, Heap.alloc, Heap.read, h1, h2]

/-! ## Agreement with the pure mirror -/

/-- The heap result `res` holds the pure result `r` in two arrays allocated
during the call, and every object that existed before the call is unchanged. -/
structure Agree (h h' : Heap Obj) (res : HRes) (r : GradResult) : Prop where
  rv : h'.read res.va = .ok (.vec r.primal)
  rg : h'.read res.ga = .ok (.mat r.gradient)
  comp : res.complete = r.complete
  ne : res.va ≠ res.ga
  lov : h.next ≤ res.va
  log : h.next ≤ res.ga
  hiv : res.va < h'.next
  hig : res.ga < h'.next
  grow : h.next ≤ h'.next
  keep : ∀ p, p < h.next → h'.read p = h.read p

/-- Children's arrays read back as the pure children's results. -/
def Reads (h : Heap Obj) : List HRes → List GradResult → Prop
  | [], [] => True
  | res :: ress, r :: rs => h.read res.va = .ok (.vec r.primal) ∧
      h.read res.ga = .ok (.mat r.gradient) ∧ Reads h ress rs
  | _, _ => False

/-- Children's arrays occupy consecutive address ranges: each child's two
arrays are distinct and lie above every earlier child's arrays. -/
def Sep : Nat → List HRes → Nat → Prop
  | lo, [], hi => lo ≤ hi
  | lo, r :: rs, hi => ∃ mid, lo ≤ r.va ∧ lo ≤ r.ga ∧ r.va < mid ∧ r.ga < mid ∧ r.va ≠ r.ga ∧
      Sep mid rs hi

theorem sep_bounds : ∀ (ress : List HRes) (lo hi : Nat), Sep lo ress hi →
    lo ≤ hi ∧ ∀ r ∈ ress, lo ≤ r.va ∧ lo ≤ r.ga ∧ r.va < hi ∧ r.ga < hi := by
  intro ress
  induction ress with
  | nil => intro lo hi h; exact ⟨h, by simp⟩
  | cons r rs ih =>
    intro lo hi h
    obtain ⟨mid, h1, h2, h3, h4, _, hs⟩ := h
    obtain ⟨hmh, hall⟩ := ih mid hi hs
    refine ⟨by omega, ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · omega
    · have := hall r' hr'; omega

theorem sep_nodup : ∀ (ress : List HRes) (lo hi : Nat), Sep lo ress hi →
    (ress.flatMap fun r => [r.va, r.ga]).Nodup := by
  intro ress
  induction ress with
  | nil => intros; simp
  | cons r rs ih =>
    intro lo hi h
    obtain ⟨mid, _, _, h3, h4, hne, hs⟩ := h
    have hb := (sep_bounds rs mid hi hs).2
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨by simp [hne], ih mid hi hs, ?_⟩
    intro a ha b hb' hab
    obtain ⟨r', hr', hb2⟩ := List.mem_flatMap.1 hb'
    have := hb r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb2
    subst hab
    rcases ha with rfl | rfl <;> rcases hb2 with h | h <;> omega

theorem reads_keep (h1 h2 : Heap Obj) : ∀ (ress : List HRes) (rs : List GradResult) (lo hi : Nat),
    Reads h1 ress rs → Sep lo ress hi → (∀ p, p < hi → h2.read p = h1.read p) →
    Reads h2 ress rs := by
  intro ress
  induction ress with
  | nil => intro rs lo hi hr _ _; cases rs <;> simp_all [Reads]
  | cons r ress ih =>
    intro rs lo hi hr hs hk
    cases rs with
    | nil => simp [Reads] at hr
    | cons x xs =>
      obtain ⟨hv, hg, hrest⟩ := hr
      have hb := (sep_bounds _ lo hi hs).2 r (by simp)
      obtain ⟨mid, _, _, _, _, _, hs'⟩ := hs
      exact ⟨by rw [hk _ hb.2.2.1, hv], by rw [hk _ hb.2.2.2, hg], ih xs mid hi hrest hs' hk⟩

theorem reads_length : ∀ (ress : List HRes) (rs : List GradResult) (h : Heap Obj),
    Reads h ress rs → ress.length = rs.length := by
  intro ress
  induction ress with
  | nil => intro rs h hr; cases rs <;> simp_all [Reads]
  | cons r ress ih =>
    intro rs h hr
    cases rs with
    | nil => simp [Reads] at hr
    | cons x xs => simp [ih xs h hr.2.2]

theorem reads_mapM : ∀ (ress : List HRes) (rs : List GradResult) (h : Heap Obj),
    Reads h ress rs → (∀ r ∈ rs, r.complete = true) → ress.mapM (readGrad h) = .ok rs := by
  intro ress
  induction ress with
  | nil => intro rs h hr _; cases rs <;> simp_all [Reads]
  | cons r ress ih =>
    intro rs h hr hc
    cases rs with
    | nil => simp [Reads] at hr
    | cons x xs =>
      obtain ⟨hv, hg, hrest⟩ := hr
      have hx : x.complete = true := hc x (by simp)
      have hrs := ih xs h hrest (fun r hr => hc r (by simp [hr]))
      simp only [List.mapM_cons, readGrad, hv, hg, hBind, hrs, hPure]
      cases x
      simp_all

theorem collect_ok_cons (a : Jl GradResult) (as : List (Jl GradResult)) (rs : List GradResult)
    (h : collectChildren (a :: as) = .ok rs) : ∃ r, a = .ok r ∧
      ((r.complete = false ∧ rs = [r]) ∨
        (r.complete = true ∧ ∃ rs', collectChildren as = .ok rs' ∧
          ((∃ f, firstIncomplete rs' = some f ∧ rs = [f]) ∨
            (firstIncomplete rs' = none ∧ rs = r :: rs')))) := by
  cases ha : a with
  | error e => rw [ha] at h; cases h
  | ok r =>
    refine ⟨r, rfl, ?_⟩
    rw [ha] at h
    simp only [collectChildren, hBind] at h
    cases hc : r.complete
    · simp only [hc, Bool.not_false, ite_true, hPure] at h
      cases h
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false] at h
      cases hr : collectChildren as with
      | error e => rw [hr] at h; cases h
      | ok rs' =>
        rw [hr] at h
        simp only [hBind] at h
        refine Or.inr ⟨rfl, rs', rfl, ?_⟩
        cases hf : firstIncomplete rs' with
        | some f => rw [hf] at h; cases h; exact Or.inl ⟨f, rfl, rfl⟩
        | none => rw [hf] at h; cases h; exact Or.inr ⟨rfl, rfl⟩

theorem firstIncomplete_all (rs : List GradResult) (h : ∀ r ∈ rs, r.complete = true) :
    firstIncomplete rs = none := by
  simp only [firstIncomplete, List.find?_eq_none]
  intro r hr
  simp [h r hr]

theorem firstIncomplete_single' (r : GradResult) (h : r.complete = false) :
    firstIncomplete [r] = some r := by
  simp [firstIncomplete, List.find?, h]

/-- Result of the heap children loop relative to the pure one. -/
def ListAgree (h h' : Heap Obj) (res : HRes ⊕ List HRes) (rs : List GradResult) (n : Nat) :
    Prop :=
  h.next ≤ h'.next ∧ (∀ p, p < h.next → h'.read p = h.read p) ∧
  ((∃ e r, res = .inl e ∧ rs = [r] ∧ r.complete = false ∧ Agree h h' e r) ∨
   (∃ ress, res = .inr ress ∧ (∀ r ∈ rs, r.complete = true) ∧ rs.length = n ∧
      Reads h' ress rs ∧ Sep h.next ress h'.next))

theorem agree_trans_left (h h1 h2 : Heap Obj) (e : HRes) (r : GradResult)
    (hg : h.next ≤ h1.next) (hk : ∀ p, p < h.next → h1.read p = h.read p)
    (ha : Agree h1 h2 e r) : Agree h h2 e r :=
  ⟨ha.rv, ha.rg, ha.comp, ha.ne, by have := ha.lov; omega, by have := ha.log; omega, ha.hiv,
    ha.hig, by have := ha.grow; omega,
    fun p hp => by rw [ha.keep p (by omega), hk p hp]⟩

theorem listH_agree (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (xa : Nat) (ng : Nat) :
    ∀ (cs : List (Tree JF)),
      (∀ c ∈ cs, ∀ st h r, h.read xa = .ok (.input X) → gradTree s m o X ng st c = .ok r →
        ∃ res h', gradTreeH s m o xa ng st c h = .ok (res, h') ∧ Agree h h' res r) →
      ∀ st h rs, h.read xa = .ok (.input X) →
        collectChildren (gradTreeList s m o X ng st cs) = .ok rs →
        ∃ res h', gradListH s m o xa ng st cs h = .ok (res, h') ∧ ListAgree h h' res rs cs.length := by
  intro cs
  induction cs with
  | nil =>
    intro _ st h rs _ hc
    cases hc
    exact ⟨.inr [], h, rfl, Nat.le_refl _, fun _ _ => rfl,
      Or.inr ⟨[], rfl, by simp, rfl, trivial, Nat.le_refl _⟩⟩
  | cons c cs ih =>
    intro ihc st h rs hx hcol
    simp only [gradTreeList] at hcol
    obtain ⟨r1, hr1, hcase⟩ := collect_ok_cons _ _ rs hcol
    obtain ⟨res1, h1, hh1, ha1⟩ := ihc c (by simp) st h r1 hx hr1
    have hx1 : h1.read xa = .ok (.input X) := by
      rw [ha1.keep xa (read_lt h xa _ hx), hx]
    rcases hcase with ⟨hinc, rfl⟩ | ⟨hcomp, rs', hrest, hsub⟩
    · refine ⟨.inl res1, h1, ?_, ha1.grow, ha1.keep, Or.inl ⟨res1, r1, rfl, rfl, hinc, ha1⟩⟩
      simp only [gradListH, hh1, hBind, ha1.comp, hinc, Bool.not_false, ite_true, hPure]
    · obtain ⟨res2, h2, hh2, hg2, hk2, hcase2⟩ :=
        ih (fun c' hc' => ihc c' (by simp [hc'])) _ h1 rs' hx1 hrest
      have hgrow : h.next ≤ h2.next := by have := ha1.grow; omega
      have hkeep : ∀ p, p < h.next → h2.read p = h.read p := fun p hp => by
        rw [hk2 p (by have := ha1.grow; omega), ha1.keep p hp]
      rcases hcase2 with ⟨e, r, rfl, rfl, hinc, hae⟩ | ⟨ress, rfl, hall, hlen, hreads, hsep⟩
      · rcases hsub with ⟨f, hf, rfl⟩ | ⟨hf, _⟩
        · rw [firstIncomplete_single' r hinc] at hf
          cases hf
          exact ⟨.inl e, h2, by
            simp only [gradListH, hh1, hBind, ha1.comp, hcomp, Bool.not_true, Bool.false_eq_true,
              ite_false, hh2]; rfl, hgrow, hkeep,
            Or.inl ⟨e, r, rfl, rfl, hinc, agree_trans_left h h1 h2 e r ha1.grow ha1.keep hae⟩⟩
        · rw [firstIncomplete_single' r hinc] at hf; cases hf
      · rcases hsub with ⟨f, hf, _⟩ | ⟨_, rfl⟩
        · rw [firstIncomplete_all rs' hall] at hf; cases hf
        · refine ⟨.inr (res1 :: ress), h2, by
            simp only [gradListH, hh1, hBind, ha1.comp, hcomp, Bool.not_true, Bool.false_eq_true,
              ite_false, hh2]; rfl, hgrow, hkeep,
            Or.inr ⟨res1 :: ress, rfl, ?_, by simp [hlen], ?_, ?_⟩⟩
          · intro r hr
            rcases List.mem_cons.1 hr with rfl | hr
            · exact hcomp
            · exact hall r hr
          · refine ⟨by rw [hk2 _ ha1.hiv, ha1.rv], by rw [hk2 _ ha1.hig, ha1.rg], hreads⟩
          · exact ⟨h1.next, ha1.lov, ha1.log, ha1.hiv, ha1.hig, ha1.ne, hsep⟩

theorem leaf_agree (h : Heap Obj) (r0 : GradResult) :
    Agree h (allocPair (.vec (checkResult r0).primal) (.mat (checkResult r0).gradient)
      (checkResult r0).complete h).2
      (allocPair (.vec (checkResult r0).primal) (.mat (checkResult r0).gradient)
        (checkResult r0).complete h).1 (checkResult r0) :=
  ⟨by rw [allocPair_va, allocPair_read_va], by rw [allocPair_ga, allocPair_read_ga], rfl,
    by rw [allocPair_va, allocPair_ga]; omega, by rw [allocPair_va]; omega,
    by rw [allocPair_ga]; omega,
    by rw [allocPair_va, allocPair_next]; omega, by rw [allocPair_ga, allocPair_next]; omega,
    by rw [allocPair_next]; omega, fun p hp => allocPair_keep _ _ _ h p hp⟩

theorem gradTreeH_agree (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (xa : Nat)
    (ng : Nat) : ∀ (t : Tree JF), t.Representable → ∀ st h r, h.read xa = .ok (.input X) →
      gradTree s m o X ng st t = .ok r →
      ∃ res h', gradTreeH s m o xa ng st t h = .ok (res, h') ∧ Agree h h' res r := by
  intro t
  induction t using Tree.induction with
  | hc v =>
    intro _ st h r hx hr
    rw [gradTree_const] at hr
    cases h0 : grad_deg0_eval s m X.nrows ng (List.replicate X.ncols v) true (st % 65536) with
    | error e => rw [h0] at hr; cases hr
    | ok r0 =>
      rw [h0] at hr
      cases hr
      refine ⟨_, _, ?_, leaf_agree h r0⟩
      simp only [gradTreeH, readInput_of h xa X hx, hBind, h0, hPure]
  | hf k =>
    intro _ st h r hx hr
    rw [gradTree_feature] at hr
    cases hrow : X.row k with
    | error e => rw [hrow] at hr; cases hr
    | ok vals =>
      rw [hrow] at hr
      simp only [hBind] at hr
      cases h0 : grad_deg0_eval s m X.nrows ng vals.toList false k with
      | error e => rw [h0] at hr; cases hr
      | ok r0 =>
        rw [h0] at hr
        cases hr
        refine ⟨_, _, ?_, leaf_agree h r0⟩
        simp only [gradTreeH, readInput_of h xa X hx, hBind, hrow, h0, hPure]
  | hb idx cs ih =>
    intro hrep st h r hx hr
    simp only [Tree.Representable] at hrep
    rw [gradTree_branch] at hr
    cases hcol : collectChildren (gradTreeList s m o X ng st cs) with
    | error e => rw [hcol] at hr; cases hr
    | ok rs =>
      rw [hcol] at hr
      simp only [hBind] at hr
      obtain ⟨res, h1, hh1, hg1, hk1, hcase⟩ :=
        listH_agree s m o X xa ng cs (fun c hc => ih c hc (hrep.2 c hc)) st h rs hx hcol
      rcases hcase with ⟨e, r', rfl, rfl, hinc, hae⟩ | ⟨ress, rfl, hall, hlen, hreads, hsep⟩
      · rw [firstIncomplete_single' r' hinc] at hr
        cases hr
        refine ⟨e, h1, ?_, hae⟩
        simp only [gradTreeH, hh1, hBind, hPure]
      · rw [firstIncomplete_all rs hall] at hr
        dsimp only at hr
        cases hop : o.lookup cs.length idx with
        | none => rw [hop] at hr; cases hr
        | some op =>
          rw [hop] at hr
          dsimp only at hr
          cases hk : gradKernel op X.ncols rs with
          | error e => rw [hk] at hr; cases hr
          | ok out =>
            rw [hk] at hr
            cases hr
            have hx1 : h1.read xa = .ok (.input X) := by
              rw [hk1 xa (read_lt h xa _ hx), hx]
            have hrl := reads_length ress rs h1 hreads
            obtain ⟨res1, rest, rfl⟩ : ∃ res1 rest, ress = res1 :: rest := by
              cases ress with
              | nil => simp at hrl; omega
              | cons a b => exact ⟨a, b, rfl⟩
            obtain ⟨mid, hlov, hlog, hhiv, hhig, hne, hsep'⟩ := hsep
            have hhi := (sep_bounds rest mid h1.next hsep').1
            cases rs with
            | nil => simp [Reads] at hreads
            | cons r1 rs1 =>
            obtain ⟨hv1, hg1', _⟩ := id hreads
            obtain ⟨h2, hw2⟩ := write_exists h1 res1.va (.vec (checkResult out).primal) _ hv1
            have hg2 : h2.read res1.ga = .ok (.mat r1.gradient) := by
              unfold Heap.read Heap.write at *
              split at hw2
              · cases hw2
              · cases hw2; simpa [Ne.symm hne] using hg1'
            obtain ⟨h3, hw3⟩ := write_exists h2 res1.ga (.mat (checkResult out).gradient) _ hg2
            have hn2 := write_next _ _ _ _ hw2
            have hn3 := write_next _ _ _ _ hw3
            refine ⟨⟨res1.va, res1.ga, (checkResult out).complete⟩, h3, ?_, ?_⟩
            · simp only [gradTreeH, hh1, hBind, hop, readInput_of h1 xa X hx1,
                reads_mapM _ _ h1 hreads hall, hk, fusedWrite, hw2, hw3, hPure]
            · refine ⟨?_, Heap.read_write_same _ _ _ _ hw3, rfl, hne, hlov, hlog,
                by dsimp only; omega, by dsimp only; omega, by omega, ?_⟩
              · rw [Heap.read_write_other _ _ _ _ _ hw3 hne, Heap.read_write_same _ _ _ _ hw2]
              · intro p hp
                rw [Heap.read_write_other _ _ res1.ga p _ hw3 (Nat.ne_of_lt (show p < res1.ga by omega)),
                  Heap.read_write_other _ _ res1.va p _ hw2 (Nat.ne_of_lt (show p < res1.va by omega)), hk1 p hp]

/-! ## Registered properties -/

/-- For every well-formed tree, operator enum, input matrix object `X` (Array,
view or transpose: a view shares `X`'s object), storage kind and gradient mode,
`eval_grad_tree_array` returns its value and gradient in two distinct arrays
allocated during the call, holding exactly the results of the pure mirror
(so deriv-gradient-modes describes them). Neither aliases `X`, a view of `X`,
a constant, or any array that existed before the call (such as results of an
earlier call), and the call leaves every pre-existing object, including `X`,
unchanged, even though fused kernels overwrite child arrays in place. -/
def gradOutputsFresh : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat)
    (h : Heap Obj) (xa : Nat),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    h.read xa = .ok (.input X) →
    ∃ r res h', eval_grad_tree_array s m o X t = .ok r ∧ evalGradH s m o xa t h = .ok (res, h') ∧
      h'.read res.va = .ok (.vec r.primal) ∧ h'.read res.ga = .ok (.mat r.gradient) ∧
      res.complete = r.complete ∧ res.va ≠ res.ga ∧ h.next ≤ res.va ∧ h.next ≤ res.ga ∧
      ∀ p, p < h.next → h'.read p = h.read p

theorem gradOutputsFresh_proof : gradOutputsFresh := by
  intro s m o X t D h xa hwf hcap hx
  obtain ⟨r, hr, _⟩ := gradientModes_proof s m o X t D hwf hcap
  have hr' := hr
  unfold eval_grad_tree_array at hr'
  obtain ⟨res, h', hh, ha⟩ := gradTreeH_agree s m o X xa _ t (Tree.WF.representable t hwf)
    1 h r hx hr'
  refine ⟨r, res, h', hr, ?_, ha.rv, ha.rg, ha.comp, ha.ne, ha.lov, ha.log, ha.keep⟩
  simp only [evalGradH, readInput_of h xa X hx, hBind, hh]

/-- For every well-formed branch at the root, the children's value and
gradient arrays read by the in-place fused kernel are pairwise distinct
objects allocated during the call, so the kernel's in-place writes into the
first child's arrays never overwrite data it has yet to read, and never write
into `X` or a pre-existing array, src/EvaluateDerivative.jl:302-367. -/
def fusedChildrenDisjoint : Prop :=
  ∀ (s : Storage) (m : Mode) (o : DEnum) (X : JMat JF) (idx : Nat) (cs : List (Tree JF))
    (D : Nat) (h : Heap Obj) (xa : Nat),
    let t := Tree.branch idx cs
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    h.read xa = .ok (.input X) →
    ∃ res h', gradListH s m o xa (nGradients m X.nrows (scalarConstants t).length) 1 cs h =
        .ok (res, h') ∧
      ∀ ress, res = .inr ress → (ress.flatMap fun r => [r.va, r.ga]).Nodup ∧
        ∀ r ∈ ress, h.next ≤ r.va ∧ h.next ≤ r.ga

theorem fusedChildrenDisjoint_proof : fusedChildrenDisjoint := by
  intro s m o X idx cs D h xa
  dsimp only
  intro hwf hcap hx
  obtain ⟨r, hr, _⟩ := gradientModes_proof s m o X _ D hwf hcap
  unfold eval_grad_tree_array at hr
  rw [gradTree_branch] at hr
  have hrep := Tree.WF.representable _ hwf
  simp only [Tree.Representable] at hrep
  cases hcol : collectChildren (gradTreeList s m o X
      (nGradients m X.nrows (scalarConstants (.branch idx cs)).length) 1 cs) with
  | error e => rw [hcol] at hr; cases hr
  | ok rs =>
    obtain ⟨res, h', hh, _, _, hcase⟩ := listH_agree s m o X xa _ cs
      (fun c hc => gradTreeH_agree s m o X xa _ c (hrep.2 c hc)) 1 h rs hx hcol
    refine ⟨res, h', hh, ?_⟩
    intro ress hress
    rcases hcase with ⟨e, _, he, _⟩ | ⟨ress', hr', _, _, _, hsep⟩
    · rw [he] at hress; cases hress
    · rw [hr'] at hress
      cases hress
      exact ⟨sep_nodup _ _ _ hsep, fun r hr => by
        have := (sep_bounds _ _ _ hsep).2 r hr; exact ⟨this.1, this.2.1⟩⟩

/-- For every well-formed tree, operator enum, input matrix object `X` with at
least one sample and cotangent object `dY` with one entry per sample, the
pullback returns `dtree.gradient` and `dX` as two distinct arrays allocated
during the call, holding the pure pullback's results (deriv-pullback-end-to-end),
and leaves `X`, `dY` and every other pre-existing object unchanged; the
`set_invalid!` overwrite only touches the pullback's own gradient array,
src/ChainRules.jl:57-80. -/
def pullbackOutputsFresh : Prop :=
  ∀ (o : DEnum) (X : JMat JF) (t : Tree JF) (D : Nat) (dY : List JF) (dComplete : Bool)
    (h : Heap Obj) (xa ya : Nat),
    t.WF D o.nops X.nrows → X.nrows + (scalarConstants t).length ≤ 65535 →
    dY.length = X.ncols → 0 < X.ncols →
    h.read xa = .ok (.input X) → h.read ya = .ok (.vec dY) →
    ∃ res ca fa h', (EvalPullback.mk t X o).call dY dComplete = .ok res ∧
      pullbackH o t xa ya h = .ok ((ca, fa), h') ∧
      h'.read ca = .ok (.vec res.tree.gradient) ∧ h'.read fa = .ok (.mat res.features) ∧
      ca ≠ fa ∧ h.next ≤ ca ∧ h.next ≤ fa ∧ ∀ p, p < h.next → h'.read p = h.read p

theorem pullbackOutputsFresh_proof : pullbackOutputsFresh := by
  intro o X t D dY dComplete h xa ya hwf hcap hdy hns hx hy
  obtain ⟨res, hcall, _⟩ := pullbackEndToEnd_proof o X t D dY dComplete hwf hcap hdy hns
  obtain ⟨r, gres, h1, hr, hh1, hv1, hg1, hc1, hne1, hlv, hlg, hk1⟩ :=
    gradOutputsFresh_proof .dense .both o X t D h xa hwf hcap hx
  have hread : readGrad h1 gres = .ok ⟨r.primal, r.gradient, true⟩ := by
    simp [readGrad, hv1, hg1]
  have hya : readVec h ya = .ok dY := by simp [readVec, hy]
  have hcall' := hcall
  unfold EvalPullback.call at hcall'
  rw [hr] at hcall'
  simp only [hBind] at hcall'
  -- the gradient array after the optional set_invalid!
  obtain ⟨h2, hstep, hk2, hn2⟩ : ∃ h2, (if gres.complete then
        (pure (r.gradient, h1) : Jl (GradMatrix × Heap Obj)) else do
          let a := invalidateMatrix r.gradient
          let h2 ← h1.write gres.ga (.mat a)
          pure (a, h2)) =
        .ok (if r.complete then r.gradient else invalidateMatrix r.gradient, h2) ∧
      (∀ p, p < h.next → h2.read p = h.read p) ∧ h2.next = h1.next := by
    rw [hc1]
    cases hrc : r.complete
    · obtain ⟨h2, hw⟩ := write_exists h1 gres.ga (.mat (invalidateMatrix r.gradient)) _ hg1
      refine ⟨h2, by simp [hw], fun p hp => ?_, write_next _ _ _ _ hw⟩
      rw [Heap.read_write_other _ _ gres.ga p _ hw (Nat.ne_of_lt (show p < gres.ga by omega)), hk1 p hp]
    · exact ⟨h1, by simp, hk1, rfl⟩
  cases hcp : constantPullback X.nrows
      (if r.complete then r.gradient else invalidateMatrix r.gradient) dY with
  | error e => rw [hcp] at hcall'; cases hcall'
  | ok cs =>
    rw [hcp] at hcall'
    simp only [hBind] at hcall'
    cases hfp : featurePullback X.nrows
        (if r.complete then r.gradient else invalidateMatrix r.gradient) dY with
    | error e => rw [hfp] at hcall'; cases hcall'
    | ok fs =>
      rw [hfp] at hcall'
      simp only [hBind, hPure] at hcall'
      have hres := Except.ok.inj hcall'
      subst hres
      have hgrow : h.next ≤ h2.next := by
        have := (read_lt h1 gres.va _ hv1); omega
      refine ⟨_, h2.next, h2.next + 1, ((h2.alloc (.vec cs)).2.alloc (.mat fs)).2,
        hcall, ?_, by simp [Heap.alloc, Heap.read], by simp [Heap.alloc, Heap.read], by omega,
        by omega, by omega, ?_⟩
      · simp only [pullbackH, readInput_of h xa X hx, hBind, hya, hh1]
        rw [hread]
        simp only [hBind]
        rw [hstep]
        simp only [hBind, hcp, hfp, hPure]
        rfl
      · intro p hp
        have h1' : p ≠ h2.next := by omega
        have h2' : p ≠ h2.next + 1 := by omega
        simp only [Heap.alloc, Heap.read, h1', h2', ite_false] at *
        have := hk2 p hp
        simpa [Heap.read] using this

end DynExpr.Deriv
