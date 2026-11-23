import DynExpr.NoAlias.Core
import DynExpr.NodeUtils.Preallocation

namespace DynExpr.NoAlias
open DynExpr Graph

/-- Active source children match the degree (`src/Node.jl:75-91`). -/
def CopyIntoWF (g : Graph T) (r : Addr) : Prop :=
  ∀ x c, Reachable g r x → g.cells x = some c → c.children.length = c.degree

private def SlotRange (dest : List Addr) (lo hi x : Nat) : Prop :=
  ∃ i, lo ≤ i ∧ i < hi ∧ dest[i]? = some x

private def CopyFrame (g h : Graph T) (dest : List Addr) (lo hi : Nat) : Prop :=
  ∀ x, ¬ SlotRange dest lo hi x → h.cells x = g.cells x

mutual
  private inductive CopyTree (g : Graph T) (dest : List Addr) : Nat → Nat → Addr → Prop
    | node {lo mid r cs} : dest[mid]? = some r → kids g r = some cs →
        CopyForest g dest lo mid cs → CopyTree g dest lo (mid + 1) r
  private inductive CopyForest (g : Graph T) (dest : List Addr) : Nat → Nat → List Addr → Prop
    | nil {lo} : CopyForest g dest lo lo []
    | cons {lo mid hi r rs} : CopyTree g dest lo mid r → CopyForest g dest mid hi rs →
        CopyForest g dest lo hi (r :: rs)
end

private theorem slot_inj {dest : List Addr} (hn : dest.Nodup)
    {i j x : Nat} (hi : dest[i]? = some x) (hj : dest[j]? = some x) : i = j := by
  have bi := List.getElem?_eq_some_iff.mp hi
  have bj := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj hn).mp (bi.2.trans bj.2.symm)

private theorem range_mono {dest : List Addr} {l h l' h' x}
    (hl : l' ≤ l) (hh : h ≤ h') (hx : SlotRange dest l h x) :
    SlotRange dest l' h' x := by
  obtain ⟨i, hi, hj, hx⟩ := hx
  exact ⟨i, Nat.le_trans hl hi, Nat.lt_of_lt_of_le hj hh, hx⟩

private theorem range_disjoint {dest : List Addr} (hn : dest.Nodup) {l m h x}
    (ha : SlotRange dest l m x) (hb : SlotRange dest m h x) : False := by
  obtain ⟨i, _, hi, ha⟩ := ha
  obtain ⟨j, hj, _, hb⟩ := hb
  have := slot_inj hn ha hb
  omega

private theorem tree_bounds {g : Graph T} {dest lo hi r}
    (ht : CopyTree g dest lo hi r) : lo < hi :=
  CopyTree.rec (motive_1 := fun lo hi _ _ => lo < hi)
    (motive_2 := fun lo hi _ _ => lo ≤ hi)
    (fun _ _ _ ih => by omega) (by omega) (fun _ _ ih ih' => by omega) ht

private theorem forest_bounds {g : Graph T} {dest lo hi cs}
    (hf : CopyForest g dest lo hi cs) : lo ≤ hi :=
  CopyForest.rec (motive_1 := fun lo hi _ _ => lo < hi)
    (motive_2 := fun lo hi _ _ => lo ≤ hi)
    (fun _ _ _ ih => by omega) (by omega) (fun _ _ ih ih' => by omega) hf

mutual
  private theorem tree_transfer {g h : Graph T} {dest lo hi r}
      (ht : CopyTree g dest lo hi r)
      (hp : ∀ x, SlotRange dest lo hi x → h.cells x = g.cells x) :
      CopyTree h dest lo hi r := by
    cases ht with
    | @node lo mid r cs hs hk hf =>
      have hb := forest_bounds hf
      refine .node hs ?_ (forest_transfer hf ?_)
      · simp only [kids, hp r ⟨mid, hb, by omega, hs⟩]; exact hk
      · intro x hx; exact hp x (range_mono (Nat.le_refl _) (by omega) hx)
  termination_by (hi, 0)
  decreasing_by all_goals simp_wf; omega
  private theorem forest_transfer {g h : Graph T} {dest lo hi cs}
      (hf : CopyForest g dest lo hi cs)
      (hp : ∀ x, SlotRange dest lo hi x → h.cells x = g.cells x) :
      CopyForest h dest lo hi cs := by
    cases hf with
    | nil => exact .nil
    | cons ht hf =>
      have hb := tree_bounds ht
      have hc := forest_bounds hf
      exact .cons (tree_transfer ht (fun x hx => hp x (range_mono (by omega) hc hx)))
        (forest_transfer hf (fun x hx => hp x (range_mono (by omega) (Nat.le_refl _) hx)))
  termination_by (hi, cs.length + 1)
  decreasing_by
    all_goals simp_wf
    · have := forest_bounds hf; omega
    · simp_all only [List.length_cons]; omega
end

private theorem forest_append {g : Graph T} {dest lo mid hi as bs}
    (ha : CopyForest g dest lo mid as) (hb : CopyForest g dest mid hi bs) :
    CopyForest g dest lo hi (as ++ bs) := by
  exact CopyForest.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun lo mid as _ => ∀ hi bs, CopyForest g dest mid hi bs →
      CopyForest g dest lo hi (as ++ bs))
    (fun _ _ _ _ => True.intro)
    (fun _ _ hb => hb)
    (fun ht _ _ ih hi bs hb => .cons ht (ih hi bs hb)) ha hi bs hb

mutual
  private theorem tree_owned {g : Graph T} {dest lo hi r}
      (ht : CopyTree g dest lo hi r) {x} (hx : Reachable g r x) :
      SlotRange dest lo hi x := by
    cases ht with
    | @node lo mid r cs hs hk hf =>
      have hb := forest_bounds hf
      rcases reach_inv hx with rfl | ⟨c, b, hc, hmem, hx⟩
      · exact ⟨_, hb, by omega, hs⟩
      · have hcs : c.children = cs := by simpa [kids, hc] using hk
        rw [hcs] at hmem
        exact range_mono (Nat.le_refl _) (by omega) (forest_owned hf hmem hx)
  termination_by (hi, 0)
  decreasing_by all_goals simp_wf; omega
  private theorem forest_owned {g : Graph T} {dest lo hi cs}
      (hf : CopyForest g dest lo hi cs) {b x} (hb : b ∈ cs) (hx : Reachable g b x) :
      SlotRange dest lo hi x := by
    cases hf with
    | nil => simp at hb
    | cons ht hf =>
      have h1 := tree_bounds ht
      have h2 := forest_bounds hf
      rcases List.mem_cons.mp hb with rfl | hb
      · exact range_mono (Nat.le_refl _) h2 (tree_owned ht hx)
      · exact range_mono (by omega) (Nat.le_refl _) (forest_owned hf hb hx)
  termination_by (hi, cs.length + 1)
  decreasing_by
    all_goals simp_wf
    · have := forest_bounds hf; omega
    · simp_all only [List.length_cons]; omega
end

private def ForestGood (g : Graph T) (cs : List Addr) : Prop :=
  cs.Nodup ∧ (∀ b ∈ cs, NoAlias g b) ∧
    (∀ b ∈ cs, ∀ b' ∈ cs, b ≠ b' → Disjoint g b b')

private theorem tree_noalias {g : Graph T} {dest lo hi r}
    (hn : dest.Nodup) (ht : CopyTree g dest lo hi r) : NoAlias g r := by
  apply CopyTree.rec (motive_1 := fun _ _ r _ => NoAlias g r)
    (motive_2 := fun _ _ cs _ => ForestGood g cs) ?_ ?_ ?_ ht
  · intro lo mid r cs hs hk hf ih
    obtain ⟨c, hc, hcs⟩ := cell_of_kids hk
    obtain ⟨hnd, hna, hdis⟩ := ih
    apply noAlias_node hc
    · simpa [hcs] using hnd
    · simpa [hcs] using hna
    · intro b hb hr
      rw [hcs] at hb
      obtain ⟨i, _, hi, hx⟩ := forest_owned hf hb hr
      have := slot_inj hn hx hs
      omega
    · simpa [hcs] using hdis
  · exact ⟨List.nodup_nil, by simp, by simp⟩
  · intro lo mid hi r rs ht hf hroot ih
    obtain ⟨hnd, hna, hdis⟩ := ih
    have cross : ∀ b ∈ rs, Disjoint g r b := by
      intro b hb x hx hy
      exact range_disjoint hn (tree_owned ht hx) (forest_owned hf hb hy)
    refine ⟨List.nodup_cons.mpr ⟨?_, hnd⟩, ?_, ?_⟩
    · intro hr; exact cross r hr r (reach_refl g r) (reach_refl g r)
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hroot
      · exact hna b hb
    · intro b hbmem b' hb'mem hne
      rcases List.mem_cons.mp hbmem with hbr | hbmem
      · subst b
        rcases List.mem_cons.mp hb'mem with hbr' | hb'mem
        · subst b'; exact False.elim (hne rfl)
        · exact cross b' hb'mem
      · rcases List.mem_cons.mp hb'mem with hbr' | hb'mem
        · subst b'; exact disjoint_symm (cross b hbmem)
        · exact hdis b hbmem b' hb'mem hne

private theorem read_cell {g : Graph T} {r c} (h : g.read r = .ok c) :
    g.cells r = some c := by
  unfold Heap.read at h
  cases hc : g.cells r <;> simp_all

private theorem copied_write {g h : Graph T} {a : Addr} {c : Cell T} {cs}
    (hc : c.degree = 0 → c.children = cs)
    (hw : NodeUtils.writeCopiedCell g a c cs = .ok h) :
    kids h a = some cs ∧ (∀ x, x ≠ a → h.cells x = g.cells x) := by
  unfold NodeUtils.writeCopiedCell at hw
  cases hr : g.read a with
  | error e => simp only [hr, NodeUtils.bindError, reduceCtorEq] at hw
  | ok old =>
    simp only [hr, NodeUtils.bindOk] at hw
    have hs := write_cells hw
    refine ⟨?_, hs.2.1⟩
    rw [kids_some hs.1]
    split
    · rename_i hz; simp [hc hz]
    · rfl

private theorem bind_if {A B : Type} (P : Prop) [Decidable P]
    (a b : Jl A) (f : A → Jl B) :
    (if P then a >>= f else b >>= f) = ((if P then a else b) >>= f) := by
  split <;> rfl
private theorem walk_layout {T : Type} (source : Graph T) (dest : List Addr)
    (hn : dest.Nodup) (fuel : Nat) :
    ∀ root out lo cache r out' hi cache', CopyIntoWF source root →
      NodeUtils.copyWalk source false dest fuel root out lo cache =
        .ok (r, out', hi, cache') →
      CopyTree out' dest lo hi r ∧ CopyFrame out out' dest lo hi := by
  induction fuel with
  | zero => intro root out lo cache r out' hi cache' _ he; simp [NodeUtils.copyWalk] at he
  | succ fuel ih =>
    intro root out lo cache r out' hi cache' hwf he
    simp only [NodeUtils.copyWalk, Bool.false_eq_true, ↓reduceIte] at he
    cases hc : source.read root with
    | error e => simp only [hc, NodeUtils.bindError, reduceCtorEq] at he
    | ok c =>
      have hcell := read_cell hc
      simp only [hc, NodeUtils.bindOk] at he
      let step := fun (st : List Addr × Graph T × Nat × List (Addr × Addr)) (a : Addr) => do
        let (b,h,j,m') ← NodeUtils.copyWalk source false dest fuel a st.2.1 st.2.2.1 st.2.2.2
        pure (st.1 ++ [b],h,j,m')
      rw [bind_if] at he
      change ((if c.degree = 0 then pure ([],out,lo,cache)
        else c.children.foldlM step ([],out,lo,cache)) >>= _) = _ at he
      have fold_safe : ∀ (xs : List Addr), (∀ a ∈ xs, CopyIntoWF source a) →
          ∀ as g j m bs h k m', CopyForest g dest lo j as → CopyFrame out g dest lo j →
          xs.foldlM step (as,g,j,m) = .ok (bs,h,k,m') →
          CopyForest h dest lo k bs ∧ CopyFrame out h dest lo k := by
        intro xs hxs
        induction xs with
        | nil =>
          intro as g j m bs h k m' hf hp heq
          simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at heq
          rcases heq with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨hf, hp⟩
        | cons a xs iht =>
          intro as g j m bs h k m' hf hp heq
          rw [List.foldlM_cons] at heq
          cases hwalk : NodeUtils.copyWalk source false dest fuel a g j m with
          | error e => simp only [step, hwalk, NodeUtils.bindError, reduceCtorEq] at heq
          | ok st =>
            rcases st with ⟨b, h1, j1, m1⟩
            have hwa := hxs a (by simp)
            obtain ⟨ht, hframe⟩ := ih a g j m b h1 j1 m1 hwa hwalk
            have hj := tree_bounds ht
            have hl := forest_bounds hf
            have hf' : CopyForest h1 dest lo j as := forest_transfer hf (by
              intro x hx
              exact hframe x (fun hy => range_disjoint hn hx hy))
            have hforest := forest_append hf' (.cons ht .nil)
            have hframe' : CopyFrame out h1 dest lo j1 := by
              intro x hx
              rw [hframe x (fun hy => hx (range_mono (by omega) (Nat.le_refl _) hy)),
                hp x (fun hy => hx (range_mono (Nat.le_refl _) (by omega) hy))]
            simp only [step, hwalk, NodeUtils.bindOk, pure, Except.pure] at heq
            exact iht (fun b hb => hxs b (by simp [hb]))
              (as ++ [b]) h1 j1 m1 bs h k m' hforest hframe' heq
      cases hphase : (if c.degree = 0 then
          (pure ([],out,lo,cache) : Jl (List Addr × Graph T × Nat × List (Addr × Addr)))
        else c.children.foldlM step ([],out,lo,cache)) with
      | error e => simp only [hphase, NodeUtils.bindError, reduceCtorEq] at he
      | ok st =>
        rcases st with ⟨cs, g, j, m⟩
        have hforest : CopyForest g dest lo j cs ∧ CopyFrame out g dest lo j := by
          by_cases hz : c.degree = 0
          · simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hphase
            rcases hphase with ⟨rfl, rfl, rfl, rfl⟩
            exact ⟨.nil, fun _ _ => rfl⟩
          · simp only [hz, ↓reduceIte] at hphase
            apply fold_safe c.children ?_ [] out lo cache cs g j m .nil (fun _ _ => rfl) hphase
            intro a ha x cx hx hcx
            exact hwf x cx (reach_trans (reach_mem hcell ha) hx) hcx
        have hleaf : c.degree = 0 → c.children = cs := by
          intro hz
          have hlen := hwf root c (reach_refl source root) hcell
          have hnils : c.children = [] := List.eq_nil_of_length_eq_zero (hlen.trans hz)
          simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hphase
          exact hnils.trans hphase.1
        rw [hphase] at he
        simp only [NodeUtils.bindOk] at he
        cases hslot : NodeUtils.destinationSlot dest j with
        | error e => simp only [hslot, NodeUtils.bindError, reduceCtorEq] at he
        | ok a =>
          have hs : dest[j]? = some a := by
            unfold NodeUtils.destinationSlot at hslot
            cases hx : dest[j]? <;> simp_all
          simp only [hslot, NodeUtils.bindOk] at he
          cases hwrite : NodeUtils.writeCopiedCell g a c cs with
          | error e => simp only [hwrite, NodeUtils.bindError, reduceCtorEq] at he
          | ok h =>
            simp only [hwrite, NodeUtils.bindOk, pure, Except.pure,
              Except.ok.injEq, Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨hk, hoff⟩ := copied_write hleaf hwrite
            have hb := forest_bounds hforest.1
            refine ⟨.node hs hk (forest_transfer hforest.1 ?_), ?_⟩
            · intro x hx
              apply hoff x
              intro hxa
              subst x
              obtain ⟨i, _, hi, hx⟩ := hx
              have := slot_inj hn hx hs
              omega
            · intro x hx
              calc
                h.cells x = g.cells x := hoff x (by
                  intro hxa; subst x; exact hx ⟨j, hb, by omega, hs⟩)
                _ = out.cells x := hforest.2 x (fun hy =>
                  hx (range_mono (Nat.le_refl _) (by omega) hy))

/-- Number of source-node occurrences traversed with this fuel. Shared references
are counted once per occurrence (src/base.jl:123-155, preserve_sharing=false). -/
def CopyIntoSize (source : Graph T) : Nat → Addr → Option Nat
  | 0, _ => none
  | fuel + 1, root => do
      let c ← source.cells root
      if c.children.length ≠ c.degree then none
      else if c.degree = 0 then some 1
      else do
        let ns ← c.children.mapM (CopyIntoSize source fuel)
        some (1 + ns.sum)

private def SlotsInitialized (g : Graph T) (dest : List Addr) : Prop :=
  ∀ a ∈ dest, (g.cells a).isSome

private theorem write_success {g : Graph T} {dest : List Addr} {a : Addr}
    (hi : SlotsInitialized g dest) (ha : a ∈ dest) (c : Cell T) (cs : List Addr) :
    ∃ h, NodeUtils.writeCopiedCell g a c cs = .ok h ∧ SlotsInitialized h dest := by
  have he := hi a ha
  cases hc : g.cells a with
  | none => simp [hc] at he
  | some old =>
    let v := if c.degree = 0 then c else
      {old with degree := cs.length, op := c.op, children := cs}
    have hw : ∃ h, g.write a v = .ok h := by
      unfold Heap.write
      simp only [hc, reduceCtorEq]
      exact ⟨_, rfl⟩
    obtain ⟨h, hw⟩ := hw
    refine ⟨h, ?_, ?_⟩
    · simpa only [NodeUtils.writeCopiedCell, Heap.read, hc, NodeUtils.bindOk] using hw
    · intro x hx
      by_cases hxa : x = a
      · subst x; rw [(write_cells hw).1]; rfl
      · rw [(write_cells hw).2.1 x hxa]; exact hi x hx

private theorem walk_success {T : Type} (source : Graph T) (dest : List Addr) (fuel : Nat) :
    ∀ root n out j cache, CopyIntoSize source fuel root = some n →
      SlotsInitialized out dest → j + n ≤ dest.length →
      ∃ r h, NodeUtils.copyWalk source false dest fuel root out j cache =
        .ok (r,h,j+n,cache) ∧ SlotsInitialized h dest := by
  induction fuel with
  | zero => intro root n out j cache hc; simp only [CopyIntoSize, reduceCtorEq] at hc
  | succ fuel ih =>
    intro root n out j cache hsize hinit hcap
    simp only [CopyIntoSize] at hsize
    cases hc : source.cells root with
    | none => simp only [hc, bind, Option.bind, reduceCtorEq] at hsize
    | some c =>
      simp only [hc, bind, Option.bind] at hsize
      by_cases hdeg : c.children.length = c.degree
      · simp only [hdeg, ne_eq, not_true_eq_false, ↓reduceIte] at hsize
        let step := fun (st : List Addr × Graph T × Nat × List (Addr × Addr)) (a : Addr) => do
          let (b,h,k,m) ← NodeUtils.copyWalk source false dest fuel a st.2.1 st.2.2.1 st.2.2.2
          pure (st.1 ++ [b],h,k,m)
        have fold_success : ∀ (xs : List Addr) (ns : List Nat), xs.mapM (CopyIntoSize source fuel) = some ns →
            ∀ as g k, SlotsInitialized g dest → k + ns.sum ≤ dest.length →
            ∃ bs h, xs.foldlM step (as,g,k,cache) = .ok (bs,h,k+ns.sum,cache) ∧
              SlotsInitialized h dest := by
          intro xs
          induction xs with
          | nil =>
            intro ns hn as g k hg _
            simp only [List.mapM_nil, pure, Option.some.injEq] at hn
            subst ns
            exact ⟨as,g,by simp only [List.foldlM_nil, List.sum_nil, Nat.add_zero]; rfl,hg⟩
          | cons a xs iht =>
            intro ns hn as g k hg hcap'
            simp only [List.mapM_cons] at hn
            cases ha : CopyIntoSize source fuel a with
            | none => simp only [ha, bind, Option.bind, reduceCtorEq] at hn
            | some na =>
              cases hns : xs.mapM (CopyIntoSize source fuel) with
              | none => simp only [ha, hns, bind, Option.bind, reduceCtorEq] at hn
              | some ns' =>
                simp only [ha, hns, bind, Option.bind, pure, Option.some.injEq] at hn
                subst ns
                obtain ⟨b,h,hwalk,hih⟩ := ih a na g k cache ha hg (by
                  simp only [List.sum_cons] at hcap'; omega)
                obtain ⟨bs,h',hfold,hih'⟩ := iht ns' hns (as++[b]) h (k+na) hih (by
                  simp only [List.sum_cons] at hcap'; omega)
                refine ⟨bs,h',?_,hih'⟩
                simp only [List.foldlM_cons, step, hwalk, pure, Except.pure, NodeUtils.bindOk]
                simpa only [step, pure, Except.pure, List.sum_cons, Nat.add_assoc] using hfold
        have finish : ∀ cs g k, SlotsInitialized g dest → k < dest.length →
            ∃ r h, (do
              let r ← NodeUtils.destinationSlot dest k
              let h ← NodeUtils.writeCopiedCell g r c cs
              pure (r,h,k+1,cache)) = .ok (r,h,k+1,cache) ∧ SlotsInitialized h dest := by
          intro cs g k hg hk
          let a := dest[k]
          have hslot : NodeUtils.destinationSlot dest k = .ok a := by
            simp only [NodeUtils.destinationSlot, List.getElem?_eq_getElem hk]
            rfl
          obtain ⟨h,hw,hih⟩ := write_success hg (List.getElem_mem hk) c cs
          change NodeUtils.writeCopiedCell g a c cs = .ok h at hw
          exact ⟨a,h,by simp only [hslot, NodeUtils.bindOk, hw]; rfl,hih⟩
        by_cases hz : c.degree = 0
        · simp only [hz, ↓reduceIte, Option.some.injEq] at hsize
          subst n
          obtain ⟨a,h,hw,hi⟩ := finish [] out j hinit (by omega)
          refine ⟨a,h,?_,hi⟩
          simpa only [NodeUtils.copyWalk, Bool.false_eq_true, ↓reduceIte, Heap.read, hc,
            pure, Except.pure, NodeUtils.bindOk, hz] using hw
        · simp only [hz, ↓reduceIte] at hsize
          cases hns : c.children.mapM (CopyIntoSize source fuel) with
          | none => simp only [hns, reduceCtorEq] at hsize
          | some ns =>
            simp only [hns, Option.some.injEq] at hsize
            subst n
            obtain ⟨cs,g,hfold,hg⟩ := fold_success c.children ns hns [] out j hinit (by omega)
            obtain ⟨a,h,hw,hi⟩ := finish cs g (j+ns.sum) hg (by omega)
            refine ⟨a,h,?_,hi⟩
            simp only [NodeUtils.copyWalk, Bool.false_eq_true, ↓reduceIte, Heap.read, hc,
              NodeUtils.bindOk, hz]
            change (List.foldlM step ([],out,j,cache) c.children >>= _) = _
            rw [hfold]
            simp only [NodeUtils.bindOk]
            simpa only [Nat.add_comm 1 ns.sum, Nat.add_assoc] using hw
      · simp only [hdeg, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq] at hsize

/-- Decoding a source tree gives its exact occurrence budget for copying. -/
theorem copyIntoSize_of_unfold {T : Type} (source : Graph T) (fuel : Nat) :
    ∀ root (t : Tree T), source.unfold fuel root = some t →
      CopyIntoSize source fuel root = some t.size := by
  induction fuel with
  | zero => intro root t hu; simp only [Graph.unfold, reduceCtorEq] at hu
  | succ fuel ih =>
    intro root t hu
    simp only [Graph.unfold] at hu
    cases hc : source.cells root with
    | none => simp only [hc, bind, Option.bind, reduceCtorEq] at hu
    | some c =>
      simp only [hc, bind, Option.bind] at hu
      simp only [CopyIntoSize, hc, bind, Option.bind]
      by_cases hd : c.children.length = c.degree
      · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte] at hu ⊢
        by_cases hz : c.degree = 0
        · simp only [hz, ↓reduceIte] at hu ⊢
          cases hb : c.constant with
          | false =>
            simp only [hb, Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at hu
            subst t; simp only [Tree.size]
          | true =>
            simp only [hb, ↓reduceIte] at hu
            cases hv : c.val with
            | none => simp only [hv, reduceCtorEq] at hu
            | some v =>
              simp only [hv, pure, Option.some.injEq] at hu
              subst t; simp only [Tree.size]
        · simp only [hz, ↓reduceIte] at hu ⊢
          have hm : ∀ (xs : List Addr) (ts : List (Tree T)), xs.mapM (source.unfold fuel) = some ts →
              xs.mapM (CopyIntoSize source fuel) = some (ts.map Tree.size) := by
            intro xs
            induction xs with
            | nil =>
              intro ts he
              simp only [List.mapM_nil, pure, Option.some.injEq] at he
              subst ts; rfl
            | cons a xs iht =>
              intro ts he
              simp only [List.mapM_cons] at he
              cases ha : source.unfold fuel a with
              | none => simp only [ha, bind, Option.bind, reduceCtorEq] at he
              | some ta =>
                cases hs : xs.mapM (source.unfold fuel) with
                | none => simp only [ha, hs, bind, Option.bind, reduceCtorEq] at he
                | some ts' =>
                  simp only [ha, hs, bind, Option.bind, pure, Option.some.injEq] at he
                  subst ts
                  simp only [List.mapM_cons, ih a ta ha, iht ts' hs, bind, Option.bind,
                    pure, List.map_cons]
          cases hs : c.children.mapM (source.unfold fuel) with
          | none => simp only [hs, reduceCtorEq] at hu
          | some ts =>
            simp only [hs, pure, Option.some.injEq] at hu
            subst t
            rw [hm c.children ts hs]
            simp only [Tree.size]
      · simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte, reduceCtorEq] at hu

/-- Adequate initialized destination storage guarantees plain copying succeeds,
including sources with shared child references. -/
theorem copyInto_success {T : Type} (source out : Graph T) (dest : List Addr)
    (fuel root : Nat) (t : Tree T) (hu : source.unfold fuel root = some t)
    (hi : ∀ a ∈ dest, (out.cells a).isSome) (hcap : t.size ≤ dest.length) :
    ∃ r h, NodeUtils.copyInto source false dest out fuel root = .ok (r,h,t.size,[]) ∧
      (∀ a ∈ dest, (h.cells a).isSome) := by
  obtain ⟨r,h,he,hinit⟩ := walk_success source dest fuel root t.size out 0 []
    (copyIntoSize_of_unfold source fuel root t hu) hi (by omega)
  exact ⟨r,h,by simpa only [NodeUtils.copyInto, Nat.zero_add] using he,hinit⟩


/-- The walk consumes a consecutive destination interval from any starting cursor. -/
def copy_walk_noalias : Prop :=
  ∀ (T : Type) (source out : Graph T) (dest : List Addr)
    (fuel root j : Nat) (t : Tree T) (cache : List (Addr × Addr)),
    dest.Nodup → CopyIntoWF source root → source.unfold fuel root = some t →
    (∀ a ∈ dest, (out.cells a).isSome) → j + t.size ≤ dest.length →
    ∃ r out', NodeUtils.copyWalk source false dest fuel root out j cache =
      .ok (r,out',j+t.size,cache) ∧ j < j+t.size ∧ NoAlias out' r ∧
      (∀ x, Reachable out' r x → ∃ i, j ≤ i ∧ i < j+t.size ∧ dest[i]? = some x) ∧
      (∀ x, (¬ ∃ i, j ≤ i ∧ i < j+t.size ∧ dest[i]? = some x) → out'.cells x = out.cells x) ∧
      (∀ (i k x : Nat), dest[i]? = some x → dest[k]? = some x → i = k)

theorem copy_walk_noalias_holds : copy_walk_noalias := by
  intro T source out dest fuel root j t cache hn hwf hu hinit hcap
  obtain ⟨r,out',he,_⟩ := walk_success source dest fuel root t.size out j cache
    (copyIntoSize_of_unfold source fuel root t hu) hinit hcap
  obtain ⟨ht,hp⟩ := walk_layout source dest hn fuel root out j cache r out' (j+t.size) cache hwf he
  exact ⟨r,out',he,tree_bounds ht,tree_noalias hn ht,fun _ hx => tree_owned ht hx,hp,
    fun _ _ _ hi hk => slot_inj hn hi hk⟩

/-- Plain-node preallocated copies have unique paths, occupy only consumed slots,
and preserve every cell outside those slots (src/NodePreallocation.jl:35-66). -/
def copy_into_noalias : Prop :=
  ∀ (T : Type) (source out : Graph T) (dest : List Addr) (fuel root : Nat) (t : Tree T),
    dest.Nodup → CopyIntoWF source root → source.unfold fuel root = some t →
    (∀ a ∈ dest, (out.cells a).isSome) → t.size ≤ dest.length →
    ∃ r out' cursor cache,
      NodeUtils.copyInto source false dest out fuel root = .ok (r,out',cursor,cache) ∧
      cursor = t.size ∧ NoAlias out' r ∧ (∀ x, Reachable out' r x → x ∈ dest.take cursor) ∧
      (∀ x, x ∉ dest.take cursor → out'.cells x = out.cells x)

private theorem range_take {dest : List Addr} {hi x} (hx : SlotRange dest 0 hi x) :
    x ∈ dest.take hi := by
  obtain ⟨i, _, hi', hx⟩ := hx
  apply List.mem_of_getElem? (i := i)
  simpa only [List.getElem?_take, hi', ↓reduceIte] using hx

theorem copy_into_noalias_holds : copy_into_noalias := by
  intro T source out dest fuel root t hn hwf hu hinit hcap
  obtain ⟨r,out',he,_⟩ := copyInto_success source out dest fuel root t hu hinit hcap
  obtain ⟨ht,hp⟩ := walk_layout source dest hn fuel root out 0 [] r out' t.size [] hwf he
  exact ⟨r,out',t.size,[],he,rfl,tree_noalias hn ht,fun _ hx => range_take (tree_owned ht hx),
    fun x hx => hp x (fun hy => hx (range_take hy))⟩

example : (NodeUtils.emptySlots 1).1.Nodup ∧ CopyIntoWF (NodeUtils.sourceLeaf 7) 0 ∧
    (NodeUtils.sourceLeaf 7).unfold 1 0 = some (.const 7) ∧
    (∀ a ∈ (NodeUtils.emptySlots 1).1, ((NodeUtils.emptySlots 1).2.cells a).isSome) ∧
    1 ≤ (NodeUtils.emptySlots 1).1.length := by
  refine ⟨by simp [NodeUtils.emptySlots, NodeUtils.allocateContainer, Heap.alloc, Heap.empty],
    ?_, rfl, ?_, by decide⟩
  · intro x c _ hc
    by_cases hx : x = 0
    · subst x
      simp only [NodeUtils.sourceLeaf, Heap.alloc, Heap.empty, ↓reduceIte, Option.some.injEq] at hc
      subst c; rfl
    · simp [NodeUtils.sourceLeaf, Heap.alloc, Heap.empty, hx] at hc
  · intro a ha
    simp only [NodeUtils.emptySlots, NodeUtils.allocateContainer, Heap.alloc, Heap.empty,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    subst a; rfl

example : (NodeUtils.emptySlots 2).1.Nodup ∧ CopyIntoWF (NodeUtils.sourceLeaf 7) 0 ∧
    (NodeUtils.sourceLeaf 7).unfold 1 0 = some (.const 7) ∧
    (∀ a ∈ (NodeUtils.emptySlots 2).1, ((NodeUtils.emptySlots 2).2.cells a).isSome) ∧
    1 + 1 ≤ (NodeUtils.emptySlots 2).1.length := by
  refine ⟨by simp [NodeUtils.emptySlots, NodeUtils.allocateContainer, Heap.alloc, Heap.empty],
    ?_, rfl, ?_, by decide⟩
  · intro x c _ hc
    by_cases hx : x = 0
    · subst x
      simp only [NodeUtils.sourceLeaf, Heap.alloc, Heap.empty, ↓reduceIte, Option.some.injEq] at hc
      subst c; rfl
    · simp [NodeUtils.sourceLeaf, Heap.alloc, Heap.empty, hx] at hc
  · intro a ha
    simp only [NodeUtils.emptySlots, NodeUtils.allocateContainer, Heap.alloc, Heap.empty,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
end DynExpr.NoAlias
