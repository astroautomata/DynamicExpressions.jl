import DynExpr.Eval.Top
import DynExpr.Eval.AliasProofs

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

private abbrev GoodTree (o : OpEnum T) (X : JMat T) (t : Tree T) : Prop :=
  ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t

private theorem feature_good (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (f : Nat) (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows) : GoodTree o X (.feature f) := by
  intro j hj
  have he := JMat.get?_eq X f (j + 1) hf1 hf2 (by omega) (by omega)
  simp only [AllValid]
  refine ⟨cv o X (.feature f) j, by simp [cv, vx, col, Tree.denote, he, Except.toOption], ?_⟩
  simp only [cv, vx, Tree.denote, col, he, Except.toOption, Option.getD_some]
  exact hX _ (Array.getElem_mem_toList _)

private theorem leaf_good (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (l : Tree T) (hl : LeafOK X l) (hv : isConstLeaf l = true → valid (leafVal l) = true) :
    GoodTree o X l := by
  cases l with
  | const v => intro j hj; simpa [AllValid, leafVal] using hv rfl
  | feature f => exact feature_good o X hX f hl.1 hl.2
  | branch _ _ => exact hl.elim

private theorem branch_av (o : OpEnum T) (x : Nat → Option T) (op : Nat)
    (cs : List (Tree T)) (g : List T → T) (hg : o.lookup cs.length op = some g)
    (hc : ∀ c ∈ cs, AllValid o x c) (hv : valid (g (cs.map (vx o x))) = true) :
    AllValid o x (.branch op cs) := by
  have hmap := mapM_opt_eq (Tree.denote o x) (vx o x) cs (fun c hc' => AllValid.some o x c (hc c hc'))
  simp only [AllValid]
  exact ⟨hc, g (cs.map (vx o x)), by simp [Tree.denote, hg, hmap], hv⟩

private theorem map_valid (hA : ArrayValidExact T) (n : Nat) (f : Nat → T)
    (hv : isValidArray ((List.range n).map f).toArray = true) :
    ∀ j, j < n → valid (f j) = true := by
  intro j hj
  apply (hA _).1 hv
  simp only [List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

private theorem post_sound (f : List T → T) (x : T) (hv : valid (post true f x) = true) :
    valid x = true ∧ valid (f [x]) = true := by
  cases hx : valid x <;> simp [post, hx] at hv ⊢
  exact hv

private theorem fused3_left_sound (f g : List T → T) (a b c : T)
    (hv : valid (fused3 .left true f g a b c) = true) :
    valid (g [a, b]) = true ∧ valid c = true ∧ valid (f [g [a, b], c]) = true := by
  cases hi : valid (g [a, b]) <;> cases hc : valid c <;> simp [fused3, hi, hc] at hv ⊢
  exact hv

private theorem fused3_right_sound (f g : List T → T) (a b c : T)
    (hv : valid (fused3 .right true f g a b c) = true) :
    valid a = true ∧ valid (g [b, c]) = true ∧ valid (f [a, g [b, c]]) = true := by
  cases ha : valid a <;> cases hi : valid (g [b, c]) <;> simp [fused3, ha, hi] at hv ⊢
  exact hv

private theorem retV_success (D : Nat) (X : JMat T) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (r : ResultOk T) (b : Buf T)
    (h : retV ⟨true, true, D⟩ X v k .none = .ok (r, b)) (hok : r.ok = true) :
    valid v = true ∧ k .none = .ok (r, b) := by
  cases hv : valid v with
  | false =>
    have he : (⟨JVec.fill X.ncols JlScalar.undef, false, .fresh⟩, Buf.none) = (r, b) := by
      simpa [retV, hv, getArray, nextId] using h
    have hf : false = r.ok := congrArg (fun p : ResultOk T × Buf T => p.1.ok) he
    have hf := hf.trans hok
    cases hf
  | true => exact ⟨rfl, by simpa [retV, hv] using h⟩

private theorem retVIf_success (D : Nat) (X : JMat T) (c : Bool) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (r : ResultOk T) (b : Buf T)
    (h : retVIf ⟨true, true, D⟩ X c v k .none = .ok (r, b)) (hok : r.ok = true) :
    k .none = .ok (r, b) := by
  unfold retVIf at h
  split at h
  · exact (retV_success D X v k r b h hok).2
  · exact h

private theorem result_canon (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hw : t.WF D o.nops X.nrows)
    (hv : GoodTree o X t) (r : ResultOk T) (b : Buf T)
    (h : evalT ⟨true, true, D⟩ o X t .none = .ok (r, b)) : r.x = canon o X t := by
  have hAs : ArrayValidSound T := fun a ha => (hA a).2 ha
  obtain ⟨_, _, hrun⟩ := evalT_valid ⟨true, true, D⟩ o X hAs hn t hw hv
  obtain ⟨id, b', he, hg⟩ := hrun 0 .none trivial
  have eq := Except.ok.inj (h.symm.trans he)
  exact congrArg (fun p : ResultOk T × Buf T => p.1.x) eq

omit [JlScalar T] in
private theorem false_flag (a r : ResultOk T) (b c : Buf T) (ha : a.ok = false)
    (hr : r.ok = true) (h : (Except.ok (a, b) : Jl _) = .ok (r, c)) : False := by
  have he := congrArg (fun p : ResultOk T × Buf T => p.1.ok) (Except.ok.inj h)
  rw [ha, hr] at he
  cases he

private theorem checked_success (D : Nat) (o : OpEnum T) (X : JMat T) (c : Tree T)
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T))
    (r : ResultOk T) (b : Buf T)
    (h : checked ⟨true, true, D⟩ (evalT ⟨true, true, D⟩ o X c) k .none = .ok (r, b))
    (hok : r.ok = true) :
    ∃ rc, evalT ⟨true, true, D⟩ o X c .none = .ok (rc, .none) ∧
      rc.ok = true ∧ isValidArray rc.x = true ∧ k rc.x rc.id .none = .ok (r, b) := by
  cases hc : evalT ⟨true, true, D⟩ o X c .none with
  | error e => simp [checked, hc] at h
  | ok a =>
    rcases a with ⟨rc, bc⟩
    have hb := (aliasFresh_of_ok ⟨true, true, D⟩ o X c rc bc hc).2
    subst bc
    cases ho : rc.ok with
    | false => exact False.elim (false_flag rc r .none b ho hok (by simpa [checked, hc, ho] using h))
    | true =>
      cases hv : isValidArray rc.x with
      | false => exact False.elim (false_flag ⟨rc.x, false, rc.id⟩ r .none b rfl hok
          (by simpa [checked, hc, ho, hv] using h))
      | true => exact ⟨rc, rfl, ho, hv, by simpa [checked, hc, ho, hv] using h⟩

omit [JlScalar T] in
private theorem map_result (n : Nat) (f : Nat → T) (id : Ident) (r : ResultOk T) (b : Buf T)
    (h : (Except.ok (⟨((List.range n).map f).toArray, true, id⟩, Buf.none) : Jl _) = .ok (r, b)) :
    r.x = ((List.range n).map f).toArray :=
  (congrArg (fun p : ResultOk T × Buf T => p.1.x) (Except.ok.inj h)).symm

private theorem deg1L1_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (f fl : List T → T) (l : Tree T) (hl : LeafOK X l) (hc : isConstLeaf l = false)
    (r : ResultOk T) (b : Buf T) (h : deg1L1 ⟨true, true, D⟩ X f fl l .none = .ok (r, b)) :
    GoodTree o X l ∧ r.x = ((List.range X.ncols).map
      (fun j => post true f (fl [cv o X l j]))).toArray := by
  have hgood := leaf_good o X hX l hl (by intro ht; rw [hc] at ht; cases ht)
  have hm := simdWrite_eq (JVec.fill X.ncols JlScalar.undef) X.ncols
    (fun j => do let v ← featureAt X (leafFeat l) j; pure (post true f (fl [v])))
    (fun j => post true f (fl [cv o X l j])) (by simp [JVec.fill]) (by
      intro j hj; simp [leaf_read o X l hl hc j hj])
  have he : (Except.ok (⟨((List.range X.ncols).map (fun j => post true f (fl [cv o X l j]))).toArray,
      true, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
    simp only [deg1L1, hc, Bool.false_eq_true, ↓reduceIte, leaf_chk X l hl hc, getArray,
      jl_ok_bind, nextId] at h
    rw [hm] at h
    simpa only [jl_ok_bind, jl_pure] using h
  exact ⟨hgood, map_result _ _ _ r b he⟩

private theorem deg1L2_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (f fl : List T → T) (l q : Tree T) (hl : LeafOK X l) (hq : LeafOK X q)
    (hnc : (isConstLeaf l && isConstLeaf q) = false) (r : ResultOk T) (b : Buf T)
    (h : deg1L2 ⟨true, true, D⟩ X f fl l q .none = .ok (r, b)) (hok : r.ok = true) :
    GoodTree o X l ∧ GoodTree o X q ∧ r.x = ((List.range X.ncols).map
      (fun j => post true f (fl [cv o X l j, cv o X q j]))).toArray := by
  cases hcl : isConstLeaf l <;> cases hcq : isConstLeaf q
  · have hgl := leaf_good o X hX l hl (by simp [hcl])
    have hgq := leaf_good o X hX q hq (by simp [hcq])
    have hm := simdWrite_eq (JVec.fill X.ncols JlScalar.undef) X.ncols
      (fun j => do
        let v1 ← featureAt X (leafFeat l) j
        let v2 ← featureAt X (leafFeat q) j
        pure (post true f (fl [v1, v2])))
      (fun j => post true f (fl [cv o X l j, cv o X q j])) (by simp [JVec.fill]) (by
        intro j hj; simp [leaf_read o X l hl hcl j hj, leaf_read o X q hq hcq j hj])
    have he : (Except.ok (⟨((List.range X.ncols).map (fun j => post true f (fl [cv o X l j, cv o X q j]))).toArray,
        true, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
      simp only [deg1L2, hcl, hcq, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        leaf_chk X l hl hcl, leaf_chk X q hq hcq, getArray, jl_ok_bind, nextId] at h
      rw [hm] at h
      simpa only [jl_ok_bind, jl_pure] using h
    exact ⟨hgl, hgq, map_result _ _ _ r b he⟩
  · simp only [deg1L2, hcl, hcq, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      leaf_chk X l hl hcl, jl_ok_bind] at h
    obtain ⟨hval, h⟩ := retV_success D X (leafVal q) _ r b h hok
    have hgl := leaf_good o X hX l hl (by simp [hcl])
    have hgq := leaf_good o X hX q hq (fun _ => hval)
    have hm := simdWrite_eq (JVec.fill X.ncols JlScalar.undef) X.ncols
      (fun j => do let v ← featureAt X (leafFeat l) j; pure (post true f (fl [v, leafVal q])))
      (fun j => post true f (fl [cv o X l j, cv o X q j])) (by simp [JVec.fill]) (by
        intro j hj; simp [leaf_read o X l hl hcl j hj, leaf_const o X q hcq j])
    have he : (Except.ok (⟨((List.range X.ncols).map (fun j => post true f (fl [cv o X l j, cv o X q j]))).toArray,
        true, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
      simp only [getArray, jl_ok_bind, nextId] at h
      rw [hm] at h
      simpa only [jl_ok_bind, jl_pure] using h
    exact ⟨hgl, hgq, map_result _ _ _ r b he⟩
  · simp only [deg1L2, hcl, hcq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨hval, h⟩ := retV_success D X (leafVal l) _ r b h hok
    have hgl := leaf_good o X hX l hl (fun _ => hval)
    have hgq := leaf_good o X hX q hq (by simp [hcq])
    have hm := simdWrite_eq (JVec.fill X.ncols JlScalar.undef) X.ncols
      (fun j => do let v ← featureAt X (leafFeat q) j; pure (post true f (fl [leafVal l, v])))
      (fun j => post true f (fl [cv o X l j, cv o X q j])) (by simp [JVec.fill]) (by
        intro j hj; simp [leaf_read o X q hq hcq j hj, leaf_const o X l hcl j])
    have he : (Except.ok (⟨((List.range X.ncols).map (fun j => post true f (fl [cv o X l j, cv o X q j]))).toArray,
        true, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
      simp only [leaf_chk X q hq hcq, getArray, jl_ok_bind, nextId] at h
      rw [hm] at h
      simpa only [jl_ok_bind, jl_pure] using h
    exact ⟨hgl, hgq, map_result _ _ _ r b he⟩
  · simp [hcl, hcq] at hnc


private theorem deg2L0R0_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (f : List T → T) (l q : Tree T) (hl : LeafOK X l) (hq : LeafOK X q)
    (hnc : (isConstLeaf l && isConstLeaf q) = false) (r : ResultOk T) (b : Buf T)
    (h : deg2L0R0 ⟨true, true, D⟩ X f l q .none = .ok (r, b)) (hok : r.ok = true) :
    GoodTree o X l ∧ GoodTree o X q ∧ r.x = ((List.range X.ncols).map
      (fun j => f [cv o X l j, cv o X q j])).toArray := by
  let identity := fun xs : List T => xs.headD JlScalar.undef
  have heq : deg2L0R0 ⟨true, true, D⟩ X f l q .none =
      deg1L2 ⟨true, true, D⟩ X identity f l q .none := by
    cases hcl : isConstLeaf l <;> cases hcq : isConstLeaf q
    · simp [deg2L0R0, deg1L2, hcl, hcq, getArray, post, identity, retV, nextId,
        leaf_chk X l hl hcl, leaf_chk X q hq hcq]
    · simp [deg2L0R0, deg1L2, hcl, hcq, getArray, post, identity, retV, nextId,
        leaf_chk X l hl hcl]
    · simp [deg2L0R0, deg1L2, hcl, hcq, getArray, post, identity, retV, nextId,
        leaf_chk X q hq hcq]
    · simp [hcl, hcq] at hnc
  obtain ⟨hgl, hgq, hx⟩ := deg1L2_shape D o X hX identity f l q hl hq hnc r b (heq.symm.trans h) hok
  exact ⟨hgl, hgq, by simpa [post, identity] using hx⟩

private theorem deg2R0_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (hn : 1 ≤ X.ncols) (f : List T → T) (c q : Tree T) (hq : LeafOK X q) (id : Ident)
    (r : ResultOk T) (b : Buf T)
    (h : deg2R0 ⟨true, true, D⟩ X f q (canon o X c) id .none = .ok (r, b)) (hok : r.ok = true) :
    GoodTree o X q ∧ r.x = ((List.range X.ncols).map
      (fun j => f [cv o X c j, cv o X q j])).toArray := by
  have hgood : GoodTree o X q := by
    apply leaf_good o X hX q hq
    intro hc
    simp only [deg2R0, hc, ↓reduceIte] at h
    exact (retV_success D X (leafVal q) _ r b h hok).1
  have he := deg2R0_ok ⟨true, true, D⟩ o X f c q hq hn
    (fun j hj => AllValid.valid o _ q (hgood j hj)) id .none
  exact ⟨hgood, map_result _ _ _ r b (he.symm.trans h)⟩

private theorem deg2L0_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (hn : 1 ≤ X.ncols) (f : List T → T) (q c : Tree T) (hq : LeafOK X q) (id : Ident)
    (r : ResultOk T) (b : Buf T)
    (h : deg2L0 ⟨true, true, D⟩ X f q (canon o X c) id .none = .ok (r, b)) (hok : r.ok = true) :
    GoodTree o X q ∧ r.x = ((List.range X.ncols).map
      (fun j => f [cv o X q j, cv o X c j])).toArray := by
  have hgood : GoodTree o X q := by
    apply leaf_good o X hX q hq
    intro hc
    simp only [deg2L0, hc, ↓reduceIte] at h
    exact (retV_success D X (leafVal q) _ r b h hok).1
  have he := deg2L0_ok ⟨true, true, D⟩ o X f q c hq hn
    (fun j hj => AllValid.valid o _ q (hgood j hj)) id .none
  exact ⟨hgood, map_result _ _ _ r b (he.symm.trans h)⟩

private theorem deg1L1_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hX : XFinite X) (op lop : Nat) (f fl : List T → T)
    (hf : o.lookup 1 op = some f) (hfl : o.lookup 1 lop = some fl)
    (l : Tree T) (hl : LeafOK X l) (hc : isConstLeaf l = false)
    (r : ResultOk T) (b : Buf T)
    (h : deg1L1 ⟨true, true, D⟩ X f fl l .none = .ok (r, b)) (hv : isValidArray r.x = true) :
    GoodTree o X (.branch op [.branch lop [l]]) := by
  obtain ⟨hgl, hx⟩ := deg1L1_shape D o X hX f fl l hl hc r b h
  rw [hx] at hv
  have hpost := map_valid hA _ _ hv
  intro j hj
  obtain ⟨hin, hout⟩ := post_sound f (fl [cv o X l j]) (hpost j hj)
  have hinner : AllValid o (col X (j + 1)) (.branch lop [l]) := by
    apply branch_av o _ lop [l] fl hfl
    · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst c; exact hgl j hj
    · simpa using hin
  apply branch_av o _ op [.branch lop [l]] f hf
  · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst c; exact hinner
  · have he := vx_branch o (col X (j + 1)) lop [l] fl hfl
      (fun c hc => AllValid.some o _ c (by simp at hc; subst c; exact hgl j hj))
    simpa [he] using hout

private theorem deg1L2_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hX : XFinite X) (op lop : Nat) (f fl : List T → T)
    (hf : o.lookup 1 op = some f) (hfl : o.lookup 2 lop = some fl)
    (l q : Tree T) (hl : LeafOK X l) (hq : LeafOK X q)
    (hnc : (isConstLeaf l && isConstLeaf q) = false) (r : ResultOk T) (b : Buf T)
    (h : deg1L2 ⟨true, true, D⟩ X f fl l q .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) :
    GoodTree o X (.branch op [.branch lop [l, q]]) := by
  obtain ⟨hgl, hgq, hx⟩ := deg1L2_shape D o X hX f fl l q hl hq hnc r b h hok
  rw [hx] at hv
  have hpost := map_valid hA _ _ hv
  intro j hj
  have hchildren : ∀ c ∈ [l, q], AllValid o (col X (j + 1)) c := by
    intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hgl j hj
    · exact hgq j hj
  obtain ⟨hin, hout⟩ := post_sound f (fl [cv o X l j, cv o X q j]) (hpost j hj)
  have hinner : AllValid o (col X (j + 1)) (.branch lop [l, q]) := by
    apply branch_av o _ lop [l, q] fl hfl hchildren
    simpa using hin
  apply branch_av o _ op [.branch lop [l, q]] f hf
  · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; subst c; exact hinner
  · have he := vx_branch o (col X (j + 1)) lop [l, q] fl hfl
      (fun c hc => AllValid.some o _ c (hchildren c hc))
    simpa [he] using hout

private theorem binary_array_good (o : OpEnum T) (X : JMat T) (hA : ArrayValidExact T)
    (op : Nat) (f : List T → T) (hf : o.lookup 2 op = some f) (l q : Tree T)
    (hl : GoodTree o X l) (hq : GoodTree o X q)
    (hv : isValidArray ((List.range X.ncols).map (fun j => f [cv o X l j, cv o X q j])).toArray = true) :
    GoodTree o X (.branch op [l, q]) := by
  have hpoint := map_valid hA _ _ hv
  intro j hj
  apply branch_av o _ op [l, q] f hf
  · intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hl j hj
    · exact hq j hj
  · simpa using hpoint j hj


private theorem branch0_shape (D : Nat) (o : OpEnum T) (X : JMat T) (hX : XFinite X)
    (f g : List T → T) (side : Side) (l1 l2 l3 : Tree T)
    (hl1 : LeafOK X l1) (hl2 : LeafOK X l2) (hl3 : LeafOK X l3)
    (hnc : ¬ (isConstLeaf l1 = true ∧ isConstLeaf l2 = true ∧ isConstLeaf l3 = true))
    (r : ResultOk T) (b : Buf T)
    (h : branch0 ⟨true, true, D⟩ X f g side l1 l2 l3 .none = .ok (r, b)) (hok : r.ok = true) :
    GoodTree o X l1 ∧ GoodTree o X l2 ∧ GoodTree o X l3 ∧
    r.x = ((List.range X.ncols).map (fun j =>
      fused3 side true f g (cv o X l1 j) (cv o X l2 j) (cv o X l3 j))).toArray := by
  simp only [branch0, getArray, jl_ok_bind] at h
  split at h
  · exact False.elim (false_flag ⟨JVec.fill X.ncols JlScalar.undef, false, .fresh⟩ r .none b rfl hok
      (by simpa [getArray, nextId] using h))
  · rename_i hbad
    have hv1 : isConstLeaf l1 = true → valid (leafVal l1) = true := by
      intro hc; cases hv : valid (leafVal l1)
      · simp [hc, hv] at hbad
      · rfl
    have hv2 : isConstLeaf l2 = true → valid (leafVal l2) = true := by
      intro hc; cases hv : valid (leafVal l2)
      · simp [hc, hv] at hbad
      · rfl
    have hv3 : isConstLeaf l3 = true → valid (leafVal l3) = true := by
      intro hc; cases hv : valid (leafVal l3)
      · simp [hc, hv] at hbad
      · rfl
    have hg1 := leaf_good o X hX l1 hl1 hv1
    have hg2 := leaf_good o X hX l2 hl2 hv2
    have hg3 := leaf_good o X hX l3 hl3 hv3
    have hleaves : Leaves3 o X l1 l2 l3 := ⟨hl1, hl2, hl3, hnc,
      fun j hj => AllValid.valid o _ l1 (hg1 j hj),
      fun j hj => AllValid.valid o _ l2 (hg2 j hj),
      fun j hj => AllValid.valid o _ l3 (hg3 j hj)⟩
    have hrows := hleaves.nrows
    let pick := fun (l : Tree T) (j : Nat) => do
      let a ← featureAt X (if isConstLeaf l = true then 1 else leafFeat l) j
      pure (if isConstLeaf l = true then (if isConstLeaf l = true then leafVal l else JlScalar.zero) else a)
    have hp : ∀ l, LeafOK X l → ∀ j, j < X.ncols → pick l (j + 1) = .ok (cv o X l j) := by
      intro l hl j hj
      exact pick_ok o X l hl hrows j hj
    have hm := simdWrite_eq (JVec.fill X.ncols JlScalar.undef) X.ncols
      (fun j => do
        let a ← pick l1 j
        let c ← pick l2 j
        let d ← pick l3 j
        pure (fused3 side true f g a c d))
      (fun j => fused3 side true f g (cv o X l1 j) (cv o X l2 j) (cv o X l3 j))
      (by simp [JVec.fill]) (by
        intro j hj
        simp [hp l1 hl1 j hj, hp l2 hl2 j hj, hp l3 hl3 j hj])
    simp only [pick_chk X l1 hl1 hrows, pick_chk X l2 hl2 hrows, pick_chk X l3 hl3 hrows,
      jl_ok_bind] at h
    have h' : (do
      let (cum, b') ← getArray (Buf.none : Buf T) X.ncols
      let out ← simdWrite cum X.ncols (fun j => do
        let a ← pick l1 j
        let c ← pick l2 j
        let d ← pick l3 j
        pure (fused3 side true f g a c d))
      pure ((⟨out, true, .fresh⟩ : ResultOk T), b')) = Except.ok (r, b) := by
      cases side <;> exact retVIf_success D X _ _ _ r b h hok
    simp only [getArray, jl_ok_bind] at h'
    rw [hm] at h'
    have he : (Except.ok (⟨((List.range X.ncols).map (fun j =>
        fused3 side true f g (cv o X l1 j) (cv o X l2 j) (cv o X l3 j))).toArray,
        true, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
      simpa only [jl_ok_bind, jl_pure] using h'
    exact ⟨hg1, hg2, hg3, map_result _ _ _ r b he⟩

private theorem branch0_left_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hX : XFinite X) (op lop : Nat) (f g : List T → T)
    (hf : o.lookup 2 op = some f) (hg : o.lookup 2 lop = some g)
    (l1 l2 l3 : Tree T) (hl1 : LeafOK X l1) (hl2 : LeafOK X l2) (hl3 : LeafOK X l3)
    (hnc : ¬ (isConstLeaf l1 = true ∧ isConstLeaf l2 = true ∧ isConstLeaf l3 = true))
    (r : ResultOk T) (b : Buf T)
    (h : branch0 ⟨true, true, D⟩ X f g .left l1 l2 l3 .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) :
    GoodTree o X (.branch op [.branch lop [l1, l2], l3]) := by
  obtain ⟨h1, h2, h3, hx⟩ := branch0_shape D o X hX f g .left l1 l2 l3 hl1 hl2 hl3 hnc r b h hok
  rw [hx] at hv
  have hpoint := map_valid hA _ _ hv
  intro j hj
  obtain ⟨hin, hleaf, hout⟩ := fused3_left_sound f g _ _ _ (hpoint j hj)
  have hchildren : ∀ c ∈ [l1, l2], AllValid o (col X (j + 1)) c := by
    intro c hc; simp at hc; rcases hc with rfl | rfl
    · exact h1 j hj
    · exact h2 j hj
  have hinner : AllValid o (col X (j + 1)) (.branch lop [l1, l2]) := by
    apply branch_av o _ lop [l1, l2] g hg hchildren
    simpa using hin
  apply branch_av o _ op [.branch lop [l1, l2], l3] f hf
  · intro c hc; simp at hc; rcases hc with rfl | rfl
    · exact hinner
    · exact h3 j hj
  · have he := vx_branch o (col X (j + 1)) lop [l1, l2] g hg
      (fun c hc => AllValid.some o _ c (hchildren c hc))
    simpa [he] using hout

private theorem branch0_right_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hX : XFinite X) (op lop : Nat) (f g : List T → T)
    (hf : o.lookup 2 op = some f) (hg : o.lookup 2 lop = some g)
    (l1 l2 l3 : Tree T) (hl1 : LeafOK X l1) (hl2 : LeafOK X l2) (hl3 : LeafOK X l3)
    (hnc : ¬ (isConstLeaf l1 = true ∧ isConstLeaf l2 = true ∧ isConstLeaf l3 = true))
    (r : ResultOk T) (b : Buf T)
    (h : branch0 ⟨true, true, D⟩ X f g .right l1 l2 l3 .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) :
    GoodTree o X (.branch op [l1, .branch lop [l2, l3]]) := by
  obtain ⟨h1, h2, h3, hx⟩ := branch0_shape D o X hX f g .right l1 l2 l3 hl1 hl2 hl3 hnc r b h hok
  rw [hx] at hv
  have hpoint := map_valid hA _ _ hv
  intro j hj
  obtain ⟨hleaf, hin, hout⟩ := fused3_right_sound f g _ _ _ (hpoint j hj)
  have hchildren : ∀ c ∈ [l2, l3], AllValid o (col X (j + 1)) c := by
    intro c hc; simp at hc; rcases hc with rfl | rfl
    · exact h2 j hj
    · exact h3 j hj
  have hinner : AllValid o (col X (j + 1)) (.branch lop [l2, l3]) := by
    apply branch_av o _ lop [l2, l3] g hg hchildren
    simpa using hin
  apply branch_av o _ op [l1, .branch lop [l2, l3]] f hf
  · intro c hc; simp at hc; rcases hc with rfl | rfl
    · exact h1 j hj
    · exact hinner
  · have he := vx_branch o (col X (j + 1)) lop [l2, l3] g hg
      (fun c hc => AllValid.some o _ c (hchildren c hc))
    simpa [he] using hout


private abbrev IndSound (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T) : Prop :=
  ∀ r b, evalT ⟨true, true, D⟩ o X t .none = .ok (r, b) →
    r.ok = true → isValidArray r.x = true → GoodTree o X t

private theorem array_good (o : OpEnum T) (X : JMat T) (hA : ArrayValidExact T)
    (op : Nat) (cs : List (Tree T)) (f : List T → T) (hf : o.lookup cs.length op = some f)
    (hc : ∀ c ∈ cs, GoodTree o X c)
    (hv : isValidArray ((List.range X.ncols).map (fun j => f (cs.map (fun c => cv o X c j)))).toArray = true) :
    GoodTree o X (.branch op cs) := by
  have hpoint := map_valid hA _ _ hv
  intro j hj
  exact branch_av o _ op cs f hf (fun c hm => hc c hm j hj) (hpoint j hj)

private theorem unfused1_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (op : Nat) (c : Tree T)
    (hw : c.WF D o.nops X.nrows) (ih : IndSound D o X c) (f : List T → T)
    (hf : o.lookup 1 op = some f) (r : ResultOk T) (b : Buf T)
    (h : unfused1 ⟨true, true, D⟩ (.ok f) (evalT ⟨true, true, D⟩ o X c) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [c]) := by
  unfold unfused1 at h
  obtain ⟨rc, hc, hco, hcv, hk⟩ := checked_success D o X c _ r b h hok
  have hgood := ih rc .none hc hco hcv
  have hcanon := result_canon D o X c hA hn hw hgood rc .none hc
  have he := degnEval_canon o X f [c] (by simp)
  rw [hcanon] at hk
  simp only [List.map_cons, List.map_nil] at he
  simp only [jl_ok_bind] at hk
  rw [he] at hk
  have hx := map_result _ _ _ r b (by simpa only [jl_ok_bind, jl_pure, List.map_cons, List.map_nil] using hk)
  rw [hx] at hv
  apply array_good o X hA op [c] f hf
  · intro a ha; simp at ha; subst a; exact hgood
  · simpa using hv

private theorem unfused2_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (op : Nat) (l q : Tree T)
    (hwl : l.WF D o.nops X.nrows) (hwq : q.WF D o.nops X.nrows)
    (ihl : IndSound D o X l) (ihq : IndSound D o X q) (f : List T → T)
    (hf : o.lookup 2 op = some f) (r : ResultOk T) (b : Buf T)
    (h : unfused2 ⟨true, true, D⟩ (.ok f) (evalT ⟨true, true, D⟩ o X l)
      (evalT ⟨true, true, D⟩ o X q) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [l, q]) := by
  unfold unfused2 at h
  obtain ⟨rl, hl, hlo, hlv, hk⟩ := checked_success D o X l _ r b h hok
  obtain ⟨rq, hq, hqo, hqv, hk⟩ := checked_success D o X q _ r b hk hok
  have hgl := ihl rl .none hl hlo hlv
  have hgq := ihq rq .none hq hqo hqv
  have hcl := result_canon D o X l hA hn hwl hgl rl .none hl
  have hcq := result_canon D o X q hA hn hwq hgq rq .none hq
  rw [hcl, hcq] at hk
  have he := degnEval_canon o X f [l, q] (by simp)
  simp only [List.map_cons, List.map_nil] at he
  simp only [jl_ok_bind] at hk
  rw [he] at hk
  have hx := map_result _ _ _ r b (by simpa only [jl_ok_bind, jl_pure, List.map_cons, List.map_nil] using hk)
  rw [hx] at hv
  exact binary_array_good o X hA op f hf l q hgl hgq hv

private theorem checked_R0_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hX : XFinite X) (op : Nat) (l q : Tree T)
    (hwl : l.WF D o.nops X.nrows) (ihl : IndSound D o X l) (hq : LeafOK X q)
    (f : List T → T) (hf : o.lookup 2 op = some f) (r : ResultOk T) (b : Buf T)
    (h : checked ⟨true, true, D⟩ (evalT ⟨true, true, D⟩ o X l)
      (fun xl id b => deg2R0 ⟨true, true, D⟩ X f q xl id b) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [l, q]) := by
  obtain ⟨rl, hl, hlo, hlv, hk⟩ := checked_success D o X l _ r b h hok
  have hgl := ihl rl .none hl hlo hlv
  have hcl := result_canon D o X l hA hn hwl hgl rl .none hl
  rw [hcl] at hk
  obtain ⟨hgq, hx⟩ := deg2R0_shape D o X hX hn f l q hq rl.id r b hk hok
  rw [hx] at hv
  exact binary_array_good o X hA op f hf l q hgl hgq hv

private theorem checked_L0_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hX : XFinite X) (op : Nat) (l q : Tree T)
    (hwq : q.WF D o.nops X.nrows) (ihq : IndSound D o X q) (hl : LeafOK X l)
    (f : List T → T) (hf : o.lookup 2 op = some f) (r : ResultOk T) (b : Buf T)
    (h : checked ⟨true, true, D⟩ (evalT ⟨true, true, D⟩ o X q)
      (fun xq id b => deg2L0 ⟨true, true, D⟩ X f l xq id b) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [l, q]) := by
  obtain ⟨rq, hq, hqo, hqv, hk⟩ := checked_success D o X q _ r b h hok
  have hgq := ihq rq .none hq hqo hqv
  have hcq := result_canon D o X q hA hn hwq hgq rq .none hq
  rw [hcq] at hk
  obtain ⟨hgl, hx⟩ := deg2L0_shape D o X hX hn f l q hl rq.id r b hk hok
  rw [hx] at hv
  exact binary_array_good o X hA op f hf l q hgl hgq hv



private def ScalarStatus (o : OpEnum T) (t : Tree T) (r : T × Bool) : Prop :=
  valid r.1 = r.2 ∧ (r.2 = true → ∀ x, AllValid o x t ∧ r.1 = vx o x t)

private def ScalarListStatus (o : OpEnum T) (cs : List (Tree T)) :
    (T × Bool) ⊕ List T → Prop
  | .inl r => r.2 = false ∧ valid r.1 = false
  | .inr vs => ∀ x, (∀ c ∈ cs, AllValid o x c) ∧ vs = cs.map (vx o x)

private theorem constEvalL_total (o : OpEnum T) (cs : List (Tree T))
    (hc : ∀ c ∈ cs, ∃ r, constEval o c = .ok r ∧ ScalarStatus o c r) :
    ∃ r, constEvalL o cs = .ok r ∧ ScalarListStatus o cs r := by
  induction cs with
  | nil => exact ⟨.inr [], rfl, fun _ => ⟨by simp, rfl⟩⟩
  | cons c cs ih =>
    obtain ⟨⟨v, ok⟩, hv, hs⟩ := hc c (by simp)
    simp only [ScalarStatus] at hs
    cases ok with
    | false => exact ⟨.inl (v, false), by simp [constEvalL, hv], rfl, hs.1⟩
    | true =>
      obtain ⟨r, hr, hsr⟩ := ih (by intro c hm; exact hc c (by simp [hm]))
      cases r with
      | inl r => exact ⟨.inl r, by simp [constEvalL, hv, hr], hsr⟩
      | inr vs =>
        refine ⟨.inr (v :: vs), by simp [constEvalL, hv, hr], ?_⟩
        intro x
        obtain ⟨hvx, he⟩ := hs.2 rfl x
        obtain ⟨hcs, hvs⟩ := hsr x
        exact ⟨by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hvx; exact hcs a ha,
          by simp [he, hvs]⟩

private theorem constEval_total (o : OpEnum T) (D nf : Nat) (t : Tree T) :
    t.WF D o.nops nf → isConstant t = true →
    ∃ r, constEval o t = .ok r ∧ ScalarStatus o t r := by
  induction t using Tree.induction with
  | hc v =>
    intro hw hcon
    exact ⟨(v, valid v), rfl, rfl, by
      intro hv x; exact ⟨by simpa [AllValid] using hv, by simp [vx, Tree.denote]⟩⟩
  | hf f => intro hw hcon; simp [isConstant] at hcon
  | hb op cs ih =>
    intro hw hcon
    simp only [Tree.WF] at hw
    have hcs : ∀ c ∈ cs, isConstant c = true := by
      have hl : isConstantL cs = true := hcon
      clear hw ih hcon
      induction cs with
      | nil => simp
      | cons c cs ihl =>
        simp only [isConstantL, Bool.and_eq_true] at hl
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hl.1
        · exact ihl hl.2 a ha
    obtain ⟨r, hr, hs⟩ := constEvalL_total o cs (by
      intro c hc; exact ih c hc (hw.2.2 c hc) (hcs c hc))
    cases r with
    | inl r =>
      refine ⟨r, by simp [constEval, hr], ?_⟩
      simp only [ScalarListStatus] at hs
      exact ⟨hs.2.trans hs.1.symm, by intro ht; rw [hs.1] at ht; cases ht⟩
    | inr vs =>
      obtain ⟨g, hg, hnif⟩ := nifOp_lookup o cs.length op hw.1.1 hw.2.1.1 hw.2.1.2.1
      have hidx := idxOp_lookup o cs.length op g hw.1.1 hg
      refine ⟨(g vs, valid (g vs)), by simp [constEval, hr, hnif, hidx], rfl, ?_⟩
      intro hv x
      obtain ⟨hchildren, hvs⟩ := hs x
      have hvx := vx_branch o x op cs g hg (fun c hc => AllValid.some o x c (hchildren c hc))
      have hden : (Tree.branch op cs).denote o x = some (g vs) := by
        simp [Tree.denote, hg, mapM_opt_eq (Tree.denote o x) (vx o x) cs
          (fun c hc => AllValid.some o x c (hchildren c hc)), hvs]
      exact ⟨by simp only [AllValid]; exact ⟨hchildren, g vs, hden, hv⟩, by rw [hvx, hvs]⟩

private theorem constPath_sound (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hw : t.WF D o.nops X.nrows) (hc : isConstant t = true)
    (r : ResultOk T) (b : Buf T) (h : constPath o X t .none = .ok (r, b))
    (hok : r.ok = true) : GoodTree o X t := by
  obtain ⟨⟨v, ok⟩, hr, hs⟩ := constEval_total o D X.nrows t hw hc
  cases ok with
  | false => exact False.elim (false_flag ⟨JVec.fill X.ncols JlScalar.undef, false, .fresh⟩ r .none b rfl hok
      (by simpa [constPath, hr, getArray, nextId] using h))
  | true => intro j hj; exact (hs.2 rfl (col X (j + 1))).1

private def ChildrenStatus (o : OpEnum T) (X : JMat T) (cs : List (Tree T)) :
    (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T) → Prop
  | .inl (r, b) => r.ok = false ∧ b = .none
  | .inr (xs, b) => b = .none ∧ xs.map Prod.fst = cs.map (canon o X) ∧
      ∀ c ∈ cs, GoodTree o X c

private theorem children_status (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (cs : List (Tree T))
    (hc : ∀ c ∈ cs, c.WF D o.nops X.nrows) (ih : ∀ c ∈ cs, IndSound D o X c)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T))
    (h : evalChildren ⟨true, true, D⟩ o X cs .none = .ok res) : ChildrenStatus o X cs res := by
  induction cs generalizing res with
  | nil => simp [evalChildren] at h; subst res; exact ⟨rfl, rfl, by simp⟩
  | cons c cs hi =>
    cases he : evalT ⟨true, true, D⟩ o X c .none with
    | error e => simp [evalChildren, he] at h
    | ok p =>
      rcases p with ⟨r, b⟩
      have hb := (aliasFresh_of_ok ⟨true, true, D⟩ o X c r b he).2
      subst b
      cases ho : r.ok with
      | false => simp [evalChildren, he, ho] at h; subst res; exact ⟨ho, rfl⟩
      | true =>
        cases hv : isValidArray r.x with
        | false => simp [evalChildren, he, ho, hv] at h; subst res; exact ⟨rfl, rfl⟩
        | true =>
          have hgood := ih c (by simp) r .none he ho hv
          have hcanon := result_canon D o X c hA hn (hc c (by simp)) hgood r .none he
          cases ht : evalChildren ⟨true, true, D⟩ o X cs .none with
          | error e => simp [evalChildren, he, ho, hv, ht] at h
          | ok p =>
            have hs := hi (by intro c hm; exact hc c (by simp [hm]))
              (by intro c hm; exact ih c (by simp [hm])) p (by simpa using ht)
            cases p with
            | inl a =>
              simp [evalChildren, he, ho, hv, ht] at h
              subst res
              exact hs
            | inr a =>
              rcases a with ⟨xs, b⟩
              obtain ⟨rfl, hxs, hvalid⟩ := hs
              simp [evalChildren, he, ho, hv, ht] at h
              subst res
              refine ⟨rfl, by simp [hcanon, hxs], ?_⟩
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hgood
              · exact hvalid a ha

private theorem degn_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (op : Nat) (cs : List (Tree T))
    (hw : (Tree.branch op cs).WF D o.nops X.nrows) (ih : ∀ c ∈ cs, IndSound D o X c)
    (r : ResultOk T) (b : Buf T)
    (h : (do let res ← evalChildren ⟨true, true, D⟩ o X cs .none
             degnFinish o cs.length op res) = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op cs) := by
  have hw' := hw
  simp only [Tree.WF] at hw'
  cases he : evalChildren ⟨true, true, D⟩ o X cs .none with
  | error e => simp [he] at h
  | ok res =>
    have hs := children_status D o X hA hn cs hw'.2.2 ih res he
    cases res with
    | inl p =>
      rcases p with ⟨rc, bc⟩
      obtain ⟨hco, rfl⟩ := hs
      exact False.elim (false_flag rc r .none b hco hok (by simpa [he, degnFinish] using h))
    | inr p =>
      rcases p with ⟨xs, bx⟩
      obtain ⟨rfl, hxs, hgood⟩ := hs
      obtain ⟨f, hf, hnif⟩ := nifOp_lookup o cs.length op hw'.1.1 hw'.2.1.1 hw'.2.1.2.1
      have hd := degnEval_canon o X f cs (by intro hnil; simp [hnil] at hw')
      simp only [he, jl_ok_bind, degnFinish, hnif, hxs, hd] at h
      have hx := map_result _ _ _ r b (by simpa only [jl_ok_bind, jl_pure] using h)
      rw [hx] at hv
      exact array_good o X hA op cs f hf hgood hv


private theorem deg1Dispatch_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hX : XFinite X) (op : Nat) (c : Tree T)
    (hw : (Tree.branch op [c]).WF D o.nops X.nrows) (hc : isConstant c = false)
    (ih : IndSound D o X c) (r : ResultOk T) (b : Buf T)
    (h : deg1Dispatch ⟨true, true, D⟩ o X op c (evalT ⟨true, true, D⟩ o X c) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [c]) := by
  have hw' := hw
  simp only [Tree.WF] at hw'
  have hcw := hw'.2.2 c (by simp)
  obtain ⟨f, hf, hnif⟩ := nifOp_lookup o 1 op (by omega) hw'.2.1.1 (by simpa using hw'.2.1.2.1)
  have hidx := idxOp_lookup o 1 op f (by omega) hf
  have hu : unfused1 ⟨true, true, D⟩ (.ok f) (evalT ⟨true, true, D⟩ o X c) .none = .ok (r, b) →
      GoodTree o X (.branch op [c]) := fun he => unfused1_sound D o X hA hn op c hcw ih f hf r b he hok hv
  unfold deg1Dispatch at h
  by_cases hlim : operatorLimit < (opsOf o 1).length
  · simp only [hlim, ↓reduceIte, hidx] at h
    exact hu h
  · simp only [hlim, ↓reduceIte, hnif, jl_ok_bind] at h
    rcases c with a | fidx | ⟨lop, cs⟩
    · exact hu h
    · exact hu h
    · rcases cs with _ | ⟨ll, _ | ⟨lr, _ | ⟨s, rest⟩⟩⟩
      · exact hu h
      · cases hleaf : isLeaf ll with
        | false => simp only [hleaf, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h; exact hu h
        | true =>
          simp only [hleaf, Bool.true_and, ↓reduceIte] at h
          simp only [Tree.WF] at hcw
          obtain ⟨fl, hfl, hnifl⟩ := nifOp_lookup o 1 lop (by omega) hcw.2.1.1 (by simpa using hcw.2.1.2.1)
          rw [hnifl] at h
          simp only [jl_ok_bind] at h
          have hll : LeafOK X ll := LeafOK.of_wf ll hleaf (hcw.2.2 ll (by simp))
          have hnc : isConstLeaf ll = false := by
            rw [← isConstant_leaf ll hleaf]
            simpa [isConstant, isConstantL] using hc
          exact deg1L1_sound D o X hA hX op lop f fl hf hfl ll hll hnc r b h hv
      · cases hleaf : (isLeaf ll && isLeaf lr) with
        | false => simp only [Bool.true_and, hleaf, Bool.false_eq_true, ↓reduceIte] at h; exact hu h
        | true =>
          simp only [Bool.true_and, hleaf, ↓reduceIte] at h
          have hleaves : isLeaf ll = true ∧ isLeaf lr = true := by simpa using hleaf
          simp only [Tree.WF] at hcw
          obtain ⟨fl, hfl, hnifl⟩ := nifOp_lookup o 2 lop (by omega) hcw.2.1.1 (by simpa using hcw.2.1.2.1)
          rw [hnifl] at h
          simp only [jl_ok_bind] at h
          have hll := LeafOK.of_wf ll hleaves.1 (hcw.2.2 ll (by simp))
          have hlr := LeafOK.of_wf lr hleaves.2 (hcw.2.2 lr (by simp))
          have hnc : (isConstLeaf ll && isConstLeaf lr) = false := by
            rw [← isConstant_leaf ll hleaves.1, ← isConstant_leaf lr hleaves.2]
            simpa [isConstant, isConstantL] using hc
          exact deg1L2_sound D o X hA hX op lop f fl hf hfl ll lr hll hlr hnc r b h hok hv
      · exact hu h

private theorem deg2Dispatch_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hX : XFinite X) (op : Nat) (l q : Tree T)
    (hw : (Tree.branch op [l, q]).WF D o.nops X.nrows)
    (hc : (isConstant l && isConstant q) = false)
    (ihl : IndSound D o X l) (ihq : IndSound D o X q) (r : ResultOk T) (b : Buf T)
    (h : deg2Dispatch ⟨true, true, D⟩ o X op l q
      (evalT ⟨true, true, D⟩ o X l) (evalT ⟨true, true, D⟩ o X q) .none = .ok (r, b))
    (hok : r.ok = true) (hv : isValidArray r.x = true) : GoodTree o X (.branch op [l, q]) := by
  have hw' := hw
  simp only [Tree.WF] at hw'
  have hwl := hw'.2.2 l (by simp)
  have hwq := hw'.2.2 q (by simp)
  obtain ⟨f, hf, hnif⟩ := nifOp_lookup o 2 op (by omega) hw'.2.1.1 (by simpa using hw'.2.1.2.1)
  have hidx := idxOp_lookup o 2 op f (by omega) hf
  have hu : unfused2 ⟨true, true, D⟩ (.ok f) (evalT ⟨true, true, D⟩ o X l)
      (evalT ⟨true, true, D⟩ o X q) .none = .ok (r, b) → GoodTree o X (.branch op [l, q]) :=
    fun he => unfused2_sound D o X hA hn op l q hwl hwq ihl ihq f hf r b he hok hv
  have hR : isLeaf q = true → checked ⟨true, true, D⟩ (evalT ⟨true, true, D⟩ o X l)
      (fun xl id b => deg2R0 ⟨true, true, D⟩ X f q xl id b) .none = .ok (r, b) →
      GoodTree o X (.branch op [l, q]) :=
    fun hq he => checked_R0_sound D o X hA hn hX op l q hwl ihl (LeafOK.of_wf q hq hwq) f hf r b he hok hv
  have hL : isLeaf l = true → checked ⟨true, true, D⟩ (evalT ⟨true, true, D⟩ o X q)
      (fun xq id b => deg2L0 ⟨true, true, D⟩ X f l xq id b) .none = .ok (r, b) →
      GoodTree o X (.branch op [l, q]) :=
    fun hl he => checked_L0_sound D o X hA hn hX op l q hwq ihq (LeafOK.of_wf l hl hwl) f hf r b he hok hv
  unfold deg2Dispatch at h
  by_cases hlim : operatorLimit < (opsOf o 2).length
  · simp only [hlim, ↓reduceIte, hidx] at h
    exact hu h
  · simp only [hlim, ↓reduceIte, hnif, jl_ok_bind] at h
    cases hll : isLeaf l <;> cases hqq : isLeaf q
    · simp only [hll, hqq, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
      exact hu h
    · simp only [hll, hqq, Bool.true_and, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
      rcases l with a | fidx | ⟨lop, cs⟩
      · simp [isLeaf] at hll
      · simp [isLeaf] at hll
      · rcases cs with _ | ⟨ll, _ | ⟨lr, _ | ⟨s, rest⟩⟩⟩
        · exact hR hqq h
        · exact hR hqq h
        · cases hfu : (isNum T && isLeaf ll && isLeaf lr) with
          | false => simp only [hfu, Bool.false_eq_true, ↓reduceIte] at h; exact hR hqq h
          | true =>
            simp only [hfu, ↓reduceIte] at h
            have hleaf : isLeaf ll = true ∧ isLeaf lr = true := by
              have hp : (isNum T = true ∧ isLeaf ll = true) ∧ isLeaf lr = true := by simpa using hfu
              exact ⟨hp.1.2, hp.2⟩
            simp only [Tree.WF] at hwl
            obtain ⟨g, hg, hnifg⟩ := nifOp_lookup o 2 lop (by omega) hwl.2.1.1 (by simpa using hwl.2.1.2.1)
            rw [hnifg] at h
            simp only [jl_ok_bind] at h
            have hl1 := LeafOK.of_wf ll hleaf.1 (hwl.2.2 ll (by simp))
            have hl2 := LeafOK.of_wf lr hleaf.2 (hwl.2.2 lr (by simp))
            have hl3 := LeafOK.of_wf q hqq hwq
            have hnc : ¬ (isConstLeaf ll = true ∧ isConstLeaf lr = true ∧ isConstLeaf q = true) := by
              intro ⟨h1, h2, h3⟩
              rw [← isConstant_leaf ll hleaf.1] at h1
              rw [← isConstant_leaf lr hleaf.2] at h2
              rw [← isConstant_leaf q hqq] at h3
              simp [isConstant, isConstantL, h1, h2, h3] at hc
            exact branch0_left_sound D o X hA hX op lop f g hf hg ll lr q hl1 hl2 hl3 hnc r b h hok hv
        · exact hR hqq h
    · simp only [hll, hqq, Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
      rcases q with a | fidx | ⟨qop, cs⟩
      · simp [isLeaf] at hqq
      · simp [isLeaf] at hqq
      · rcases cs with _ | ⟨ql, _ | ⟨qr, _ | ⟨s, rest⟩⟩⟩
        · exact hL hll h
        · exact hL hll h
        · cases hfu : (isNum T && isLeaf ql && isLeaf qr) with
          | false => simp only [hfu, Bool.false_eq_true, ↓reduceIte] at h; exact hL hll h
          | true =>
            simp only [hfu, ↓reduceIte] at h
            have hleaf : isLeaf ql = true ∧ isLeaf qr = true := by
              have hp : (isNum T = true ∧ isLeaf ql = true) ∧ isLeaf qr = true := by simpa using hfu
              exact ⟨hp.1.2, hp.2⟩
            simp only [Tree.WF] at hwq
            obtain ⟨g, hg, hnifg⟩ := nifOp_lookup o 2 qop (by omega) hwq.2.1.1 (by simpa using hwq.2.1.2.1)
            rw [hnifg] at h
            simp only [jl_ok_bind] at h
            have hl1 := LeafOK.of_wf l hll hwl
            have hl2 := LeafOK.of_wf ql hleaf.1 (hwq.2.2 ql (by simp))
            have hl3 := LeafOK.of_wf qr hleaf.2 (hwq.2.2 qr (by simp))
            have hnc : ¬ (isConstLeaf l = true ∧ isConstLeaf ql = true ∧ isConstLeaf qr = true) := by
              intro ⟨h1, h2, h3⟩
              rw [← isConstant_leaf l hll] at h1
              rw [← isConstant_leaf ql hleaf.1] at h2
              rw [← isConstant_leaf qr hleaf.2] at h3
              simp [isConstant, isConstantL, h1, h2, h3] at hc
            exact branch0_right_sound D o X hA hX op qop f g hf hg l ql qr hl1 hl2 hl3 hnc r b h hok hv
        · exact hL hll h
    · simp only [hll, hqq, Bool.true_and, ↓reduceIte] at h
      have hl := LeafOK.of_wf l hll hwl
      have hq := LeafOK.of_wf q hqq hwq
      have hnc : (isConstLeaf l && isConstLeaf q) = false := by
        rw [← isConstant_leaf l hll, ← isConstant_leaf q hqq]
        exact hc
      obtain ⟨hgl, hgq, hx⟩ := deg2L0R0_shape D o X hX f l q hl hq hnc r b h hok
      rw [hx] at hv
      exact binary_array_good o X hA op f hf l q hgl hgq hv


private theorem evalT_sound (D : Nat) (o : OpEnum T) (X : JMat T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hX : XFinite X) (t : Tree T) :
    t.WF D o.nops X.nrows → IndSound D o X t := by
  induction t using Tree.induction with
  | hc v =>
    intro hw r b h hok hv
    have he : (Except.ok (⟨JVec.fill X.ncols v, valid v, .fresh⟩, Buf.none) : Jl _) = .ok (r, b) := by
      simpa [evalT, getFilled, nextId] using h
    have hval : valid v = true :=
      (congrArg (fun p : ResultOk T × Buf T => p.1.ok) (Except.ok.inj he)).trans hok
    intro j hj
    simpa only [AllValid] using hval
  | hf f =>
    intro hw r b h hok hv
    simp only [Tree.WF] at hw
    exact feature_good o X hX f hw.1 hw.2.1
  | hb op cs ih =>
    intro hw r b h hok hv
    have hw' := hw
    simp only [Tree.WF] at hw'
    have hchildren : ∀ c ∈ cs, IndSound D o X c := fun c hc => ih c hc (hw'.2.2 c hc)
    cases hcon : isConstantL cs with
    | true =>
      unfold evalT at h
      simp only [hcon, ↓reduceIte] at h
      exact constPath_sound D o X (.branch op cs) hw hcon r b h hok
    | false =>
      rcases cs with _ | ⟨c, _ | ⟨q, _ | ⟨s, rest⟩⟩⟩
      · simp at hw'
      · simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte] at h
        exact deg1Dispatch_sound D o X hA hn hX op c hw
          (by simpa [isConstantL] using hcon) (hchildren c (by simp)) r b h hok hv
      · simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte] at h
        exact deg2Dispatch_sound D o X hA hn hX op c q hw
          (by simpa [isConstantL] using hcon) (hchildren c (by simp)) (hchildren q (by simp)) r b h hok hv
      · have hD : D ≠ 2 := by have := hw'.1.2.1; simp only [List.length_cons] at this; omega
        simp only [evalT, hcon, Bool.false_eq_true, ↓reduceIte, hD] at h
        apply degn_sound D o X hA hn op (c :: q :: s :: rest) hw hchildren r b _ hok hv
        simpa only [List.length_cons, Nat.add_assoc] using h

theorem fusedSound {T : Type} [JlScalar T] (D : Nat) (o : OpEnum T) (X : JMat T) (t : Tree T)
    (hA : ArrayValidExact T) (hn : 1 ≤ X.ncols) (hw : t.WF D o.nops X.nrows) (hX : XFinite X)
    (out : JVec T) (h : evalArr ⟨true, true, D⟩ o X t .none = .ok (out, true)) :
    ∀ j, j < X.ncols → AllValid o (col X (j + 1)) t := by
  cases he : evalT ⟨true, true, D⟩ o X t .none with
  | error e => simp [evalArr, he] at h
  | ok p =>
    rcases p with ⟨r, b⟩
    simp only [evalArr, he, jl_ok_bind, jl_pure] at h
    have hf := congrArg Prod.snd (Except.ok.inj h)
    have hp : r.ok = true ∧ isValidArray r.x = true := by simpa using hf
    exact evalT_sound D o X hA hn hX t hw r b he hp.1 hp.2

private instance : JlScalar Nat where
  valid := fun _ => true
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  isNumber := false
  isFloat := false
  floatLike := false
  undef := 0
  invalid? := none

example : ∀ j, j < (⟨1, 1, #[7], rfl⟩ : JMat Nat).ncols →
    AllValid (⟨[]⟩ : OpEnum Nat) (col ⟨1, 1, #[7], rfl⟩ (j + 1)) (.const 7) := by
  refine fusedSound 2 ⟨[]⟩ ⟨1, 1, #[7], rfl⟩ (.const 7) ?_ ?_ ?_ ?_ #[7] ?_
  · simp [ArrayValidExact, isValidArray, isNum, valid, JlScalar.isNumber, JlValue.valid]
  · decide
  · simp [Tree.WF]
  · simp [XFinite, valid, JlValue.valid]
  · simp [evalArr, evalT, filled, getFilled, nextId, isValidArray, isNum, valid, JlScalar.isNumber, JlValue.valid, JVec.fill]


end DynExpr.Eval
