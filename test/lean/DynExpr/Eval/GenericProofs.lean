import DynExpr.Eval.Props

namespace DynExpr.Eval

@[local simp] private theorem ok_bind {A B : Type} (a : A) (f : A → Jl B) :
    (Except.ok a >>= f) = f a := rfl
@[local simp] private theorem error_bind {A B : Type} (e : JlError) (f : A → Jl B) :
    (Except.error e >>= f) = .error e := rfl
@[local simp] private theorem ok_map {A B : Type} (a : A) (f : A → B) :
    f <$> (Except.ok a : Jl A) = .ok (f a) := rfl

@[local simp] private theorem jl_pure {A : Type} (a : A) : (pure a : Jl A) = .ok a := rfl
@[local simp] private theorem error_map {A B : Type} (e : JlError) (f : A → B) :
    f <$> (Except.error e : Jl A) = .error e := rfl

private theorem select_last {A : Type} (xs : List A) (op : Nat) (v : A)
    (hp : 1 ≤ op) (hv : xs[op - 1]? = some v) :
    ∃ last, xs.getLast? = some last ∧
      (if 1 ≤ op ∧ op < xs.length then (xs[op - 1]?).getD last else last) = v := by
  have hb : op - 1 < xs.length := (List.getElem?_eq_some_iff.mp hv).1
  have hn : xs ≠ [] := by intro he; simp [he] at hb
  obtain ⟨last, hl⟩ : ∃ last, xs.getLast? = some last := by
    cases h : xs.getLast? with
    | none => simp_all
    | some last => exact ⟨last, rfl⟩
  refine ⟨last, hl, ?_⟩
  by_cases h : op < xs.length
  · simp [hp, h, hv]
  · have he : op - 1 = xs.length - 1 := by omega
    have hx : xs.getLast? = xs[xs.length - 1]? := List.getLast?_eq_getElem?
    rw [hx, ← he, hv] at hl
    simp only [Option.some.injEq] at hl
    simp [h, ← hl]

private theorem gnifOp_of_get {V : Type} (xs : List (GOp V)) (op : Nat) (g : GOp V)
    (hp : 1 ≤ op) (hg : xs[op - 1]? = some g) : gnifOp xs op = .ok g := by
  obtain ⟨last, hl, hs⟩ := select_last xs op g hp hg
  simp [gnifOp, hl, hs]

private theorem gen1_of_GOk {V : Type} (o : GOpEnum V) (throw : Bool) (x : JVec V)
    (t : Tree V) : ∀ v, GOk o (fun f => if 1 ≤ f then x[f - 1]? else none) t v →
      gen1 o throw x t = .ok (some v, true) := by
  induction t using Tree.induction with
  | hc v => intro w h; cases h; rfl
  | hf f =>
    intro v h
    cases h with
    | feature _ _ hv =>
      split at hv
      · simp [gen1, *]
      · cases hv
  | hb op cs ih =>
    intro v h
    cases h with
    | branch _ _ vs g _ hl hg hp hm hv =>
      have hc : gen1L o throw x cs = .ok (.inr vs) := by
        clear hm hg hv
        induction cs generalizing vs with
        | nil => cases hl; rfl
        | cons c cs ihl =>
          cases hl with
          | cons _ _ v vs hc hs =>
            have ht := ih c (by simp) v hc
            have tail := ihl (by intro c hc; exact ih c (by simp [hc])) vs hs
            simp [gen1L, ht, tail]
      have hop := gnifOp_of_get _ op g hp hg
      simp [gen1, hc, hop, hm, hv]

theorem evalGenericVectorAV_proof : evalGenericVectorAV := by
  intro V o throw x t v h
  simp [genEvalVec, genCatch, gen1_of_GOk o throw x t v h]

private theorem gen1L_abort {V : Type} (o : GOpEnum V) (x : JVec V)
    (cs : List (Tree V)) : ∀ r, gen1L o false x cs = .ok (.inl r) → r = (none, false) := by
  induction cs with
  | nil => intro r h; cases h
  | cons c cs ih =>
    intro r h
    simp only [gen1L] at h
    cases ht : gen1 o false x c with
    | error e => simp [ht] at h
    | ok a =>
      rcases a with ⟨v, ok⟩
      cases ok <;> simp [ht] at h
      · exact h.symm
      · cases v with
        | none => cases h
        | some v =>
          cases hs : gen1L o false x cs with
          | error e => simp [hs] at h
          | ok a =>
            cases a with
            | inl a => simp [hs] at h; subst r; exact ih a hs
            | inr vs => simp [hs] at h

private theorem gen1_flag {V : Type} (o : GOpEnum V) (x : JVec V) (t : Tree V)
    (r : Option V × Bool) (h : gen1 o false x t = .ok r)
    (hf : r.2 = false) : r.1 = none := by
  cases t with
  | const v => simp [gen1] at h; subst r; cases hf
  | feature f =>
    simp only [gen1] at h
    split at h
    · split at h
      · simp only [Except.ok.injEq] at h; subst r; cases hf
      · cases h
    · cases h
  | branch op cs =>
    simp only [gen1] at h
    cases hc : gen1L o false x cs with
    | error e => simp [hc] at h
    | ok a =>
      cases a with
      | inl a =>
        have ha := gen1L_abort o x cs a hc
        simpa [hc, ha] using congrArg (fun r : Option V × Bool => r.1) (by simpa [hc, ha] using h.symm)
      | inr vs =>
        cases hg : gnifOp (gopsOf o cs.length) op with
        | error e => simp [hc, hg] at h
        | ok g =>
          simp only [hc, hg, ok_bind, Bool.not_false, Bool.true_and] at h
          split at h
          · simp only [jl_pure, Except.ok.injEq] at h
            exact congrArg Prod.fst h.symm
          · cases hv : g.call vs with
            | error e => simp [hv] at h
            | ok v => simp [hv] at h; subst r; cases hf

private theorem mapM_ok {A B : Type} (xs : List A) (f : A → Jl B) (g : A → B)
    (h : ∀ a ∈ xs, f a = .ok (g a)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp [List.mapM_cons, h a (by simp), ih (by intro b hb; exact h b (by simp [hb]))]

private theorem bcast_ok {V : Type} (n : Nat) (xs : List (JVec V))
    (f : List V → Jl V) (hne : xs ≠ []) (hs : ∀ x ∈ xs, x.size = n)
    (hv : ∀ k, k < n → ∃ v,
      (do
        let args ← xs.mapM (fun (x : JVec V) => match x[k]? with
          | some a => Except.ok a | none => Except.error JlError.boundsError)
        f args) = .ok v) :
    ∃ out, bcast f xs = .ok out ∧ out.size = n ∧
      ∀ k, k < n → ∀ v,
        (do
          let args ← xs.mapM (fun (x : JVec V) => match x[k]? with
            | some a => Except.ok a | none => Except.error JlError.boundsError)
          f args) = .ok v → out[k]? = some v := by
  classical
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    have hx := hs x (by simp)
    have hall : (x :: xs).all (fun c => c.size == x.size) = true := by
      apply List.all_eq_true.mpr
      intro a ha
      simp [hs a ha, hx]
    let value := fun k : Fin n => (hv k.val k.isLt).choose
    let out := Array.ofFn value
    refine ⟨out, ?_, by simp [out], ?_⟩
    · simp only [bcast]
      rw [ite_eq_left hall, hx]
      have hrange : (List.finRange n).map Fin.val = List.range n := by
        apply List.ext_getElem
        · simp
        · intro i hi hj; simp
      have hm : (List.range n).mapM (fun (k : Nat) => do
          let args ← (x :: xs).mapM (fun (a : JVec V) => match a[k]? with
            | some v => Except.ok v | none => Except.error JlError.boundsError)
          f args) = .ok ((List.finRange n).map value) := by
        rw [← hrange, List.mapM_map]
        exact mapM_ok _ _ value (by intro a ha; exact (hv a.val a.isLt).choose_spec)
      change ((List.range n).mapM (fun (k : Nat) => do
        let args ← (x :: xs).mapM (fun (a : JVec V) => match a[k]? with
          | some v => Except.ok v | none => Except.error JlError.boundsError)
        f args) >>= fun vs => Except.ok vs.toArray) = Except.ok out
      rw [hm]
      simp only [ok_bind]
      congr 1
      apply Array.ext
      · simp [out]
      · intro i hi hj; simp [out]
    · intro k hk v he
      have heq := (hv k hk).choose_spec
      have eqv : (hv k hk).choose = v := Except.ok.inj (heq.symm.trans he)
      simpa [out, value, hk] using eqv


private theorem gen2L_abort {V : Type} (o : GOpEnum V) (X : JMat V)
    (cs : List (Tree V)) : ∀ r, gen2L o false X cs = .ok (.inl r) → r = (none, false) := by
  induction cs with
  | nil => intro r h; cases h
  | cons c cs ih =>
    intro r h
    simp only [gen2L] at h
    cases ht : gen2 o false X c with
    | error e => simp [ht] at h
    | ok a =>
      rcases a with ⟨v, ok⟩
      cases ok <;> simp [ht] at h
      · exact h.symm
      · cases v with
        | none => cases h
        | some v =>
          cases hs : gen2L o false X cs with
          | error e => simp [hs] at h
          | ok a =>
            cases a with
            | inl a => simp [hs] at h; subst r; exact ih a hs
            | inr vs => simp [hs] at h

private theorem gen2_flag {V : Type} (o : GOpEnum V) (X : JMat V) (t : Tree V)
    (r : Option (JVec V) × Bool) (h : gen2 o false X t = .ok r)
    (hf : r.2 = false) : r.1 = none := by
  cases t with
  | const v => simp [gen2] at h; subst r; cases hf
  | feature f =>
    cases hr : X.row f with
    | error e => simp [gen2, hr] at h
    | ok x => simp [gen2, hr] at h; subst r; cases hf
  | branch op cs =>
    simp only [gen2] at h
    cases hc : gen2L o false X cs with
    | error e => simp [hc] at h
    | ok a =>
      cases a with
      | inl a =>
        have ha := gen2L_abort o X cs a hc
        have he : r = (none, false) := by simpa [hc, ha] using h.symm
        simp [he]
      | inr vs =>
        cases hg : gnifOp (gopsOf o cs.length) op with
        | error e => simp [hc, hg] at h
        | ok g =>
          simp only [hc, hg, ok_bind, Bool.not_false, Bool.true_and] at h
          split at h
          · simp only [jl_pure, Except.ok.injEq] at h
            exact congrArg Prod.fst h.symm
          · cases hv : bcast g.call vs with
            | error e => simp [hv] at h
            | ok v => simp [hv] at h; subst r; cases hf

private theorem catch_false {R : Type} (r : Jl (Option R × Bool))
    (h : ∀ v, r = .ok v → v.2 = false → v.1 = none) :
    ∃ v, genCatch false r = .ok v ∧ (v.2 = false → v.1 = none) := by
  cases r with
  | error e => exact ⟨(none, false), rfl, by simp⟩
  | ok v => exact ⟨v, rfl, h v rfl⟩

private theorem catch_true {R : Type} (r : Jl (Option R × Bool)) :
    ∀ e, genCatch true r = .error e → ∃ m, e = .errorException m := by
  cases r with
  | ok v => intro e h; cases h
  | error e => intro e h; exact ⟨"Failed to evaluate tree", (Except.error.inj h).symm⟩

theorem evalGenericThrow_proof : evalGenericThrow := by
  intro V o x X t
  exact ⟨catch_false _ (gen1_flag o x t), catch_false _ (gen2_flag o X t),
    catch_true _, catch_true _⟩

example : GOk (⟨[]⟩ : GOpEnum Nat)
    (fun f => if 1 ≤ f then (#[7] : JVec Nat)[f - 1]? else none) (.const 7) 7 :=
  .const 7


private theorem row_sample {V : Type} (X : JMat V) (f : Nat) (out : JVec V)
    (hr : X.row f = .ok out) (k : Nat) (hk : k < X.ncols) :
    out[k]? = (X.get? f (k + 1)).toOption := by
  unfold JMat.row at hr
  split at hr
  · cases hr
    simp only [JMat.get?]
    change _ = (if h : (1 ≤ f ∧ f ≤ X.nrows) ∧ (1 ≤ k + 1 ∧ k + 1 ≤ X.ncols) then
      Except.ok (X.data[X.nrows * ((k + 1) - 1) + (f - 1)]'_) else
      Except.error JlError.boundsError).toOption
    have hkn : k + 1 ≤ X.ncols := by omega
    simp [*, Except.toOption]
  · cases hr

private theorem GOkL_member {V : Type} (o : GOpEnum V) (x : Nat → Option V)
    (cs : List (Tree V)) (vs : List V) (h : GOkL o x cs vs) :
    ∀ c ∈ cs, ∃ v, GOk o x c v := by
  induction cs generalizing vs with
  | nil => simp
  | cons c cs ih =>
    cases h with
    | cons _ _ v vs hc hs =>
      intro a ha
      rcases List.mem_cons.mp ha with he | ht
      · subst a; exact ⟨v, hc⟩
      · exact ih vs hs a ht

private theorem gen2L_sound {V : Type} (o : GOpEnum V) (X : JMat V)
    (cs : List (Tree V))
    (hc : ∀ c ∈ cs, ∃ out, gen2 o true X c = .ok (some out, true) ∧
      out.size = X.ncols ∧ ∀ j, 1 ≤ j → j ≤ X.ncols →
        ∀ v, GOk o (genSample X j) c v → out[j - 1]? = some v) :
    ∃ xs, gen2L o true X cs = .ok (.inr xs) ∧ xs.length = cs.length ∧
      (∀ x ∈ xs, x.size = X.ncols) ∧ ∀ j, 1 ≤ j → j ≤ X.ncols →
      ∀ vs, GOkL o (genSample X j) cs vs →
        xs.mapM (fun x => match x[j - 1]? with
          | some v => Except.ok v | none => Except.error JlError.boundsError) = .ok vs := by
  induction cs with
  | nil => refine ⟨[], rfl, rfl, by simp, ?_⟩; intro j hj hjn vs h; cases h; rfl
  | cons c cs ih =>
    obtain ⟨out, ho, hn, hv⟩ := hc c (by simp)
    obtain ⟨xs, hl, hlen, hs, hvs⟩ := ih (by intro c hm; exact hc c (by simp [hm]))
    refine ⟨out :: xs, by simp [gen2L, ho, hl], by simp [hlen], ?_, ?_⟩
    · intro x hx; rcases List.mem_cons.mp hx with he | hm
      · subst x; exact hn
      · exact hs x hm
    · intro j hj hjn vs h
      cases h with
      | cons _ _ v vs hc ht =>
        simp [List.mapM_cons, hv j hj hjn v hc, hvs j hj hjn vs ht]

private theorem gen2_sound {V : Type} (o : GOpEnum V) (X : JMat V) (t : Tree V) :
    t.WF 255 (fun d => (gopsOf o d).length) X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, GOk o (genSample X j) t v) →
    ∃ out, gen2 o true X t = .ok (some out, true) ∧ out.size = X.ncols ∧
      ∀ j, 1 ≤ j → j ≤ X.ncols → ∀ v,
        GOk o (genSample X j) t v → out[j - 1]? = some v := by
  induction t using Tree.induction with
  | hc v =>
    intro hw h
    refine ⟨JVec.fill X.ncols v, rfl, by simp [JVec.fill], ?_⟩
    intro j hj hjn w hw; cases hw
    simp [JVec.fill, show j - 1 < X.ncols by omega]
  | hf f =>
    intro hw h
    simp only [Tree.WF] at hw
    obtain ⟨out, hr, hn⟩ := X.row_exists f hw.1 hw.2.1
    refine ⟨out, by simp [gen2, hr], hn, ?_⟩
    intro j hj hjn v h
    cases h with
    | feature _ _ hv =>
      have hs := row_sample X f out hr (j - 1) (by omega)
      change (X.get? f j).toOption = some v at hv
      simpa [show j - 1 + 1 = j by omega, hv] using hs
  | hb op cs ih =>
    intro hw h
    simp only [Tree.WF] at hw
    have hc : ∀ c ∈ cs, ∃ out, gen2 o true X c = .ok (some out, true) ∧
        out.size = X.ncols ∧ ∀ j, 1 ≤ j → j ≤ X.ncols →
          ∀ v, GOk o (genSample X j) c v → out[j - 1]? = some v := by
      intro c hm
      apply ih c hm (hw.2.2 c hm)
      intro j hj hjn
      obtain ⟨v, hv⟩ := h j hj hjn
      cases hv with
      | branch _ _ vs g _ hl hg hp hmethod hv => exact GOkL_member o _ cs vs hl c hm
    obtain ⟨xs, hl, hlen, hs, hvs⟩ := gen2L_sound o X cs hc
    have hi : op - 1 < (gopsOf o cs.length).length := by have := hw.2.1.2.1; omega
    let g := (gopsOf o cs.length)[op - 1]'hi
    have hg : (gopsOf o cs.length)[op - 1]? = some g := by simp [g, hi]
    have hop := gnifOp_of_get _ op g hw.2.1.1 hg
    have hpoint : ∀ j, 1 ≤ j → j ≤ X.ncols → ∀ v,
        GOk o (genSample X j) (.branch op cs) v →
        (do let args ← xs.mapM (fun (x : JVec V) => match x[j - 1]? with
              | some a => Except.ok a | none => Except.error JlError.boundsError)
            g.call args) = .ok v := by
      intro j hj hjn v hv
      cases hv with
      | branch _ _ vs g' _ hchildren hg' hp hm hcall =>
        have he : g' = g := Option.some.inj (hg'.symm.trans hg)
        subst g'
        simp [hvs j hj hjn vs hchildren, hcall]
    obtain ⟨out, hb, hn, hout⟩ := bcast_ok X.ncols xs g.call
      (by intro he; have := hw.1.1; simp [he] at hlen; omega) hs (by
        intro k hk
        obtain ⟨v, hv⟩ := h (k + 1) (by omega) (by omega)
        exact ⟨v, by simpa using hpoint (k + 1) (by omega) (by omega) v hv⟩)
    refine ⟨out, by simp [gen2, hl, hop, hb], hn, ?_⟩
    intro j hj hjn v hv
    exact hout (j - 1) (by omega) v (hpoint j hj hjn v hv)

theorem evalGenericMatrixAV_proof : evalGenericMatrixAV := by
  intro V o X t vs hw h
  obtain ⟨out, ho, hn, hv⟩ := gen2_sound o X t hw (by
    intro j hj hjn; exact ⟨vs j, h j hj hjn⟩)
  exact ⟨out, by simp [genEvalMat, genCatch, ho], hn,
    fun j hj hjn => hv j hj hjn (vs j) (h j hj hjn)⟩

example : (Tree.const 7 : Tree Nat).WF 255
    (fun d => (gopsOf (⟨[]⟩ : GOpEnum Nat) d).length) 1 ∧
    (∀ j, 1 ≤ j → j ≤ (JMat.ofFn 1 1 (fun _ _ => 7)).ncols →
      GOk (⟨[]⟩ : GOpEnum Nat) (genSample (JMat.ofFn 1 1 (fun _ _ => 7)) j)
        (.const 7) 7) := by
  simp only [Tree.WF]
  exact ⟨True.intro, fun _ _ _ => .const 7⟩


private theorem nifOp_of_lookup {T : Type} [JlScalar T] (o : OpEnum T)
    (d op : Nat) (f : List T → T) (hd : 1 ≤ d) (hp : 1 ≤ op)
    (hf : o.lookup d op = some f) : nifOp (opsOf o d) op = .ok f := by
  have hg : (opsOf o d)[op - 1]? = some f := by
    simpa [OpEnum.lookup, opsOf, show d ≠ 0 by omega, show op ≠ 0 by omega] using hf
  obtain ⟨last, hl, hs⟩ := select_last (opsOf o d) op f hp hg
  simp [nifOp, hl, hs]

private theorem diffL_denote {T : Type} [JlScalar T] (o : OpEnum T) (X : JMat T)
    (cs : List (Tree T))
    (hc : ∀ c ∈ cs, ∃ out, diffT o X c = .ok ⟨out, true, .fresh⟩ ∧ Denotes o X c out) :
    ∃ xs, diffL o X cs = .ok (.inr xs) ∧ xs.length = cs.length ∧
      (∀ x ∈ xs, x.size = X.ncols) ∧ ∀ j, 1 ≤ j → j ≤ X.ncols →
        ∃ vs, xs.mapM (fun x => match x[j - 1]? with
          | some v => Except.ok v | none => Except.error JlError.boundsError) = .ok vs ∧
          cs.mapM (Tree.denoteRow o X j) = some vs := by
  induction cs with
  | nil => exact ⟨[], rfl, rfl, by simp, fun _ _ _ => ⟨[], rfl, rfl⟩⟩
  | cons c cs ih =>
    obtain ⟨out, ho, hn, hv⟩ := hc c (by simp)
    obtain ⟨xs, hl, hlen, hs, hvs⟩ := ih (by intro c hm; exact hc c (by simp [hm]))
    refine ⟨out :: xs, by simp [diffL, ho, hl], by simp [hlen], ?_, ?_⟩
    · intro x hx; rcases List.mem_cons.mp hx with he | hm
      · subst x; exact hn
      · exact hs x hm
    · intro j hj hjn
      have hi : j - 1 < out.size := by omega
      let v := out[j - 1]'hi
      have hg : out[j - 1]? = some v := by simp [v, hi]
      have hd : c.denoteRow o X j = some v := (hv j hj hjn).symm.trans hg
      obtain ⟨vs, hget, hden⟩ := hvs j hj hjn
      exact ⟨v :: vs, by simp [List.mapM_cons, hg, hget],
        by simp [List.mapM_cons, hd, hden]⟩

private theorem valid_of_denotes {T : Type} [JlScalar T] (o : OpEnum T) (X : JMat T)
    (t : Tree T) (out : JVec T) (hd : Denotes o X t out)
    (hv : ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, t.denoteRow o X j = some v ∧ valid v = true) :
    out.toList.all valid = true := by
  apply List.all_eq_true.mpr
  intro v hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
  have hin : i < out.size := by simpa using hi
  have hget : out[i]? = some v := by
    simp only [Array.getElem?_eq_getElem hin]
    congr 1
  obtain ⟨w, hw, hwv⟩ := hv (i + 1) (by omega) (by have := hd.1; omega)
  have hdget := hd.2 (i + 1) (by omega) (by have := hd.1; omega)
  have heq : v = w := Option.some.inj (hget.symm.trans (by simpa [hw] using hdget))
  simpa [heq] using hwv

private theorem diffT_denote {T : Type} [JlScalar T] (D : Nat) (o : OpEnum T)
    (X : JMat T) (unit : ∀ v : T, JlScalar.mul JlScalar.one v = v) (hn : 1 ≤ X.ncols)
    (t : Tree T) : t.WF D o.nops X.nrows →
    (∀ j, 1 ≤ j → j ≤ X.ncols → AllValid o (col X j) t) →
    ∃ out, diffT o X t = .ok ⟨out, true, .fresh⟩ ∧ Denotes o X t out := by
  induction t using Tree.induction with
  | hc v =>
    intro hw h
    have hconst : constRow X.ncols v = JVec.fill X.ncols v := by
      simp [constRow, JVec.fill, unit]
    have hv : valid v = true := by simpa [AllValid] using h 1 (by omega) hn
    refine ⟨JVec.fill X.ncols v, by simp [diffT, hconst, hv], by simp [JVec.fill], ?_⟩
    intro j hj hjn
    simp [Tree.denoteRow, Tree.denote, JVec.fill, show j - 1 < X.ncols by omega]
  | hf f =>
    intro hw h
    simp only [Tree.WF] at hw
    obtain ⟨out, hr, hn⟩ := X.row_exists f hw.1 hw.2.1
    have hd : Denotes o X (.feature f) out := by
      refine ⟨hn, ?_⟩
      intro j hj hjn
      simpa [Tree.denoteRow, Tree.denote, show j - 1 + 1 = j by omega] using
        row_sample X f out hr (j - 1) (by omega)
    have hv := valid_of_denotes o X (.feature f) out hd (fun j hj hjn => by
      simpa [AllValid, Tree.denoteRow, Tree.denote, col] using h j hj hjn)
    have ha : isValidArray out = true := by
      unfold isValidArray
      have hv' : out.all valid = true := by simpa using hv
      simp [hv']
    exact ⟨out, by simp [diffT, hr, ha], hd⟩
  | hb op cs ih =>
    intro hw h
    simp only [AllValid] at h
    simp only [Tree.WF] at hw
    have hc : ∀ c ∈ cs, ∃ out, diffT o X c = .ok ⟨out, true, .fresh⟩ ∧ Denotes o X c out := by
      intro c hm
      apply ih c hm (hw.2.2 c hm)
      intro j hj hjn
      exact (h j hj hjn).1 c hm
    obtain ⟨xs, hl, hlen, hs, hvs⟩ := diffL_denote o X cs hc
    obtain ⟨f, hf⟩ := (o.lookup_some_iff cs.length op).2 ⟨hw.2.1.1, hw.2.1.2.1⟩
    have hop := nifOp_of_lookup o cs.length op f hw.1.1 hw.2.1.1 hf
    obtain ⟨out, hb, hn, hout⟩ := bcast_ok X.ncols xs (fun vs => .ok (f vs))
      (by intro he; have := hw.1.1; simp [he] at hlen; omega) hs (by
        intro k hk
        obtain ⟨vs, hg, hd⟩ := hvs (k + 1) (by omega) (by omega)
        have hh := congrArg (fun r : Jl (List T) => r >>= fun vs => Except.ok (f vs)) hg
        exact ⟨f vs, by simpa using hh⟩)
    have hd : Denotes o X (.branch op cs) out := by
      refine ⟨hn, ?_⟩
      intro j hj hjn
      obtain ⟨vs, hg, hd⟩ := hvs j hj hjn
      simp only [Tree.denoteRow] at hd
      have ho := hout (j - 1) (by omega) (f vs) (by simp [hg])
      simpa [Tree.denoteRow, Tree.denote, hf, hd] using ho
    have hvalid : out.toList.all valid = true := valid_of_denotes o X _ out hd (by
      intro j hj hjn
      exact (h j hj hjn).2)
    exact ⟨out, by simp only [diffT, hl, hop, hb, ok_bind, jl_pure, hvalid], hd⟩

theorem evalDiffDenoteAV_proof : evalDiffDenoteAV := by
  intro T inst D o X t unit hn hw hv
  obtain ⟨out, ho, hd⟩ := diffT_denote D o X unit hn t hw hv
  exact ⟨out, by simp [differentiableEvalTreeArray, ho, Except.map], hd⟩

private instance : JlScalar Nat where
  valid := fun _ => true
  zero := 0
  one := 1
  add := Nat.add
  mul := Nat.mul
  isNumber := true
  isFloat := false
  floatLike := false
  undef := 0
  invalid? := none

example : (∀ v : Nat, JlScalar.mul JlScalar.one v = v) ∧
    1 ≤ (JMat.ofFn 1 1 (fun _ _ => 7)).ncols ∧
    (Tree.const 7).WF 1 (OpEnum.nops (⟨[]⟩ : OpEnum Nat)) 1 ∧
    (∀ j, 1 ≤ j → j ≤ (JMat.ofFn 1 1 (fun _ _ => 7)).ncols →
      AllValid (⟨[]⟩ : OpEnum Nat) (col (JMat.ofFn 1 1 (fun _ _ => 7)) j) (.const 7)) := by
  simp [JlScalar.mul, JlScalar.one, Tree.WF, AllValid, valid, JlValue.valid, JMat.ofFn]



/-- With total operators and every in-range feature bound, a well-formed tree
has a generic value. -/
theorem gok_exists {V : Type} (o : GOpEnum V) (ho : GOpsTotal o) (x : Nat → Option V) (nf : Nat)
    (hx : ∀ i, 1 ≤ i → i ≤ nf → ∃ v, x i = some v) :
    ∀ t : Tree V, t.WF 255 (fun d => (gopsOf o d).length) nf → ∃ v, GOk o x t v := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; exact ⟨v, .const v⟩
  | hf f =>
    intro hw
    simp only [Tree.WF] at hw
    obtain ⟨v, hv⟩ := hx f hw.1 hw.2.1
    exact ⟨v, .feature f v hv⟩
  | hb op cs ih =>
    intro hw
    simp only [Tree.WF] at hw
    have hL : ∀ cs' : List (Tree V), (∀ c ∈ cs', ∃ v, GOk o x c v) → ∃ vs, GOkL o x cs' vs := by
      intro cs' h
      induction cs' with
      | nil => exact ⟨[], .nil⟩
      | cons c cs'' ihc =>
        obtain ⟨v, hv⟩ := h c (by simp)
        obtain ⟨vs, hvs⟩ := ihc (fun c' hc' => h c' (by simp [hc']))
        exact ⟨v :: vs, .cons c cs'' v vs hv hvs⟩
    obtain ⟨vs, hvs⟩ := hL cs (fun c hc => ih c hc (hw.2.2 c hc))
    have hi : op - 1 < (gopsOf o cs.length).length := by have := hw.2.1.2.1; omega
    let g := (gopsOf o cs.length)[op - 1]'hi
    have hg : (gopsOf o cs.length)[op - 1]? = some g := by simp [g, hi]
    have hmem : g ∈ gopsOf o cs.length := List.getElem_mem hi
    obtain ⟨hm, _, hc⟩ := ho cs.length g hmem
    obtain ⟨v, hv⟩ := hc vs
    exact ⟨v, .branch op cs vs g v hvs hg hw.2.1.1 (hm vs) hv⟩

theorem evalGenericVector_proof : evalGenericVector := by
  intro V o throw x t hw ho
  obtain ⟨v, hv⟩ := gok_exists o ho (fun f => if 1 ≤ f then x[f - 1]? else none) x.size
    (by
      intro i h1 h2
      exact ⟨x[i - 1]'(by omega), by simp [h1, show i - 1 < x.size by omega]⟩) t hw
  exact ⟨v, hv, evalGenericVectorAV_proof V o throw x t v hv⟩

theorem evalCallableGeneric_proof : evalCallableGeneric := by
  intro V o x t v hv
  simp [callTreeGeneric, evalGenericVectorAV_proof V o false x t v hv]

theorem evalGenericMatrix_proof : evalGenericMatrix := by
  intro V o X t hw ho
  have hex : ∀ j, 1 ≤ j → j ≤ X.ncols → ∃ v, GOk o (genSample X j) t v := by
    intro j hj hjn
    apply gok_exists o ho (genSample X j) X.nrows _ t hw
    intro i h1 h2
    obtain ⟨v, hv⟩ := X.get?_exists i j h1 h2 hj hjn
    exact ⟨v, by simp [genSample, hv, Except.toOption]⟩
  obtain ⟨out, hres, hn, hv⟩ := gen2_sound o X t hw hex
  refine ⟨out, by simp [genEvalMat, genCatch, hres], hn, ?_⟩
  intro j hj hjn
  obtain ⟨v, hgv⟩ := hex j hj hjn
  exact ⟨v, hgv, hv j hj hjn v hgv⟩

/-- Total operators exist: a generic enum with one total unary operator. -/
example : GOpsTotal (⟨[[⟨fun _ => true, fun _ => true, fun _ => .ok (0 : Nat)⟩]]⟩ : GOpEnum Nat) := by
  intro d g hg
  have hg' : g = ⟨fun _ => true, fun _ => true, fun _ => .ok (0 : Nat)⟩ := by
    simp only [gopsOf] at hg
    rcases d with _ | _ | d <;> simp at hg <;> exact hg
  subst hg'
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => ⟨0, rfl⟩⟩

end DynExpr.Eval
