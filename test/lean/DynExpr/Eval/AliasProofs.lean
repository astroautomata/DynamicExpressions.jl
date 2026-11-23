import DynExpr.Eval.Props
import Lean

namespace DynExpr.Eval

private def Mono {T : Type} (b c : Buf T) : Prop :=
  b.idx ≤ c.idx ∧ b.isNone = c.isNone

private def IdOK {T : Type} (b : Buf T) (id : Ident) (c : Buf T) : Prop :=
  match id with
  | .fresh => b.isNone = true
  | .slot k => b.isNone = false ∧ b.idx < k ∧ k ≤ c.idx

private def Track {T : Type} (b : Buf T) (id : Ident) (c : Buf T) : Prop :=
  Mono b c ∧ IdOK b id c

private def Post {A : Type} (m : Jl A) (p : A → Prop) : Prop :=
  ∀ a, m = .ok a → p a

private theorem post_bind {A B : Type} (m : Jl A) (f : A → Jl B) (p : B → Prop) :
    Post (m >>= f) p ↔ ∀ a, m = .ok a → Post (f a) p := by
  cases m <;> simp [Post, Bind.bind, Except.bind]

private theorem post_pure {A : Type} (a : A) (p : A → Prop) :
    Post (pure a : Jl A) p ↔ p a := by
  simp [Post, Pure.pure, Except.pure]

private theorem mono_refl {T : Type} (b : Buf T) : Mono b b := ⟨Nat.le_refl _, rfl⟩
private theorem mono_trans {T : Type} {a b c : Buf T} (h : Mono a b) (g : Mono b c) :
    Mono a c := ⟨Nat.le_trans h.1 g.1, h.2.trans g.2⟩

private theorem track_pre {T : Type} {a b c : Buf T} {id : Ident}
    (h : Mono a b) (g : Track b id c) : Track a id c := by
  refine ⟨mono_trans h g.1, ?_⟩
  cases id with
  | fresh => exact h.2.trans g.2
  | slot k => exact ⟨h.2.trans g.2.1, Nat.lt_of_le_of_lt h.1 g.2.2.1, g.2.2.2⟩

private theorem track_post {T : Type} {a b c : Buf T} {id : Ident}
    (h : Track a id b) (g : Mono b c) : Track a id c := by
  refine ⟨mono_trans h.1 g, ?_⟩
  cases id with
  | fresh => exact h.2
  | slot k => exact ⟨h.2.1, h.2.2.1, Nat.le_trans h.2.2.2 g.1⟩

variable {T : Type} [JlScalar T]

private theorem array_track (b : Buf T) (n : Nat) :
    Post (getArray b n) (fun p => Track b (nextId b) p.2) := by
  cases b <;> simp only [getArray]
  · simp [Post, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]
  · rw [post_bind]
    intro a h
    split <;> simp [Post, Pure.pure, Except.pure, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]
  · split
    · split <;> simp [Post, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]
    · simp [Post, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]

private theorem filled_track (b : Buf T) (v : T) (n : Nat) :
    Post (getFilled b v n) (fun p => Track b (nextId b) p.2) := by
  cases b with
  | none => simp [getFilled, Post, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]
  | mat A i =>
    simp only [getFilled, post_bind, Prod.forall]
    intro x b h
    simpa [post_pure] using array_track (.mat A i) n (x, b) h
  | vec a i =>
    simp only [getFilled, post_bind, Prod.forall]
    intro x b h
    simpa [post_pure] using array_track (.vec a i) n (x, b) h

private theorem feature_track (b : Buf T) (X : JMat T) (f : Nat) :
    Post (getFeature b X f) (fun p => Track b (nextId b) p.2) := by
  cases b with
  | none =>
    simp only [getFeature, post_bind]
    intro a h
    simp [post_pure, Track, Mono, IdOK, nextId, Buf.idx, Buf.isNone]
  | mat A i =>
    simp only [getFeature, post_bind, Prod.forall]
    intro x b h
    intro r hr
    simpa [post_pure] using array_track (.mat A i) X.ncols (x, b) h
  | vec a i =>
    simp only [getFeature, post_bind, Prod.forall]
    intro x b h
    intro r hr
    simpa [post_pure] using array_track (.vec a i) X.ncols (x, b) h

@[irreducible] private def Run (b : Buf T) (m : Jl (ResultOk T × Buf T)) : Prop :=
  Post m (fun p => Track b p.1.id p.2)

omit [JlScalar T] in
private theorem run_pure (base b : Buf T) (r : ResultOk T) (h : Track base r.id b) :
    Run base (pure (r, b)) := by simpa [Run, post_pure] using h

private theorem retV_run (base b : Buf T) (cx : Ctx) (X : JMat T) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (hb : Mono base b) (hk : Run base (k b)) :
    Run base (retV cx X v k b) := by
  unfold retV
  split
  · simp only [Run, post_bind, Prod.forall, post_pure]
    intro a c h
    exact track_pre hb (array_track b X.ncols (a, c) h)
  · exact hk

private theorem retVIf_run (base b : Buf T) (cx : Ctx) (X : JMat T) (c : Bool) (v : T)
    (k : Buf T → Jl (ResultOk T × Buf T)) (hb : Mono base b) (hk : Run base (k b)) :
    Run base (retVIf cx X c v k b) := by
  unfold retVIf
  split
  · exact retV_run base b cx X v k hb hk
  · exact hk

private theorem filled_run (base b : Buf T) (X : JMat T) (v : T) (hb : Mono base b) :
    Run base (filled X v b) := by
  simp only [filled, Run, post_bind, Prod.forall, post_pure]
  intro a c h
  exact track_pre hb (filled_track b v X.ncols (a, c) h)

private theorem array_run (base b : Buf T) (n : Nat)
    (k : (JVec T × Buf T) → Jl (ResultOk T × Buf T)) (hb : Mono base b)
    (hk : ∀ a c, Track base (nextId b) c → Run base (k (a, c))) :
    Run base (getArray b n >>= k) := by
  simp only [Run, post_bind, Prod.forall]
  intro a c h
  simpa only [Run] using hk a c (track_pre hb (array_track b n (a, c) h))

omit [JlScalar T] in
private theorem value_run {A : Type} (base : Buf T) (m : Jl A)
    (k : A → Jl (ResultOk T × Buf T)) (hk : ∀ a, Run base (k a)) :
    Run base (m >>= k) := by
  simp only [Run, post_bind]
  intro a _
  simpa only [Run] using hk a

open Lean Elab Tactic in
elab "alias_step" : tactic => do
  evalTactic (← `(tactic| try simp_all only [Prod.mk.injEq]))
  if (← getGoals).isEmpty then return
  let target ← getMainTarget
  if target.isForall then
    evalTactic (← `(tactic| intro h))
  else if target.getAppFn.constName? == some ``Run then
    let m := target.getAppArgs.back!
    let head := m.getAppFn.constName?
    if m.isLet then
      evalTactic (← `(tactic| dsimp only))
    else if head == some ``filled then
      evalTactic (← `(tactic| apply filled_run))
    else if head == some ``retV then
      evalTactic (← `(tactic| apply retV_run))
    else if head == some ``retVIf then
      evalTactic (← `(tactic| apply retVIf_run))
    else if head == some ``Pure.pure then
      evalTactic (← `(tactic| apply run_pure))
    else if head == some ``Bind.bind then
      let args := m.getAppArgs
      let source := args[args.size - 2]!
      if source.getAppFn.constName? == some ``getArray then
        evalTactic (← `(tactic| apply array_run))
      else
        evalTactic (← `(tactic| apply value_run))
    else
      evalTactic (← `(tactic| split))
  else
    evalTactic (← `(tactic| first | assumption | exact mono_refl _ | exact (And.left ‹Track _ _ _›) | exact track_post (by assumption) (by assumption) | exact track_pre (by assumption) (by assumption)))

open Lean Elab Tactic in
elab "alias_leaf" : tactic => do
  while !(← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals alias_step))

private theorem deg1L2_run (cx : Ctx) (X : JMat T) (f fl : List T → T)
    (ll lr : Tree T) (b : Buf T) : Run b (deg1L2 cx X f fl ll lr b) := by
  unfold deg1L2
  alias_leaf

private theorem deg1L1_run (cx : Ctx) (X : JMat T) (f fl : List T → T)
    (ll : Tree T) (b : Buf T) : Run b (deg1L1 cx X f fl ll b) := by
  unfold deg1L1
  alias_leaf

private theorem deg2L0R0_run (cx : Ctx) (X : JMat T) (f : List T → T)
    (l r : Tree T) (b : Buf T) : Run b (deg2L0R0 cx X f l r b) := by
  unfold deg2L0R0
  alias_leaf

private theorem deg2L0_run (base b : Buf T) (cx : Ctx) (X : JMat T)
    (f : List T → T) (l : Tree T) (cum : JVec T) (id : Ident)
    (h : Track base id b) : Run base (deg2L0 cx X f l cum id b) := by
  unfold deg2L0
  alias_leaf

private theorem deg2R0_run (base b : Buf T) (cx : Ctx) (X : JMat T)
    (f : List T → T) (r : Tree T) (cum : JVec T) (id : Ident)
    (h : Track base id b) : Run base (deg2R0 cx X f r cum id b) := by
  unfold deg2R0
  alias_leaf

private theorem branch0_run (cx : Ctx) (X : JMat T) (f g : List T → T)
    (s : Side) (l1 l2 l3 : Tree T) (b : Buf T) :
    Run b (branch0 cx X f g s l1 l2 l3 b) := by
  unfold branch0
  alias_leaf

private theorem checked_run (base b : Buf T) (cx : Ctx)
    (ev : Buf T → Jl (ResultOk T × Buf T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T))
    (hb : Mono base b) (he : ∀ c, Run c (ev c))
    (hk : ∀ x id c, Mono b c → Track base id c → Run base (k x id c)) :
    Run base (checked cx ev k b) := by
  simp only [checked, Run, post_bind, Prod.forall]
  intro r c h
  have he' : Post (ev b) (fun p => Track b p.1.id p.2) := by
    simpa only [Run] using he b
  have hr : Track b r.id c := he' (r, c) h
  have ht := track_pre hb hr
  split
  · simpa only [post_pure] using ht
  · split
    · simpa only [post_pure] using ht
    · simpa only [Run] using hk r.x r.id c hr.1 ht

private theorem unfused1_run (cx : Ctx) (fop : Jl (List T → T))
    (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (he : ∀ c, Run c (ev c)) : Run b (unfused1 cx fop ev b) := by
  unfold unfused1
  apply checked_run _ _ _ _ _ (mono_refl _) he
  intro x id c hm ht
  alias_leaf

private theorem unfused2_run (cx : Ctx) (fop : Jl (List T → T))
    (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (hl : ∀ c, Run c (evL c)) (hr : ∀ c, Run c (evR c)) :
    Run b (unfused2 cx fop evL evR b) := by
  unfold unfused2
  apply checked_run _ _ _ _ _ (mono_refl _) hl
  intro xl id c hm ht
  apply checked_run _ _ _ _ _ hm hr
  intro xr rid d hn hu
  alias_leaf

open Lean Elab Tactic in
elab "alias_dispatch" : tactic => do
  while !(← getGoals).isEmpty do
    evalTactic (← `(tactic| all_goals first
      | assumption
      | apply deg1L2_run
      | apply deg1L1_run
      | apply deg2L0R0_run
      | apply branch0_run
      | apply unfused1_run
      | apply unfused2_run
      | apply deg2L0_run
      | apply deg2R0_run
      | apply checked_run
      | alias_step))

private theorem deg1Dispatch_run (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (c : Tree T) (ev : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (he : ∀ a, Run a (ev a)) : Run b (deg1Dispatch cx o X op c ev b) := by
  unfold deg1Dispatch
  alias_dispatch

private theorem deg2Dispatch_run (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (op : Nat) (l r : Tree T) (evL evR : Buf T → Jl (ResultOk T × Buf T)) (b : Buf T)
    (hl : ∀ a, Run a (evL a)) (hr : ∀ a, Run a (evR a)) :
    Run b (deg2Dispatch cx o X op l r evL evR b) := by
  unfold deg2Dispatch
  alias_dispatch

private theorem constPath_run (o : OpEnum T) (X : JMat T) (t : Tree T) (b : Buf T)
    (early : Bool) : Run b (constPath o X t b early) := by
  unfold constPath
  split
  · simp [Run, Post]
  · alias_leaf

private def ChildTrack (b : Buf T) :
    ((ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T)) → Prop
  | .inl (r, c) => Track b r.id c
  | .inr (xs, c) => Mono b c ∧ ∀ p ∈ xs, Track b p.2 c

private theorem children_run (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (cs : List (Tree T)) (ih : ∀ c ∈ cs, ∀ b, Run b (evalT cx o X c b)) :
    ∀ b, Post (evalChildren cx o X cs b) (ChildTrack b) := by
  induction cs with
  | nil => intro b; simp [evalChildren, Post, ChildTrack, Mono]
  | cons c cs hi =>
    intro b
    simp only [evalChildren, post_bind, Prod.forall]
    intro r d h
    have hc : Post (evalT cx o X c b) (fun p => Track b p.1.id p.2) := by
      simpa only [Run] using ih c (by simp) b
    have ht := hc (r, d) h
    split
    · simpa only [post_pure, ChildTrack] using ht
    · split
      · simpa only [post_pure, ChildTrack] using ht
      · simp only [post_bind]
        intro res hr
        have hs := hi (fun t hm => ih t (by simp [hm])) d res hr
        cases res with
        | inl p =>
          rcases p with ⟨r', e⟩
          simpa only [post_pure, ChildTrack] using track_pre ht.1 hs
        | inr p =>
          rcases p with ⟨xs, e⟩
          simp only [post_pure, ChildTrack]
          refine ⟨mono_trans ht.1 hs.1, ?_⟩
          intro p hp
          cases hp with
          | head => exact track_post ht hs.1
          | tail _ hp => exact track_pre ht.1 (hs.2 p hp)

omit [JlScalar T] in
private theorem degnFinish_run (o : OpEnum T) (d op : Nat) (base : Buf T)
    (res : (ResultOk T × Buf T) ⊕ (List (JVec T × Ident) × Buf T))
    (h : ChildTrack base res) : Run base (degnFinish o d op res) := by
  cases res with
  | inl p => rcases p with ⟨r, b⟩; exact run_pure base b r h
  | inr p =>
    rcases p with ⟨xs, b⟩
    cases xs with
    | nil =>
      simp only [degnFinish, Run, post_bind]
      intro f hf
      simp [degnEval, Post]
    | cons x xs =>
      have ht : Track base x.2 b := h.2 x (by simp)
      simp only [degnFinish, Run, post_bind]
      intro f hf out hout
      simpa only [post_pure, List.head?_cons, Option.map_some, Option.getD_some] using ht

private theorem eval_run (cx : Ctx) (o : OpEnum T) (X : JMat T) (t : Tree T) :
    ∀ b, Run b (evalT cx o X t b) := by
  induction t using Tree.induction with
  | hc v =>
    intro b
    simp only [evalT, Run, post_bind, Prod.forall, post_pure]
    intro a c h
    exact filled_track b v X.ncols (a, c) h
  | hf f =>
    intro b
    simp only [evalT, Run, post_bind, Prod.forall, post_pure]
    intro _ _ a c h
    exact feature_track b X f (a, c) h
  | hb op cs ih =>
    intro b
    unfold evalT
    split
    · exact constPath_run o X (.branch op cs) b cx.earlyExit
    · cases cs with
      | nil => simp [Run, Post]
      | cons c cs =>
        have hc := ih c (by simp)
        cases cs with
        | nil => exact deg1Dispatch_run cx o X op c _ b hc
        | cons d ds =>
          have hd := ih d (by simp)
          cases ds with
          | nil => exact deg2Dispatch_run cx o X op c d _ _ b hc hd
          | cons e es =>
            simp only
            split
            · exact deg2Dispatch_run cx o X op c d _ _ b hc hd
            · simp only [Run, post_bind]
              intro res hr
              have ht := children_run cx o X (c :: d :: e :: es) ih b res hr
              simpa only [Run] using degnFinish_run o (List.length (e :: es) + 2) op b res ht

/-- Every successful unbuffered evaluation returns a fresh array and leaves the
buffer `nothing`. -/
theorem aliasFresh_of_ok {T : Type} [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (t : Tree T) (r : ResultOk T) (b : Buf T) (h : evalT cx o X t .none = .ok (r, b)) :
    r.id = .fresh ∧ b = .none := by
  have he : Post (evalT cx o X t .none) (fun p => Track .none p.1.id p.2) := by
    simpa only [Run] using eval_run cx o X t .none
  have ht := he (r, b) h
  have hb : b = .none := by
    cases b <;> simp_all [Track, Mono, Buf.isNone]
  subst b
  refine ⟨?_, rfl⟩
  cases hi : r.id <;> simp_all [Track, IdOK, Buf.isNone]

/-- Every successful buffered evaluation returns a slot handed out in this call. -/
theorem aliasSlots_of_ok {T : Type} [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (t : Tree T) (b : Buf T) (r : ResultOk T) (c : Buf T) (hb : b.isNone = false)
    (h : evalT cx o X t b = .ok (r, c)) :
    c.isNone = false ∧ ∃ k, r.id = .slot k ∧ b.idx < k ∧ k ≤ c.idx := by
  have he : Post (evalT cx o X t b) (fun p => Track b p.1.id p.2) := by
    simpa only [Run] using eval_run cx o X t b
  have ht := he (r, c) h
  refine ⟨ht.1.2 ▸ hb, ?_⟩
  cases hi : r.id with
  | fresh => simp [Track, hi, IdOK, hb] at ht
  | slot k =>
    have hid : b.isNone = false ∧ b.idx < k ∧ k ≤ c.idx := by
      simpa only [IdOK, hi] using ht.2
    exact ⟨k, rfl, hid.2.1, hid.2.2⟩

/-- Two successful evaluations sharing a buffer return different slots. -/
theorem aliasSuccessive_of_ok {T : Type} [JlScalar T] (cx : Ctx) (o : OpEnum T) (X : JMat T)
    (t1 t2 : Tree T) (b b1 b2 : Buf T) (r1 r2 : ResultOk T) (hb : b.isNone = false)
    (h1 : evalT cx o X t1 b = .ok (r1, b1)) (h2 : evalT cx o X t2 b1 = .ok (r2, b2)) :
    r1.id ≠ r2.id := by
  obtain ⟨hb1, k1, hi1, _, hk1⟩ := aliasSlots_of_ok cx o X t1 b r1 b1 hb h1
  obtain ⟨_, k2, hi2, hk2, _⟩ := aliasSlots_of_ok cx o X t2 b1 r2 b2 hb1 h2
  rw [hi1, hi2]
  intro h
  cases h
  omega

theorem evalGenericExposure_proof : evalGenericExposure := by
  intro V o throw x X f v
  refine ⟨?_, rfl, rfl⟩
  intro hf hx
  have hindex : f - 1 < x.size := by omega
  have hget : x[f - 1]? = some x[f - 1] := Array.getElem?_eq_getElem hindex
  simp [genEvalVec, genCatch, gen1, hf, hget]

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

private def tinyInput : JMat Nat := ⟨1, 1, #[7], rfl⟩
private def tinyOps : OpEnum Nat := ⟨[]⟩
private def tinyBuf1 : Buf Nat := .vec #[JVec.fill 1 0] 1
private def tinyBuf2 : Buf Nat := .vec #[JVec.fill 1 0, JVec.fill 1 0] 2
private def tinyResult (id : Ident) : ResultOk Nat := ⟨JVec.fill 1 7, true, id⟩

example : ∃ r b, evalT {} tinyOps tinyInput (.const 7) .none = .ok (r, b) ∧
    r.id = .fresh ∧ b = .none := by
  refine ⟨tinyResult .fresh, .none, rfl, ?_⟩
  exact aliasFresh_of_ok {} tinyOps tinyInput (.const 7) _ _ rfl

example : ∃ r b, (Buf.vec #[] 0 : Buf Nat).isNone = false ∧
    evalT {} tinyOps tinyInput (.const 7) (.vec #[] 0) = .ok (r, b) ∧
    b.isNone = false ∧ ∃ k, r.id = .slot k ∧ 0 < k ∧ k ≤ b.idx := by
  refine ⟨tinyResult (.slot 1), tinyBuf1, rfl, rfl, ?_⟩
  exact aliasSlots_of_ok {} tinyOps tinyInput (.const 7)
    (.vec #[] 0) (tinyResult (.slot 1)) tinyBuf1 rfl rfl

example : ∃ r1 r2 b1 b2, (Buf.vec #[] 0 : Buf Nat).isNone = false ∧
    evalT {} tinyOps tinyInput (.const 7) (.vec #[] 0) = .ok (r1, b1) ∧
    evalT {} tinyOps tinyInput (.const 7) b1 = .ok (r2, b2) ∧ r1.id ≠ r2.id := by
  refine ⟨tinyResult (.slot 1), tinyResult (.slot 2), tinyBuf1, tinyBuf2, rfl, rfl, rfl, ?_⟩
  exact aliasSuccessive_of_ok {} tinyOps tinyInput (.const 7) (.const 7)
    (.vec #[] 0) tinyBuf1 tinyBuf2 _ _ rfl rfl rfl

example : 1 ≤ (1 : Nat) ∧ 1 ≤ (#[7] : JVec Nat).size ∧
    genEvalVec (⟨[]⟩ : GOpEnum Nat) false (.feature 1) #[7] = .ok (some 7, true) ∧
    genEvalVec (⟨[]⟩ : GOpEnum Nat) false (.const 7) #[7] = .ok (some 7, true) ∧
    genEvalMat (⟨[]⟩ : GOpEnum Nat) false (.const 7) tinyInput =
      .ok (some (JVec.fill 1 7), true) := by
  have h := evalGenericExposure_proof Nat ⟨[]⟩ false #[7] tinyInput 1 7
  exact ⟨by decide, by decide, h.1 (by decide) (by decide), h.2.1, h.2.2⟩

end DynExpr.Eval
