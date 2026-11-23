import DynExpr.ParamStruct.Properties

namespace DynExpr.ParamStruct

private theorem mapM_congr_local {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons, List.mapM_cons, h a (by simp)]
    rw [ih (by intro b hb; exact h b (by simp [hb]))]

private theorem mapM_map_local {α β γ : Type} (xs : List α)
    (f : α → β) (g : β → Option γ) : (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, ih]

/-- For every tree and arbitrary operator enum, conversion preserves its scalar
denotation under the shifted feature binding. UInt16 wrapping is explicit,
so `FeatureShift` gives ordinary addition on representable feature ranges. -/
def GeneralConvertedDenotation : Prop := ∀ (np : UInt16) (o : OpEnum JF)
    (y : Nat → Option JF) (t : PTree),
  (convertTree np t).denote o y =
    denoteP o (fun i => y ((UInt16.ofNat i + np).toNat)) y t

theorem generalConvertedDenotation_proven : GeneralConvertedDenotation := by
  intro np o y t
  induction t using Tree.induction with
  | hc v => cases v <;> simp [convertTree, Tree.denote, denoteP]
  | hf i => simp [convertTree, Tree.denote, denoteP]
  | hb op cs ih =>
    simp only [convertTree, Tree.denote, denoteP, List.length_map]
    rw [mapM_map_local]
    rw [mapM_congr_local cs _ _ ih]

private theorem write_read_self (heap : Heap JF) (a : Addr) (v : JF)
    (hr : heap.read a = .ok v) : heap.write a v = .ok heap := by
  have hc : heap.cells a = some v := by
    unfold Heap.read at hr
    cases hs : heap.cells a with
    | none => simp [hs] at hr
    | some w => simp [hs] at hr; subst w; rfl
  have heq : (fun b => if b = a then some v else heap.cells b) = heap.cells := by
    funext b
    by_cases hb : b = a
    · subst b; simp [hc]
    · simp [hb]
  simp [Heap.write, hc, heq]

private theorem write_constants_restore (heap : Heap JF) (refs : List Addr)
    (vs : List JF) (hr : refs.mapM heap.read = .ok vs) :
    writeConstants heap refs vs = .ok heap := by
  induction refs generalizing vs with
  | nil => simp [List.mapM_nil] at hr; subst vs; rfl
  | cons a as ih =>
    cases ha : heap.read a with
    | error err => simp [List.mapM_cons, ha] at hr
    | ok v =>
      cases hs : as.mapM heap.read with
      | error err => simp [List.mapM_cons, ha, hs] at hr
      | ok tail =>
        simp [List.mapM_cons, ha, hs] at hr
        subst vs
        simp [writeConstants, write_read_self heap a v ha, ih tail hs]

/-- Setting the getter's constants leaves the heap and parameter matrix
unchanged, even with repeated references to the same mutable constant. -/
def ConstantsGetSet : Prop := ∀ s : ConstantState, ∀ vs,
  getConstants s = .ok vs → setConstants s vs = .ok s

theorem constantsGetSet_proven : ConstantsGetSet := by
  intro s vs h
  cases hm : s.refs.mapM s.heap.read with
  | error err => simp [getConstants, hm] at h
  | ok cs =>
    simp [getConstants, hm] at h
    subst vs
    have hl : cs.length = s.refs.length := by
      have length_mapM : ∀ refs : List Addr, ∀ cs : List JF,
          refs.mapM s.heap.read = .ok cs → cs.length = refs.length := by
        intro refs
        induction refs with
        | nil => intro cs hc; simp at hc; subst cs; rfl
        | cons a as ih =>
          intro cs hc
          cases ha : s.heap.read a with
          | error err => simp [List.mapM_cons, ha] at hc
          | ok v =>
            cases hs : as.mapM s.heap.read with
            | error err => simp [List.mapM_cons, ha, hs] at hc
            | ok tail =>
              simp [List.mapM_cons, ha, hs] at hc
              subst cs
              simp [ih tail hs]
      exact length_mapM s.refs cs hm
    have takeEq : (cs ++ s.params).take s.refs.length = cs := by
      rw [← hl]; simp
    have dropEq : (cs ++ s.params).drop s.refs.length = s.params := by
      rw [← hl]; simp
    have enough : ¬ (cs ++ s.params).length ≠ s.refs.length + s.params.length := by
      simp [← hl]
    simp only [setConstants, if_neg enough, takeEq, dropEq,
      write_constants_restore s.heap s.refs cs hm, jl_bind_ok,
      arrayRoundtrip_proven s.params s.params rfl]
    rfl

example : getConstants ⟨Heap.empty, [], [.fin 1]⟩ = .ok [.fin 1] := rfl

/-- Independent scalar references retain independent values under an update,
src/ParametricExpression.jl:276-279. The ordinary node source has no aliases. -/
def IndependentConstantsUpdate : Prop := ∀ h h' : Heap JF,
    ∀ refs : List Addr, ∀ values,
  refs.Nodup → writeConstants h refs values = .ok h' →
  refs.mapM h'.read = .ok values

theorem independentConstantsUpdate_proven : IndependentConstantsUpdate :=
  writeConstants_read_values

/-- Static constants precede matrix entries, which remain in column-major order. -/
def ConstantsFlattenOrder : Prop := ∀ s : ConstantState, ∀ constants,
  s.refs.mapM s.heap.read = .ok constants →
  getConstants s = .ok (constants ++ s.params)

theorem constantsFlattenOrder_proven : ConstantsFlattenOrder := by
  intro s constants h
  simp [getConstants,h]

end DynExpr.ParamStruct
