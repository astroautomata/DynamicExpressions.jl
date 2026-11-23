import DynExpr.StringsParse.Roundtrip.Grammar

/-! Imaginary-unit normalization of the `Meta.parse` syntax
(`src/Parse.jl:219-249`) maps it to the syntax of the expected tree. -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

theorem toSurf_literal {ops : Operators} {names : List String} {u : Tree Scalar} {v : Scalar}
    (h : toSurf ops names u = .literal v) : u = .const v := by
  match u, h with
  | .const w, h => simp only [toSurf, Surface.literal.injEq] at h; rw [h]
  | .feature _, h => simp [toSurf] at h
  | .branch _ [], h => simp [toSurf] at h
  | .branch _ [_], h => simp [toSurf] at h
  | .branch _ [_, _], h => simp [toSurf] at h
  | .branch _ (_ :: _ :: _ :: _), h => simp [toSurf] at h

/-- Literal syntax arises exactly from folded real constants. -/
theorem surf_literal {ops : Operators} {names : List String} (t : Tree Scalar)
    (ha : Admissible ops names t) :
    (∀ v, surf ops names t = .literal v → ∃ x, v = .real x ∧ expect ops t = .const (.real x)) ∧
    (∀ x, expect ops t = .const (.real x) → surf ops names t = .literal (.real x)) := by
  induction t using Tree.induction with
  | hc v =>
    constructor
    · intro w h
      cases v with
      | real x =>
        simp only [surf, Surface.literal.injEq] at h
        subst h
        exact ⟨x, rfl, rfl⟩
      | float32 x => simp [Admissible, CleanConst] at ha
      | complex re im =>
        cases re <;> cases im <;> first
          | (simp [Admissible, CleanConst] at ha; done)
          | (simp [surf] at h)
    · intro x h
      simp only [expect, Tree.const.injEq] at h
      subst h
      rfl
  | hf k =>
    exact ⟨fun v h => by simp [surf] at h, fun x h => by simp [expect] at h⟩
  | hb idx cs ih =>
    simp only [Admissible] at ha
    match cs, ih, ha with
    | [c], ih, ha =>
      obtain ⟨ih1, ih2⟩ := ih c (by simp) (ha c (by simp))
      constructor
      · intro v h
        simp only [surf] at h
        split at h
        · split at h
          · rename_i w hw
            obtain ⟨x, rfl, hx⟩ := ih1 w hw
            simp only [Surface.literal.injEq] at h
            subst h
            simp only [expect, hx, unaryFold]
            by_cases hm : (opName ops 1 idx == "-") = true
            · exact ⟨-x, by simp [hm, Scalar.neg], by simp [hm]⟩
            · have hp : (opName ops 1 idx == "+") = true := by simp_all
              exact ⟨x, by simp [hm], by simp [hm, hp]⟩
          · simp at h
        · simp at h
      · intro x h
        simp only [expect, unaryFold] at h
        split at h
        · rename_i v hv
          have hs := ih2 v hv
          split at h
          · rename_i hm
            simp only [Tree.const.injEq, Scalar.real.injEq] at h
            subst h
            simp [surf, hs, hm, Scalar.neg]
          · split at h
            · rename_i hm hp
              simp only [Tree.const.injEq, Scalar.real.injEq] at h
              subst h
              simp [surf, hs, hp, hm]
            · simp at h
        · simp at h
    | [a, b], _, _ =>
      constructor
      · intro v h; simp [surf] at h
      · intro x h
        simp only [expect, binaryFold] at h
        split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp at h
    | [], _, _ => exact ⟨fun v h => by simp [surf] at h, fun x h => by simp [expect] at h⟩
    | _ :: _ :: _ :: _, _, _ => exact ⟨fun v h => by simp [surf] at h, fun x h => by simp [expect] at h⟩

theorem normalizeCall_single (n : String) (x : Surface) : normalizeCall n [x] = .call n [x] := by
  unfold normalizeCall
  split <;> simp_all

theorem toSurf_pair_literal {ops : Operators} {names : List String} {a b : Tree Scalar}
    {v w : Scalar} (h : [toSurf ops names a, toSurf ops names b] = [.literal v, .literal w]) :
    a = .const v ∧ b = .const w := by
  simp only [List.cons.injEq, and_true] at h
  exact ⟨toSurf_literal h.1, toSurf_literal h.2⟩

theorem normalizeCall_toSurf {ops : Operators} {names : List String} (idx : Nat) (a b : Tree Scalar) :
    normalizeCall (opName ops 2 idx) [toSurf ops names a, toSurf ops names b] =
      toSurf ops names (binaryFold (opName ops 2 idx) idx a b) := by
  unfold normalizeCall
  split
  next x y hn hl => obtain ⟨rfl, rfl⟩ := toSurf_pair_literal hl; rw [hn]; rfl
  next x y hn hl => obtain ⟨rfl, rfl⟩ := toSurf_pair_literal hl; rw [hn]; rfl
  next x y hn hl => obtain ⟨rfl, rfl⟩ := toSurf_pair_literal hl; rw [hn]; rfl
  next x y hn hl => obtain ⟨rfl, rfl⟩ := toSurf_pair_literal hl; rw [hn]; rfl
  next x y hn hl => obtain ⟨rfl, rfl⟩ := toSurf_pair_literal hl; rw [hn]; rfl
  next n1 n2 n3 n4 n5 =>
    unfold binaryFold
    split
    next =>
      split
      next hp => exact absurd rfl (n1 _ _ (beq_iff_eq.mp hp))
      next =>
        split
        next _ hm => exact absurd rfl (n3 _ _ (beq_iff_eq.mp hm))
        next =>
          split
          next _ _ hs => exact absurd rfl (n4 _ _ (beq_iff_eq.mp hs))
          next => rfl
    next =>
      split
      next hp => exact absurd rfl (n2 _ _ (beq_iff_eq.mp hp))
      next =>
        split
        next _ hs => exact absurd rfl (n5 _ _ (beq_iff_eq.mp hs))
        next => rfl
    next => rfl

theorem normalize_literal (names : Option (List String)) (v : Scalar) :
    normalize names (.literal v) = .literal v := by
  unfold normalize
  rfl

theorem normalize_symbol_mem {names : List String} {s : String} (h : names.contains s = true) :
    normalize (some names) (.symbol s) = .symbol s := by
  unfold normalize normalizeSymbol
  have hc : ((some names).map (fun ns => ns.contains s)).getD false = true := h
  rw [if_pos hc]

theorem normalize_call (names : Option (List String)) (n : String) (args : List Surface) :
    normalize names (.call n args) = normalizeCallExpr n (normalizeArgs names args) := by
  unfold normalize
  rfl

theorem normalize_im {names : List String} (him : names.contains "im" = false) :
    normalize (some names) (.symbol "im") = .literal (.complex (.fin 0) (.fin 1)) := by
  unfold normalize normalizeSymbol
  have hc : ¬ (((some names).map (fun ns => ns.contains "im")).getD false = true) := by
    show ¬ (names.contains "im" = true)
    rw [him]
    decide
  rw [if_neg hc, if_pos (by decide)]

theorem normalizeArgs_cons (names : Option (List String)) (s : Surface) (ss : List Surface) :
    normalizeArgs names (s :: ss) = normalize names s :: normalizeArgs names ss := by
  rw [normalizeArgs]

theorem normalizeArgs_nil (names : Option (List String)) : normalizeArgs names [] = [] := by
  rw [normalizeArgs]

theorem normalizeCallExpr_pair (n : String) (a b : Surface) :
    normalizeCallExpr n [a, b] = normalizeCall n [a, b] := rfl

theorem normalizeCallExpr_finite (n : String) {a : Surface} (h : nonfiniteReal a = none) :
    normalizeCallExpr n [a] = .call n [a] := by
  simp only [normalizeCallExpr, h]
  exact normalizeCall_single n a

theorem complex_value (r i : Rat) :
    (if i.num < 0 then
        Scalar.complex (.fin r) (-(JF.fin (imagMag i) * JF.fin 1))
      else Scalar.complex (.fin r) (JF.fin (imagMag i) * JF.fin 1)) =
      Scalar.complex (.fin r) (.fin i) := by
  unfold imagMag
  by_cases h : i.num < 0
  · simp only [h, ↓reduceIte]
    show Scalar.complex (.fin r) (.fin (-(-i * 1))) = _
    rw [Rat.mul_one, Rat.neg_neg]
  · simp only [h, ↓reduceIte]
    show Scalar.complex (.fin r) (.fin (i * 1)) = _
    rw [Rat.mul_one]

theorem expect_const_finite {ops : Operators} {names : List String} (t : Tree Scalar)
    (ha : Admissible ops names t) :
    ∀ v, expect ops t = .const v →
      (∃ q, v = .real (.fin q)) ∨ (∃ r i, v = .complex (.fin r) (.fin i)) := by
  induction t using Tree.induction with
  | hc w =>
    intro v h
    simp only [expect, Tree.const.injEq] at h
    subst h
    match w, ha with
    | .real (.fin q), _ => exact Or.inl ⟨q, rfl⟩
    | .complex (.fin r) (.fin i), _ => exact Or.inr ⟨r, i, rfl⟩
    | .real .nan, ha => simp [Admissible, CleanConst] at ha
    | .real .posInf, ha => simp [Admissible, CleanConst] at ha
    | .real .negInf, ha => simp [Admissible, CleanConst] at ha
    | .float32 _, ha => simp [Admissible, CleanConst] at ha
    | .complex .nan _, ha => simp [Admissible, CleanConst] at ha
    | .complex .posInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex .negInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .nan, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .posInf, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .negInf, ha => simp [Admissible, CleanConst] at ha
  | hf k => intro v h; simp [expect] at h
  | hb idx cs ih =>
    intro v h
    simp only [Admissible] at ha
    match cs, ih, ha with
    | [c], ih, ha =>
      have hc := ih c (by simp) (ha c (by simp))
      simp only [expect] at h
      unfold unaryFold at h
      split at h
      · rename_i w hw
        rcases hc _ hw with ⟨q, hq⟩ | ⟨r, i, hq⟩
        · cases hq
          split at h
          · simp only [Tree.const.injEq] at h; subst h; exact Or.inl ⟨-q, rfl⟩
          · split at h
            · simp only [Tree.const.injEq] at h; subst h; exact Or.inl ⟨q, rfl⟩
            · simp at h
        · cases hq
      · simp at h
    | [a, b], ih, ha =>
      have hia := ih a (by simp) (ha a (by simp))
      have hib := ih b (by simp) (ha b (by simp))
      simp only [expect] at h
      unfold binaryFold at h
      split at h
      next x y hx hy =>
        rcases hia _ hx with ⟨q, hq⟩ | ⟨_, _, hq⟩
        · rcases hib _ hy with ⟨_, hq'⟩ | ⟨r', i', hq'⟩
          · cases hq'
          · cases hq; cases hq'
            repeat' split at h
            all_goals (try simp only [Tree.const.injEq] at h)
            all_goals first | (subst h; exact Or.inr ⟨_, _, rfl⟩) | simp at h
        · cases hq
      next x y hx hy =>
        rcases hia _ hx with ⟨_, hq⟩ | ⟨r', i', hq⟩
        · cases hq
        · rcases hib _ hy with ⟨q, hq'⟩ | ⟨_, _, hq'⟩
          · cases hq; cases hq'
            repeat' split at h
            all_goals (try simp only [Tree.const.injEq] at h)
            all_goals first | (subst h; exact Or.inr ⟨_, _, rfl⟩) | simp at h
          · cases hq'
      next => simp at h
    | [], _, _ => simp [expect] at h
    | _ :: _ :: _ :: _, _, _ => simp [expect] at h

/-- The nonfinite unary fold never applies to the syntax of an expected tree. -/
theorem nonfiniteReal_toSurf {ops : Operators} {names : List String} (t : Tree Scalar)
    (ha : Admissible ops names t) : nonfiniteReal (toSurf ops names (expect ops t)) = none := by
  cases he : expect ops t with
  | const v =>
    rcases expect_const_finite t ha v he with ⟨q, rfl⟩ | ⟨r, i, rfl⟩ <;> rfl
  | feature k => rfl
  | branch idx cs =>
    match cs with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | _ :: _ :: _ :: _ => rfl

/-- Normalization maps the parsed syntax to the syntax of the expected tree. -/
theorem normalize_surf {ops : Operators} {names : List String} (hn : CleanNames names)
    (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length) (ha : Admissible ops names t) :
    normalize (some names) (surf ops names t) = toSurf ops names (expect ops t) := by
  induction t using Tree.induction with
  | hc v =>
    match v, ha with
    | .real x, _ => exact normalize_literal _ _
    | .complex (.fin r) (.fin i), ha =>
      simp only [Admissible, CleanConst, Bool.not_eq_true'] at ha
      have him := ha.1
      simp only [surf, expect, toSurf]
      rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons,
        normalizeArgs_nil, normalize_literal, normalize_call,
        normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil, normalize_literal,
        normalize_im him]
      simp only [normalizeCallExpr_pair]
      have hstar : normalizeCall "*" [.literal (.real (.fin (imagMag i))),
          .literal (.complex (.fin 0) (.fin 1))] =
          .literal (.complex (.fin 0) (JF.fin (imagMag i) * JF.fin 1)) := by
        first | rfl | simp [normalizeCall] | decide
      rw [hstar]
      rw [← complex_value r i]
      unfold imagSign
      by_cases h : i.num < 0
      · simp only [h, ↓reduceIte]
        first | rfl | simp [normalizeCall]
      · simp only [h, ↓reduceIte]
        first | rfl | simp [normalizeCall]
    | .complex .nan _, ha => simp [Admissible, CleanConst] at ha
    | .complex .posInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex .negInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .nan, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .posInf, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .negInf, ha => simp [Admissible, CleanConst] at ha
    | .float32 _, ha => simp [Admissible, CleanConst] at ha
  | hf k =>
    simp only [Tree.WF] at hw
    simp only [surf, expect, toSurf]
    have hk : k - 1 < names.length := by omega
    apply normalize_symbol_mem
    rw [List.getElem?_eq_getElem hk, Option.getD_some]
    simp [List.getElem_mem]
  | hb idx cs ih =>
    simp only [Tree.WF] at hw
    have ha' := ha
    simp only [Admissible] at ha'
    match cs, ih, hw, ha' with
    | [c], ih, hw, ha' =>
      have hc := ih c (by simp) (hw.2.2 c (by simp)) (ha' c (by simp))
      obtain ⟨l1, l2⟩ := surf_literal (ops := ops) (names := names) c (ha' c (by simp))
      simp only [surf, expect]
      split
      · split
        · rename_i hn' w hw'
          obtain ⟨x, rfl, hx⟩ := l1 w hw'
          rw [hx, normalize_literal]
          by_cases hm : (opName ops 1 idx == "-") = true
          · simp [unaryFold, hm, toSurf, Scalar.neg]
          · have hp : (opName ops 1 idx == "+") = true := by simp_all
            simp [unaryFold, hm, hp, toSurf]
        · rename_i hn' s hs
          have hnot : ∀ x, expect ops c ≠ .const (.real x) := by
            intro x hx
            exact hs _ (l2 x hx)
          have hu : unaryFold (opName ops 1 idx) idx (expect ops c) = .branch idx [expect ops c] := by
            unfold unaryFold
            split
            · rename_i x hx; exact absurd hx (hnot x)
            · rfl
          rw [hu, normalize_call, normalizeArgs_cons, normalizeArgs_nil, hc,
            normalizeCallExpr_finite _ (nonfiniteReal_toSurf c (ha' c (by simp)))]
          rfl
      · rename_i hn'
        have hu : unaryFold (opName ops 1 idx) idx (expect ops c) = .branch idx [expect ops c] := by
          unfold unaryFold
          split
          · simp_all
          · rfl
        rw [hu, normalize_call, normalizeArgs_cons, normalizeArgs_nil, hc,
          normalizeCallExpr_finite _ (nonfiniteReal_toSurf c (ha' c (by simp)))]
        rfl
    | [a, b], ih, hw, ha' =>
      have hia := ih a (by simp) (hw.2.2 a (by simp)) (ha' a (by simp))
      have hib := ih b (by simp) (hw.2.2 b (by simp)) (ha' b (by simp))
      simp only [surf, expect]
      rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons,
        normalizeArgs_nil, hia, hib, normalizeCallExpr_pair, normalizeCall_toSurf]
    | [], _, hw, _ => simp at hw
    | _ :: _ :: _ :: _, _, hw, _ => simp at hw

end DynExpr.StringsParse.Roundtrip
