import DynExpr.StringsParse.Roundtrip.Cases
import DynExpr.StringsParse.Roundtrip.Grammar
import DynExpr.StringsParse.Roundtrip.Rotate

/-! `metaParseTokens` on the token list of every admissible tree yields the
syntax `surf` (`src/Parse.jl:297`). -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-! ## Token facts -/

theorem ne_of_heads {s t : String} {c d : Char} {cs : List Char} (hs : s.toList = c :: cs)
    (ht : t.toList.head? = some d) (hcd : c ≠ d) : s ≠ t := by
  intro he
  rw [he] at hs
  rw [hs] at ht
  simp only [List.head?_cons, Option.some.injEq] at ht
  exact hcd ht

theorem dec_facts {q : Rat} (hq : 0 ≤ q) :
    plainTok (dec q) ∧ (dec q).toList ≠ [] ∧ ∃ c cs, (dec q).toList = c :: cs ∧ c.isDigit = true := by
  obtain ⟨c, cs, hl, hd⟩ := finiteText_nonneg_head hq
  have hne : ∀ (t : String) (d : Char), t.toList.head? = some d → d.isDigit = false → dec q ≠ t := by
    intro t d ht hdd
    exact ne_of_heads hl ht (by intro h; subst h; rw [hd] at hdd; cases hdd)
  refine ⟨⟨hne "(" '(' (by decide) (by decide), hne ")" ')' (by decide) (by decide),
    hne "-" '-' (by decide) (by decide), hne "+" '+' (by decide) (by decide),
    hne "*" '*' (by decide) (by decide), hne "/" '/' (by decide) (by decide),
    hne "^" '^' (by decide) (by decide), hne "," ',' (by decide) (by decide)⟩,
    by simp [dec, hl], c, cs, hl, hd⟩

theorem ident_facts {s : String} (hs : plainName s = true) :
    plainTok s ∧ ∃ c cs, s.toList = c :: cs ∧ (c.isAlpha || c == '_') = true ∧ c.isDigit = false := by
  simp only [plainName, Bool.and_eq_true, Bool.not_eq_true'] at hs
  have ha := hs.1
  unfold asciiIdent at ha
  cases hl : s.toList with
  | nil => rw [hl] at ha; simp at ha
  | cons c cs =>
    rw [hl] at ha
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨⟨h1, _⟩, h3⟩, _⟩ := ha
    have hne : ∀ (t : String) (d : Char), t.toList.head? = some d → (d.isAlpha || d == '_') = false →
        s ≠ t := by
      intro t d ht hdd
      exact ne_of_heads hl ht (by intro h; subst h; rw [h1] at hdd; cases hdd)
    refine ⟨⟨hne "(" '(' (by decide) (by decide), hne ")" ')' (by decide) (by decide),
      hne "-" '-' (by decide) (by decide), hne "+" '+' (by decide) (by decide),
      hne "*" '*' (by decide) (by decide), hne "/" '/' (by decide) (by decide),
      hne "^" '^' (by decide) (by decide), hne "," ',' (by decide) (by decide)⟩,
      c, cs, rfl, h1, h3⟩

theorem span_loop_eq {α : Type} (p : α → Bool) :
    ∀ (l acc : List α), List.span.loop p l acc =
      (acc.reverse ++ (List.span.loop p l []).1, (List.span.loop p l []).2) := by
  intro l
  induction l with
  | nil => intro acc; simp [List.span.loop]
  | cons a l ih =>
    intro acc
    cases h : p a
    · simp [List.span.loop, h]
    · simp only [List.span.loop, h, cond_true]
      rw [ih (a :: acc), ih [a]]
      simp

theorem span_fst_cons {α : Type} (p : α → Bool) (a : α) (l : List α) :
    ((a :: l).span p).1 = if p a then a :: (l.span p).1 else [] := by
  unfold List.span
  cases h : p a
  · simp [List.span.loop, h]
  · simp only [List.span.loop, h, cond_true, ↓reduceIte]
    rw [span_loop_eq p l [a]]
    simp

theorem bind_none_of {α β : Type} {o : Option α} {f : α → Option β} (h : ∀ a, f a = none) :
    o >>= f = none := by
  cases o
  · rfl
  · exact h _

theorem numericToken_ident {s : String} (hs : plainName s = true) : numericToken s = none := by
  obtain ⟨_, c, cs, hl, ha, hd⟩ := ident_facts hs
  have hm : c ≠ '-' ∧ c ≠ '+' ∧ c ≠ '.' := by
    refine ⟨?_, ?_, ?_⟩ <;> (intro h; subst h; exact absurd ha (by decide))
  have hmant : ∀ q : Char → Bool, ((c :: cs).span q).1 = [] ∨ ∃ ms, ((c :: cs).span q).1 = c :: ms := by
    intro q
    rw [span_fst_cons]
    split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  unfold numericToken
  dsimp only
  rw [hl]
  have hc : (c != '.') = true := by simp [hm.2.2]
  rcases hmant (fun c => c != 'e' && c != 'E' && c != 'f') with h | ⟨ms, h⟩ <;> rw [h] <;>
    split <;> apply bind_none_of <;> intro e <;> try dsimp only
  · simp [List.span, List.span.loop]
  · simp [List.span, List.span.loop]
  · simp [hm.1, hm.2.1, span_fst_cons, hc, hd]
  · simp [hm.1, hm.2.1, span_fst_cons, hc, hd]

/-! ## Structural token invariants -/

structure TokFacts (ops : Operators) (names : List String) (t : Tree Scalar) : Prop where
  balBare : Bal (bare ops names t)
  bareNe : bare ops names t ≠ []
  /-- Top-level tokens of the full rendering are never operator positions. -/
  ft : ∀ prev j, (j = 0 ∨ opTok (prev.getD "") = true) → ftAux (full ops names t) prev j 0 = []
  last : ∀ x ∈ (full ops names t).getLast?, opTok x = false
  headMinus : (full ops names t).head? = some "-" → MinusLed ops t = true
  headPlus : (full ops names t).head? = some "+" → PlusLed ops t = true
  headParen : wrapped ops t = false → (full ops names t).head? ≠ some "("
  commaBare : ∀ i, ∀ p ∈ topAux (bare ops names t) i 0, p.2 ≠ ","
  commaFull : ∀ i, ∀ p ∈ topAux (full ops names t) i 0, p.2 ≠ ","

theorem bal_full {ops : Operators} {names : List String} {t : Tree Scalar}
    (h : Bal (bare ops names t)) : Bal (full ops names t) := by
  unfold full; split
  · exact Bal.group h
  · exact h

theorem num_nonneg {q : Rat} (h : ¬ q.num < 0) : 0 ≤ q := Rat.num_nonneg.mp (by omega)
theorem neg_nonneg_of {q : Rat} (h : q.num < 0) : 0 ≤ -q := by
  apply Rat.num_nonneg.mp
  have : (-q).num = -q.num := by simp
  omega

theorem len_pos {α : Type} {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

theorem getLast?_snoc {α : Type} (l : List α) (a : α) : (l ++ [a]).getLast? = some a := by
  simp

theorem last_snoc {α : Type} {l : List α} {a x : α} (hx : x ∈ (l ++ [a]).getLast?) : x = a := by
  rw [getLast?_snoc] at hx
  exact (Option.some.inj hx).symm

/-- Token facts of an infix left operand, with or without the extra pair. -/
theorem lhs_facts {ops : Operators} {names : List String} {n : String} {a : Tree Scalar}
    (Fa : TokFacts ops names a) :
    Bal (lhs ops names n a) ∧ lhs ops names n a ≠ [] ∧
    ftAux (lhs ops names n a) none 0 0 = [] ∧
    (∀ x ∈ (lhs ops names n a).getLast?, opTok x = false) ∧
    (∀ i, ∀ p ∈ topAux (lhs ops names n a) i 0, p.2 ≠ ",") ∧
    (∀ y, y ≠ [] → outerP (lhs ops names n a ++ y) = false) ∧
    (lhsWrap ops n a = false → lhs ops names n a = full ops names a ∧ wrapped ops a = false) := by
  unfold lhs
  cases hw : lhsWrap ops n a
  · have hwa : wrapped ops a = false := by
      unfold lhsWrap at hw
      cases h : wrapped ops a
      · rfl
      · rw [h] at hw; simp at hw
    have hf : full ops names a = bare ops names a := by simp [full, hwa]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨Fa.balBare, Fa.bareNe, ?_, ?_, Fa.commaBare, ?_, fun _ => ⟨hf.symm, hwa⟩⟩
    · rw [← hf]; exact Fa.ft none 0 (Or.inl rfl)
    · rw [← hf]; exact Fa.last
    · intro y _
      apply outerP_head
      cases hb : bare ops names a with
      | nil => exact absurd hb Fa.bareNe
      | cons x xs =>
        have := Fa.headParen hwa
        rw [hf, hb] at this
        simpa using this
  · simp only [↓reduceIte]
    refine ⟨Bal.group Fa.balBare, by simp, ftAux_wrapped Fa.balBare none 0, ?_, ?_, ?_, fun h => by cases h⟩
    · intro x hx; rw [last_snoc hx]; decide
    · intro i p hp; rw [topAux_wrapped Fa.balBare] at hp; simp at hp
    · intro y hy
      have e := outerP_group_more Fa.balBare hy
      simpa using e

theorem lt_of_num {q : Rat} (h : q.num < 0) : q < 0 :=
  Rat.not_le.mp (fun h2 => by have := Rat.num_nonneg.mpr h2; omega)

theorem opTok_plain {t : String} (h : plainTok t) : opTok t = false := plainTok_opTok h

theorem plain_bal {t : String} (h : plainTok t) : t ≠ "(" ∧ t ≠ ")" := ⟨h.1, h.2.1⟩

/-- Facts about a real constant's tokens. -/
theorem realToks_facts (q : Rat) :
    Bal (realToks q) ∧ realToks q ≠ [] ∧
    (∀ prev j, (j = 0 ∨ opTok (prev.getD "") = true) → ftAux (realToks q) prev j 0 = []) ∧
    (∀ x ∈ (realToks q).getLast?, opTok x = false) ∧
    ((realToks q).head? = some "-" ∨ (realToks q).head? = some "+" → q.num < 0) ∧
    (realToks q).head? ≠ some "(" ∧
    (∀ i, ∀ p ∈ topAux (realToks q) i 0, p.2 ≠ ",") := by
  unfold realToks
  by_cases hq : q.num < 0
  · have hd := (dec_facts (neg_nonneg_of hq)).1
    simp only [hq, ↓reduceIte]
    refine ⟨.tok (by decide) (by decide) (Bal.single hd.1 hd.2.1), by simp, ?_, ?_,
      fun _ => by first | exact hq | trivial,
      by simp, ?_⟩
    · intro prev j hj
      have hm : opTok "-" = true := by decide
      simp only [ftAux, ne_beq (show ("-" : String) ≠ "(" by decide),
        ne_beq (show ("-" : String) ≠ ")" by decide), ne_beq hd.1, ne_beq hd.2.1,
        Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Option.getD_some, hm]
      rcases hj with rfl | hj
      · simp
      · simp [hj]
    · intro x hx; simp at hx; subst hx; exact opTok_plain hd
    · intro i p hp
      simp only [topAux, ne_beq (show ("-" : String) ≠ "(" by decide),
        ne_beq (show ("-" : String) ≠ ")" by decide), ne_beq hd.1, ne_beq hd.2.1,
        Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · show ("-" : String) ≠ ","; decide
      · exact hd.2.2.2.2.2.2.2
  · have hd := (dec_facts (num_nonneg hq)).1
    simp only [hq, ↓reduceIte]
    refine ⟨Bal.single hd.1 hd.2.1, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro prev j hj
      simp only [ftAux, ne_beq hd.1, ne_beq hd.2.1, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true]
      rcases hj with rfl | hj
      · simp
      · simp [hj]
    · intro x hx; simp at hx; subst hx; exact opTok_plain hd
    · intro h; simp at h; exact (h.elim hd.2.2.1 hd.2.2.2.1).elim
    · simpa using hd.1
    · intro i p hp
      simp only [topAux, ne_beq hd.1, ne_beq hd.2.1, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact hd.2.2.2.2.2.2.2

theorem opNameOK_facts {n : String} (h : opNameOK n = true) :
    n ≠ "(" ∧ n ≠ ")" ∧ n ≠ "," ∧ (infixName n = false → plainName n = true ∧ plainTok n) := by
  unfold opNameOK at h
  by_cases hi : infixName n = true
  · rcases infixName_cases hi with
      rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, by decide, fun h => by rw [hi] at h; cases h⟩
  · have hp : plainName n = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, hi, or_false] at h
      exact h.elim (fun h => h.1) (fun h => by cases h)
    have hf := (ident_facts hp).1
    exact ⟨hf.1, hf.2.1, hf.2.2.2.2.2.2.2, fun _ => ⟨hp, hf⟩⟩

theorem opName_ok {ops : Operators} (hops : CleanOps ops) {d idx : Nat} (hi : 1 ≤ idx)
    (hl : idx ≤ (table ops d).length) : opNameOK (opName ops d idx) = true := by
  rw [opName_eq hi hl]
  exact ((cleanOps_table hops d).2.2 _ (List.getElem_mem _)).1

theorem table_len {ops : Operators} {d idx : Nat} (hd : d ≠ 0) (h : idx ≤ ops.enum.nops d) :
    idx ≤ (table ops d).length := by
  rw [← nops_table ops d hd]; exact h

/-- Token invariants hold for every admissible tree. -/
theorem tokFacts {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) : TokFacts ops names t := by
  induction t using Tree.induction with
  | hc v =>
    match v, ha with
    | .real (.fin q), _ =>
      obtain ⟨b, ne, ft, last, hs, hp, hc⟩ := realToks_facts q
      have hfull : full ops names (.const (.real (.fin q))) = realToks q := by simp [full, wrapped, bare]
      refine ⟨by simpa [bare] using b, by simpa [bare] using ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfull]; exact ft
      · rw [hfull]; exact last
      · rw [hfull]; intro h; simpa [MinusLed] using hs (Or.inl h)
      · rw [hfull]; intro h
        have hq := hs (Or.inr h)
        have hr : realToks q = ["-", dec (-q)] := by simp [realToks, hq]
        rw [hr] at h
        exact absurd (Option.some.inj h) (by decide)
      · intro _; rw [hfull]; exact hp
      · simpa [bare] using hc
      · rw [hfull]; exact hc
    | .complex (.fin r) (.fin i), _ =>
      obtain ⟨b, ne, ft, last, _, hp, hc⟩ := realToks_facts r
      have hD := (dec_facts (q := imagMag i) (by
        unfold imagMag; split
        · exact neg_nonneg_of ‹_›
        · exact num_nonneg ‹_›)).1
      have hsg : imagSign i ≠ "(" ∧ imagSign i ≠ ")" ∧ imagSign i ≠ "," := by
        unfold imagSign; split <;> exact ⟨by decide, by decide, by decide⟩
      have hbal : Bal (realToks r ++ [imagSign i, dec (imagMag i), "im"]) :=
        b.append (.tok hsg.1 hsg.2.1 (.tok hD.1 hD.2.1 (Bal.single (by decide) (by decide))))
      have hfull : full ops names (.const (.complex (.fin r) (.fin i))) =
          "(" :: (realToks r ++ [imagSign i, dec (imagMag i), "im"]) ++ [")"] := by
        simp [full, wrapped, bare]
      refine ⟨by simpa [bare] using hbal, by simp [bare], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro prev j _; rw [hfull]; exact ftAux_wrapped hbal prev j
      · rw [hfull]; intro x hx; rw [last_snoc hx]; decide
      · rw [hfull]; intro h; simp at h
      · rw [hfull]; intro h; simp at h
      · intro h; simp [wrapped] at h
      · intro j p hp
        simp only [bare] at hp
        rw [topAux_top b] at hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hc j p hp
        · simp only [topAux, ne_beq hsg.1, ne_beq hsg.2.1, ne_beq hD.1, ne_beq hD.2.1,
            Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
            ne_beq (show ("im" : String) ≠ "(" by decide), ne_beq (show ("im" : String) ≠ ")" by decide),
            List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact hsg.2.2
          · exact hD.2.2.2.2.2.2.2
          · show ("im" : String) ≠ ","; decide
      · rw [hfull]; intro j p hp; rw [topAux_wrapped hbal] at hp; simp at hp
    | .complex .nan _, ha => simp [Admissible, CleanConst] at ha
    | .complex .posInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex .negInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .nan, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .posInf, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .negInf, ha => simp [Admissible, CleanConst] at ha
    | .real .nan, ha => simp [Admissible, CleanConst] at ha
    | .real .posInf, ha => simp [Admissible, CleanConst] at ha
    | .real .negInf, ha => simp [Admissible, CleanConst] at ha
    | .float32 _, ha => simp [Admissible, CleanConst] at ha
  | hf k =>
    simp only [Tree.WF] at hw
    have hk : k - 1 < names.length := by omega
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    have hp := (ident_facts (hn.2.2 _ (List.getElem_mem hk))).1
    have hb : bare ops names (.feature k) = [names[k - 1]] := by simp [bare, hname]
    have hfull : full ops names (.feature k) = [names[k - 1]] := by simp [full, wrapped, bare, hname]
    refine ⟨by rw [hb]; exact Bal.single hp.1 hp.2.1, by simp [hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro prev j hj; rw [hfull]
      simp only [ftAux, ne_beq hp.1, ne_beq hp.2.1, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
      rcases hj with rfl | hj
      · simp
      · simp [hj]
    · rw [hfull]; intro x hx; simp at hx; subst hx; exact opTok_plain hp
    · rw [hfull]; intro h; simp at h; exact absurd h hp.2.2.1
    · rw [hfull]; intro h; simp at h; exact absurd h hp.2.2.2.1
    · intro _; rw [hfull]; simpa using hp.1
    · intro j p hq; rw [hb] at hq
      simp only [topAux, ne_beq hp.1, ne_beq hp.2.1, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact hp.2.2.2.2.2.2.2
    · intro j p hq; rw [hfull] at hq
      simp only [topAux, ne_beq hp.1, ne_beq hp.2.1, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact hp.2.2.2.2.2.2.2
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have ha' := ha
    simp only [Admissible] at ha'
    match cs, hl1, hl2, hi2, ih, hcs, ha' with
    | [c], _, _, hi2, ih, hcs, ha' =>
      have F := ih c (by simp) (hcs c (by simp)) (ha' c (by simp))
      have hok := opNameOK_facts (opName_ok hops hi1 (table_len (by simp) hi2))
      generalize hnn' : opName ops 1 idx = n at hok
      have hnn : n = opName ops 1 idx := hnn'.symm
      have hb : bare ops names (.branch idx [c]) = n :: "(" :: bare ops names c ++ [")"] := by
        simp [bare, hnn]
      have hfull : full ops names (.branch idx [c]) = n :: "(" :: bare ops names c ++ [")"] := by
        simp [full, wrapped, bare, hnn]
      have hbal : Bal (n :: "(" :: bare ops names c ++ [")"]) := by
        have := Bal.tok hok.1 hok.2.1 (Bal.group F.balBare)
        simpa using this
      refine ⟨by rw [hb]; exact hbal, by simp [hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro prev j hj; rw [hfull]; exact ftAux_prefix_any hok.1 hok.2.1 F.balBare prev j hj
      · rw [hfull]; intro x hx; rw [last_snoc hx]; decide
      · rw [hfull]; intro h
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
        simp only [MinusLed, ← hnn]; simp [h]
      · rw [hfull]; intro h
        simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
        simp only [PlusLed, ← hnn]; simp [h]
      · intro _; rw [hfull]; simpa using hok.1
      · intro j p hq; rw [hb, topAux_prefix_any hok.1 hok.2.1 F.balBare] at hq
        simp at hq; rw [hq]; exact hok.2.2.1
      · intro j p hq; rw [hfull, topAux_prefix_any hok.1 hok.2.1 F.balBare] at hq
        simp at hq; rw [hq]; exact hok.2.2.1
    | [a, b], _, _, hi2, ih, hcs, ha' =>
      have Fa := ih a (by simp) (hcs a (by simp)) (ha' a (by simp))
      have Fb := ih b (by simp) (hcs b (by simp)) (ha' b (by simp))
      have hok := opNameOK_facts (opName_ok hops hi1 (table_len (by simp) hi2))
      generalize hnn' : opName ops 2 idx = n at hok
      have hnn : n = opName ops 2 idx := hnn'.symm
      by_cases hinf : infixName n = true
      · have L := lhs_facts (n := n) Fa
        have hb : bare ops names (.branch idx [a, b]) =
            lhs ops names n a ++ n :: full ops names b := by
          simp [bare, hnn.symm, hinf, full, lhs]
        have hfull : full ops names (.branch idx [a, b]) =
            "(" :: (lhs ops names n a ++ n :: full ops names b) ++ [")"] := by
          rw [show full ops names (.branch idx [a, b]) = "(" :: bare ops names (.branch idx [a, b]) ++ [")"]
            by simp [full, wrapped, hnn.symm, hinf], hb]
        have hbal : Bal (lhs ops names n a ++ n :: full ops names b) :=
          L.1.append (.tok hok.1 hok.2.1 (bal_full Fb.balBare))
        refine ⟨by rw [hb]; exact hbal, by simp [hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro prev j _; rw [hfull]; exact ftAux_wrapped hbal prev j
        · rw [hfull]; intro x hx; rw [last_snoc hx]; decide
        · rw [hfull]; intro h; simp at h
        · rw [hfull]; intro h; simp at h
        · intro h; simp [wrapped, hnn.symm, hinf] at h
        · intro j p hq
          rw [hb, topAux_top L.1] at hq
          rcases List.mem_append.mp hq with hq | hq
          · exact L.2.2.2.2.1 j p hq
          · simp only [topAux, ne_beq hok.1, ne_beq hok.2.1, Bool.false_eq_true, ↓reduceIte,
              beq_self_eq_true, List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hok.2.2.1
            · exact Fb.commaFull _ p hq
        · rw [hfull]; intro j p hq; rw [topAux_wrapped hbal] at hq; simp at hq
      · have hinf' : infixName n = false := by simpa using hinf
        obtain ⟨_, hpl⟩ := hok.2.2.2 hinf'
        have hb : bare ops names (.branch idx [a, b]) =
            n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"] := by
          simp [bare, hnn.symm, hinf']
        have hfull : full ops names (.branch idx [a, b]) =
            n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"] := by
          simp [full, wrapped, bare, hnn.symm, hinf']
        have hx : Bal (bare ops names a ++ "," :: bare ops names b) :=
          Fa.balBare.append (.tok (by decide) (by decide) Fb.balBare)
        have hbal : Bal (n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"]) := by
          have := Bal.tok hok.1 hok.2.1 (Bal.group hx)
          simpa using this
        refine ⟨by rw [hb]; exact hbal, by simp [hb], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro prev j hj; rw [hfull]; exact ftAux_prefix_any hok.1 hok.2.1 hx prev j hj
        · rw [hfull]; intro x hx; rw [last_snoc hx]; decide
        · rw [hfull]; intro h
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
          exact absurd h hpl.2.2.1
        · rw [hfull]; intro h
          simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h
          exact absurd h hpl.2.2.2.1
        · intro _; rw [hfull]; simpa using hok.1
        · intro j p hq; rw [hb, topAux_prefix_any hok.1 hok.2.1 hx] at hq
          simp at hq; rw [hq]; exact hok.2.2.1
        · intro j p hq; rw [hfull, topAux_prefix_any hok.1 hok.2.1 hx] at hq
          simp at hq; rw [hq]; exact hok.2.2.1
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

/-! ## Parsing the token lists -/

theorem mpt_fuel {fuel : Nat} {ts : List String} (hne : ts ≠ []) (h : ts.length ≤ fuel) :
    ∃ f, fuel = f + 1 ∧ ts.length ≤ f + 1 := by
  cases fuel with
  | zero => cases ts with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at h
  | succ f => exact ⟨f, rfl, h⟩

theorem parse_dec {q : Rat} (hq : 0 ≤ q) (htq : Terminating q) (fuel : Nat) (hf : 1 ≤ fuel) :
    metaParseTokens fuel [dec q] = .ok (.literal (.real (.fin q))) := by
  obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := [dec q]) (by simp) (by simpa using hf)
  rw [mpt_succ, mpt_single _ (dec_facts hq).1]
  unfold dec
  rw [numericToken_finiteText htq]

theorem parse_real {q : Rat} (htq : Terminating q) (fuel : Nat) (hf : (realToks q).length ≤ fuel) :
    metaParseTokens fuel (realToks q) = .ok (.literal (.real (.fin q))) := by
  unfold realToks at hf ⊢
  by_cases hq : q.num < 0
  · simp only [hq, ↓reduceIte] at hf ⊢
    obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := ["-", dec (-q)]) (by simp) hf
    rw [mpt_succ, mpt_neg _ (dec_facts (neg_nonneg_of hq)).1
      (parse_dec (neg_nonneg_of hq) (terminating_neg htq) f (by simp at hf; omega))]
    show Except.ok (Surface.literal (Scalar.real (JF.fin (-(-q))))) = _
    rw [Rat.neg_neg]
  · simp only [hq, ↓reduceIte] at hf ⊢
    exact parse_dec (num_nonneg hq) htq fuel (by simpa using hf)

theorem prefix_surf1 (ops : Operators) (names : List String) (idx : Nat) (c : Tree Scalar) :
    prefixResult (opName ops 1 idx) [surf ops names c] = surf ops names (.branch idx [c]) := by
  unfold prefixResult
  simp only [surf]
  split
  · generalize surf ops names c = s
    cases s <;> rfl
  · rfl

theorem lastOr_ne {x : List String} (hne : x ≠ []) (h : ∀ y ∈ x.getLast?, opTok y = false) :
    opTok ((lastOr x none).getD "") = false := by
  unfold lastOr
  cases hl : x.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
  | some y => exact h y (by simp [hl])

theorem full_of_bare {ops : Operators} {names : List String} {t : Tree Scalar} {s : Surface}
    (hbal : Bal (bare ops names t))
    (hbare : ∀ fuel, (bare ops names t).length ≤ fuel → metaParseTokens fuel (bare ops names t) = .ok s) :
    ∀ fuel, (full ops names t).length ≤ fuel → metaParseTokens fuel (full ops names t) = .ok s := by
  intro fuel hf
  unfold full at hf ⊢
  split
  · rename_i hwr
    simp only [hwr, ↓reduceIte] at hf
    obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := "(" :: bare ops names t ++ [")"]) (by simp) hf
    rw [mpt_succ, List.cons_append, mpt_outer _ hbal (hbare f (by simp at hf; omega))]
  · rename_i hwr
    simp only [hwr, Bool.false_eq_true, ↓reduceIte] at hf
    exact hbare fuel hf

/-- A leading unary `+` whose only top-level operator is `^` applies to the rest
of the tokens (`src/Parse.jl:297`). -/
theorem mpt_plus_high (rec : List String → Jl Surface) {X : List String} {k : Nat}
    (ht : ftAux ("+" :: X) none 0 0 = [(k, "^")]) {s : Surface} (hrec : rec X = .ok s) :
    mptBody rec ("+" :: X) = .ok (.call "+" [s]) := by
  have ho : outerP ("+" :: X) = false := outerP_head (by simp)
  unfold mptBody
  rw [tops_eq, ht]
  simp [ho, hrec]
  try rfl

/-- Tokens of every admissible tree parse to the syntax of its rotated tree;
the second clause carries the statement for the child of a unary call. -/
theorem parse_bare_aux {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) :
    (∀ fuel, (bare ops names t).length ≤ fuel →
      metaParseTokens fuel (bare ops names t) = .ok (surf ops names (rotT ops t))) ∧
    (∀ idx c, t = .branch idx [c] → ∀ fuel, (bare ops names c).length ≤ fuel →
      metaParseTokens fuel (bare ops names c) = .ok (surf ops names (rotT ops c))) := by
  induction t using Tree.induction with
  | hc v =>
    refine ⟨?_, fun _ _ h => by cases h⟩
    match v, ha with
    | .real (.fin q), ha =>
      simp only [Admissible, CleanConst] at ha
      intro fuel hf
      simp only [bare] at hf ⊢
      exact parse_real ha fuel hf
    | .complex (.fin r) (.fin i), ha =>
      simp only [Admissible, CleanConst] at ha
      obtain ⟨_, htr, hti⟩ := ha
      have hmag : 0 ≤ imagMag i := by
        unfold imagMag; split
        · exact neg_nonneg_of ‹_›
        · exact num_nonneg ‹_›
      have htm : Terminating (imagMag i) := by
        unfold imagMag; split
        · exact terminating_neg hti
        · exact hti
      have hmagT : realToks (imagMag i) = [dec (imagMag i)] := by
        have : ¬ (imagMag i).num < 0 := by
          have := Rat.num_nonneg.mpr hmag; omega
        simp [realToks, this]
      obtain ⟨rb, rne, rft, rlast, _, rhp, _⟩ := realToks_facts r
      have hD := (dec_facts hmag).1
      have hsg : imagSign i ≠ "(" ∧ imagSign i ≠ ")" ∧ opTok (imagSign i) = true ∧
          infixName (imagSign i) = true ∧ imagSign i ≠ "^" := by
        unfold imagSign; split <;> exact ⟨by decide, by decide, by decide, by decide, by decide⟩
      intro fuel hf
      simp only [bare] at hf ⊢
      obtain ⟨f, rfl, hf'⟩ := mpt_fuel (ts := realToks r ++ [imagSign i, dec (imagMag i), "im"])
        (by simp) hf
      have ht : ftAux (realToks r ++ imagSign i :: [dec (imagMag i), "im"]) none 0 0 =
          ((realToks r).length, imagSign i) :: [((realToks r).length + 2, "im")] := by
        rw [ftAux_top rb, rft none 0 (Or.inl rfl), List.nil_append]
        have hlo := lastOr_ne rne rlast
        have hpos : 0 < (realToks r).length := len_pos rne
        simp only [ftAux, ne_beq hsg.1, ne_beq hsg.2.1, ne_beq hD.1, ne_beq hD.2.1,
          Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Nat.zero_add, hlo, Option.getD_some,
          hsg.2.2.1, opTok_plain hD, ne_beq (show ("im" : String) ≠ "(" by decide),
          ne_beq (show ("im" : String) ≠ ")" by decide)]
        simp [hpos]
      have hR : metaParseTokens f (realToks r) = .ok (.literal (.real (.fin r))) :=
        parse_real htr f (by simp at hf'; omega)
      have hI : metaParseTokens f [dec (imagMag i), "im"] =
          .ok (.call "*" [.literal (.real (.fin (imagMag i))), .symbol "im"]) := by
        obtain ⟨g, hg, _⟩ := mpt_fuel (fuel := f) (ts := [dec (imagMag i), "im"]) (by simp)
          (by simp at hf' ⊢; omega)
        subst hg
        rw [mpt_succ, mpt_im _ hD (parse_dec hmag htm g (by simp at hf'; omega))]
      have := mpt_infix (metaParseTokens f) (A := realToks r) (B := [dec (imagMag i), "im"])
        hsg.2.2.2.1 rne (outerP_head (by
          cases h : realToks r with
          | nil => exact absurd h rne
          | cons x xs => rw [h] at rhp; simpa using rhp)) [((realToks r).length + 2, "im")]
        (by intro p hp; simp at hp; subst hp; show opCat "im" = false; decide) ht (fun h => absurd h hsg.2.2.2.2) hR hI
      rw [mpt_succ]
      simpa [surf, rotT] using this
    | .complex .nan _, ha => simp [Admissible, CleanConst] at ha
    | .complex .posInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex .negInf _, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .nan, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .posInf, ha => simp [Admissible, CleanConst] at ha
    | .complex (.fin _) .negInf, ha => simp [Admissible, CleanConst] at ha
    | .real .nan, ha => simp [Admissible, CleanConst] at ha
    | .real .posInf, ha => simp [Admissible, CleanConst] at ha
    | .real .negInf, ha => simp [Admissible, CleanConst] at ha
    | .float32 _, ha => simp [Admissible, CleanConst] at ha
  | hf k =>
    refine ⟨?_, fun _ _ h => by cases h⟩
    simp only [Tree.WF] at hw
    have hk : k - 1 < names.length := by omega
    have hpn := hn.2.2 _ (List.getElem_mem hk)
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    intro fuel hf
    simp only [bare, hname] at hf ⊢
    obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := [names[k - 1]]) (by simp) hf
    rw [mpt_succ, mpt_single _ (ident_facts hpn).1, numericToken_ident hpn]
    simp [surf, rotT, hname]
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have ha' := ha
    simp only [Admissible] at ha'
    match cs, hl1, hl2, hi2, ih, hcs, ha' with
    | [c], _, _, hi2, ih, hcs, ha' =>
      have Fc := tokFacts hops hn c (hcs c (by simp)) (ha' c (by simp))
      have IHc := (ih c (by simp) (hcs c (by simp)) (ha' c (by simp))).1
      refine ⟨?_, fun idx' c' h => by
        simp only [Tree.branch.injEq, List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        exact IHc⟩
      have hok := opNameOK_facts (opName_ok hops hi1 (table_len (by simp) hi2))
      intro fuel hf
      have hb : bare ops names (.branch idx [c]) =
          opName ops 1 idx :: "(" :: bare ops names c ++ [")"] := by simp [bare]
      rw [hb] at hf ⊢
      obtain ⟨f, rfl, hf'⟩ := mpt_fuel (ts := opName ops 1 idx :: "(" :: bare ops names c ++ [")"])
        (by simp) hf
      have hargs : (splitC (bare ops names c)).mapM (metaParseTokens f) =
          .ok [surf ops names (rotT ops c)] := by
        rw [splitC_single Fc.bareNe (Fc.commaBare 0)]
        simp [IHc f (by simp at hf'; omega)] <;> rfl
      simp only [List.length_singleton] at hok
      rw [mpt_succ]
      simp only [List.cons_append]
      rw [mpt_prefix _ hok.1 hok.2.1 Fc.balBare _ hargs, prefix_surf1, rotT_unary]
    | [a, b], _, _, hi2, ih, hcs, ha' =>
      have Fa := tokFacts hops hn a (hcs a (by simp)) (ha' a (by simp))
      have Fb := tokFacts hops hn b (hcs b (by simp)) (ha' b (by simp))
      have IHa1 := (ih a (by simp) (hcs a (by simp)) (ha' a (by simp))).1
      have IHa2 := (ih a (by simp) (hcs a (by simp)) (ha' a (by simp))).2
      have IHb1 := (ih b (by simp) (hcs b (by simp)) (ha' b (by simp))).1
      have IHa := And.intro IHa1 (full_of_bare Fa.balBare IHa1)
      have IHb := And.intro IHb1 (full_of_bare Fb.balBare IHb1)
      refine ⟨?_, fun _ _ h => by simp at h⟩
      have hok := opNameOK_facts (opName_ok hops hi1 (table_len (by simp) hi2))
      generalize hnn' : opName ops 2 idx = n at hok
      have hnn : n = opName ops 2 idx := hnn'.symm
      intro fuel hf
      by_cases hinf : infixName n = true
      · by_cases hrot : n = "^" ∧ PlusLed ops a = true
        · obtain ⟨hpow, hpl⟩ := hrot
          subst hpow
          obtain ⟨pidx, c, rfl, hp⟩ := plusLed_shape hpl
          have hwa := hcs (.branch pidx [c]) (by simp)
          simp only [Tree.WF] at hwa
          have hwc : c.WF 2 ops.enum.nops names.length := hwa.2.2 c (by simp)
          have haa := ha' (.branch pidx [c]) (by simp)
          simp only [Admissible] at haa
          have Fc := tokFacts hops hn c hwc (haa c (by simp))
          have IHc := IHa2 pidx c rfl
          have hlw : lhsWrap ops "^" (.branch pidx [c]) = false := by
            simp [lhsWrap, wrapped, MinusLed, hp]
          have hb : bare ops names (.branch idx [.branch pidx [c], b]) =
              "+" :: (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) := by
            have h0 : bare ops names (.branch idx [.branch pidx [c], b]) =
                lhs ops names "^" (.branch pidx [c]) ++ "^" :: full ops names b := by
              simp [bare, hnn.symm, hinf, full, lhs]
            rw [h0]
            simp [lhs, hlw, bare, hp]
          rw [hb] at hf ⊢
          obtain ⟨f, rfl, hf'⟩ := mpt_fuel
            (ts := "+" :: (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b)) (by simp) hf
          have hG : Bal ("(" :: bare ops names c ++ [")"]) := Bal.group Fc.balBare
          have hlG : ∀ p, lastOr ("(" :: bare ops names c ++ [")"]) p = some ")" := by
            intro p; unfold lastOr; rw [getLast?_snoc]
          have hfb : ∀ j, ftAux (full ops names b) (some "^") j 0 = [] :=
            fun j => Fb.ft (some "^") j (Or.inr (by decide))
          have htop : ftAux ("+" :: (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b))
              none 0 0 = [(1 + ("(" :: bare ops names c ++ [")"]).length, "^")] := by
            rw [show "+" :: (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) =
                ["+"] ++ (("(" :: bare ops names c ++ [")"]) ++ (["^"] ++ full ops names b)) from rfl,
              ftAux_top (Bal.single (by decide) (by decide)), ftAux_top hG,
              ftAux_top (Bal.single (by decide) (by decide)), ftAux_wrapped Fc.balBare]
            simp only [hlG]
            rw [show lastOr ["^"] (some ")") = some "^" from rfl, hfb]
            simp [ftAux, lastOr, opTok]
          have hinner : ftAux (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) none 0 0 =
              [(("(" :: bare ops names c ++ [")"]).length, "^")] := by
            rw [show ("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b =
                ("(" :: bare ops names c ++ [")"]) ++ (["^"] ++ full ops names b) from rfl,
              ftAux_top hG, ftAux_top (Bal.single (by decide) (by decide)), ftAux_wrapped Fc.balBare]
            simp only [hlG]
            rw [show lastOr ["^"] (some ")") = some "^" from rfl, hfb]
            simp [ftAux, opTok]
          have hX : ∀ g, (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b).length ≤ g →
              metaParseTokens g (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) =
                .ok (.call "^" [surf ops names (rotT ops c), surf ops names (rotT ops b)]) := by
            intro g hg
            obtain ⟨g, rfl, hg'⟩ := mpt_fuel
              (ts := ("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) (by simp) hg
            have hA : metaParseTokens g ("(" :: bare ops names c ++ [")"]) =
                .ok (surf ops names (rotT ops c)) := by
              obtain ⟨h, rfl, _⟩ := mpt_fuel (fuel := g) (ts := "(" :: bare ops names c ++ [")"])
                (by simp) (by simp at hg' ⊢; omega)
              rw [mpt_succ, List.cons_append, mpt_outer _ Fc.balBare (IHc h (by simp at hg'; omega))]
            have ho : outerP (("(" :: bare ops names c ++ [")"]) ++ "^" :: full ops names b) = false := by
              have e := outerP_group_more Fc.balBare (y := "^" :: full ops names b) (by simp)
              simpa using e
            have := mpt_infix (metaParseTokens g) (A := "(" :: bare ops names c ++ [")"])
              (B := full ops names b) (n := "^") (by decide) (by simp) ho [] (by simp) hinner
              (fun _ => by simp) hA (IHb.2 g (by simp at hg'; omega))
            rw [mpt_succ]
            exact this
          rw [mpt_succ, mpt_plus_high _ htop (hX f (by simp at hf' ⊢; omega)),
            rotT_plus ops hnn.symm hp]
          simp [surf, hnn.symm, hp]
        · have L := lhs_facts (n := n) Fa
          have hb : bare ops names (.branch idx [a, b]) =
              lhs ops names n a ++ n :: full ops names b := by
            simp [bare, hnn.symm, hinf, full, lhs]
          rw [hb] at hf ⊢
          obtain ⟨f, rfl, hf'⟩ := mpt_fuel (ts := lhs ops names n a ++ n :: full ops names b)
            (by simp) hf
          have IHl : ∀ g, (lhs ops names n a).length ≤ g →
              metaParseTokens g (lhs ops names n a) = .ok (surf ops names (rotT ops a)) := by
            intro g hg
            unfold lhs at hg ⊢
            split
            · rename_i hw
              simp only [hw, ↓reduceIte] at hg
              obtain ⟨g', rfl, _⟩ := mpt_fuel (ts := "(" :: bare ops names a ++ [")"]) (by simp) hg
              rw [mpt_succ, List.cons_append, mpt_outer _ Fa.balBare (IHa1 g' (by simp at hg; omega))]
            · rename_i hw
              simp only [hw, Bool.false_eq_true, ↓reduceIte] at hg
              exact IHa1 g hg
          have hopn : opTok n = true := by
            rcases infixName_cases hinf with
              h | h | h | h | h <;> rw [h] <;> decide
          have ht : ftAux (lhs ops names n a ++ n :: full ops names b) none 0 0 =
              [((lhs ops names n a).length, n)] := by
            rw [ftAux_top L.1, L.2.2.1, List.nil_append]
            have hlo := lastOr_ne L.2.1 L.2.2.2.1
            have hpos : 0 < (lhs ops names n a).length := len_pos L.2.1
            simp only [ftAux, ne_beq hok.1, ne_beq hok.2.1, Bool.false_eq_true, ↓reduceIte,
              beq_self_eq_true, Nat.zero_add, hlo]
            simp only [hpos, decide_true, Bool.not_false, Bool.and_self, ↓reduceIte,
              Fb.ft (some n) _ (Or.inr (by simpa using hopn))]
          have ho : outerP (lhs ops names n a ++ n :: full ops names b) = false :=
            L.2.2.2.2.2.1 _ (by simp)
          have hsign : n = "^" → (lhs ops names n a).head? ≠ some "-" ∧
              (lhs ops names n a).head? ≠ some "+" := by
            intro h
            cases hw : lhsWrap ops n a
            · obtain ⟨hl, _⟩ := L.2.2.2.2.2.2 hw
              rw [hl]
              have hm : MinusLed ops a = false := by
                unfold lhsWrap at hw
                rw [h] at hw
                simp only [beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff] at hw
                exact hw.2
              have hp : PlusLed ops a = false := by
                cases hq : PlusLed ops a
                · rfl
                · exact absurd ⟨h, hq⟩ hrot
              constructor
              · intro hh; have := Fa.headMinus hh; rw [hm] at this; cases this
              · intro hh; have := Fa.headPlus hh; rw [hp] at this; cases this
            · simp [lhs, hw]
          have := mpt_infix (metaParseTokens f) hinf L.2.1 ho [] (by simp) (by simpa using ht) hsign
            (IHl f (by simp at hf'; omega)) (IHb.2 f (by simp at hf'; omega))
          rw [mpt_succ, this, rotT_pair ops (by rw [← hnn]; exact hrot)]
          simp [surf, hnn]
      · have hinf' : infixName n = false := by simpa using hinf
        obtain ⟨_, hpl⟩ := hok.2.2.2 hinf'
        have hb : bare ops names (.branch idx [a, b]) =
            n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"] := by
          simp [bare, hnn.symm, hinf']
        rw [hb] at hf ⊢
        obtain ⟨f, rfl, hf'⟩ := mpt_fuel
          (ts := n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"]) (by simp) hf
        have hx : Bal (bare ops names a ++ "," :: bare ops names b) :=
          Fa.balBare.append (.tok (by decide) (by decide) Fb.balBare)
        have hargs : (splitC (bare ops names a ++ "," :: bare ops names b)).mapM (metaParseTokens f) =
            .ok [surf ops names (rotT ops a), surf ops names (rotT ops b)] := by
          rw [splitC_pair Fa.balBare Fa.bareNe (Fa.commaBare 0) (Fb.commaBare _)]
          simp at hf'
          simp [IHa.1 f (by omega), IHb.1 f (by omega)] <;> rfl
        have hrot : ¬ (opName ops 2 idx = "^" ∧ PlusLed ops a = true) := by
          rintro ⟨h, -⟩
          rw [← hnn] at h
          rw [h] at hinf'
          exact absurd hinf' (by decide)
        rw [mpt_succ]
        simp only [List.cons_append]
        rw [mpt_prefix _ hok.1 hok.2.1 hx _ hargs, rotT_pair ops hrot]
        have h1 : (n == "-") = false := by simp [hpl.2.2.1]
        have h2 : (n == "+") = false := by simp [hpl.2.2.2.1]
        simp [prefixResult, h1, h2, surf, hnn]
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

theorem parse_bare {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) :
    ∀ fuel, (bare ops names t).length ≤ fuel →
      metaParseTokens fuel (bare ops names t) = .ok (surf ops names (rotT ops t)) :=
  (parse_bare_aux hops hn t hw ha).1

theorem parse_toks {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) :
    (∀ fuel, (bare ops names t).length ≤ fuel →
      metaParseTokens fuel (bare ops names t) = .ok (surf ops names (rotT ops t))) ∧
    (∀ fuel, (full ops names t).length ≤ fuel →
      metaParseTokens fuel (full ops names t) = .ok (surf ops names (rotT ops t))) :=
  ⟨parse_bare hops hn t hw ha,
    full_of_bare (tokFacts hops hn t hw ha).balBare (parse_bare hops hn t hw ha)⟩

end DynExpr.StringsParse.Roundtrip
