import DynExpr.StringsParse.Roundtrip.Lex
import DynExpr.StringsParse.Roundtrip.ParseToks
import DynExpr.StringsParse.GeneralStrings

/-! Rendering of admissible trees (`src/Strings.jl:71-197`) and the lexing of
the rendered characters. -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

theorem toList_lp : "(".toList = ['('] := by decide
theorem toList_rp : ")".toList = [')'] := by decide
theorem toList_sp : " ".toList = [' '] := by decide
theorem toList_csp : ", ".toList = [',', ' '] := by decide
theorem toList_plus_sp : " + ".toList = [' ', '+', ' '] := by decide
theorem toList_minus_sp : " - ".toList = [' ', '-', ' '] := by decide
theorem toList_im : "im".toList = ['i', 'm'] := by decide

theorem ascii_of_plain {s : String} (h : plainName s = true) : asciiIdent s = true := by
  simp only [plainName, Bool.and_eq_true] at h
  exact h.1

theorem isEmpty_false {s : String} (h : s.toList ≠ []) : s.isEmpty = false := by
  cases hs : s.isEmpty
  · rfl
  · exfalso; apply h
    have : s = "" := String.isEmpty_iff.mp hs
    subst this; rfl

theorem strip_plain {s : String} (hne : s.toList ≠ []) (hh : s.toList.head? ≠ some '(') :
    stripBrackets s = .ok s := by
  unfold stripBrackets
  have hb : (s.toList.head? == some '(') = false := by simpa using hh
  simp [isEmpty_false hne, hb]

theorem strip_wrapped {s : String} {m : List Char} (h : s.toList = '(' :: m ++ [')']) :
    stripBrackets s = .ok (String.ofList m) := by
  unfold stripBrackets
  have hne : s.toList ≠ [] := by rw [h]; simp
  have hlen : s.length = m.length + 2 := by
    rw [← String.length_toList, h]; simp
  have hl : ('(' :: (m ++ [')'])).getLast? = some ')' := by rw [← List.cons_append, getLast?_snoc]
  simp [isEmpty_false hne, h, hlen, hl]

/-- Rendering facts for one admissible tree. -/
structure RenderFacts (ops : Operators) (names : List String) (t : Tree Scalar) : Prop where
  ok : ∃ s s' : String, rawTree (rcfg ops names) t = .ok s ∧ stripBrackets s = .ok s' ∧
    s.toList = (if wrapped ops t then '(' :: s'.toList ++ [')'] else s'.toList) ∧
    s'.toList ≠ [] ∧ (wrapped ops t = false → s'.toList.head? ≠ some '(') ∧
    (s.toList.head? = some '-' ↔ MinusLed ops t = true) ∧
    ∀ r ts, Bd r → LexOK r ts → LexOK (s'.toList ++ r) (bare ops names t ++ ts)

theorem lex_full {ops : Operators} {names : List String} {t : Tree Scalar} {s s' : String}
    (hs : s.toList = (if wrapped ops t then '(' :: s'.toList ++ [')'] else s'.toList))
    (hl : ∀ r ts, Bd r → LexOK r ts → LexOK (s'.toList ++ r) (bare ops names t ++ ts))
    {r : List Char} {ts : List String} (hr : Bd r) (h : LexOK r ts) :
    LexOK (s.toList ++ r) (full ops names t ++ ts) := by
  unfold full
  rw [hs]
  split
  · have := lexOK_lp (hl (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp)
      (lexOK_rp h))
    simpa using this
  · exact hl r ts hr h

theorem bd_num {r : List Char} (h : Bd r) :
    ∀ x ∈ r.head?, x.isDigit = false ∧ x ≠ '.' ∧ x ≠ 'e' ∧ x ≠ 'E' ∧ x ≠ 'f' := by
  intro x hx
  rcases h x hx with rfl | rfl | rfl <;> decide

theorem lexOK_dec {q : Rat} (hq : 0 ≤ q) {r : List Char} {ts : List String}
    (hb : ∀ x ∈ r.head?, x.isDigit = false ∧ x ≠ '.' ∧ x ≠ 'e' ∧ x ≠ 'E' ∧ x ≠ 'f')
    (h : LexOK r ts) : LexOK ((dec q).toList ++ r) (dec q :: ts) := by
  intro fuel hf
  have hne := (dec_facts hq).2.1
  have hpos : 0 < (finiteText q false).toList.length := len_pos (by simpa [dec] using hne)
  cases fuel with
  | zero => simp at hf
  | succ f =>
    unfold dec
    rw [lex_finiteText_ctx hq f r hb, h f (by simp [dec] at hf; omega)]

theorem lexOK_real {q : Rat} (htq : Terminating q) {r : List Char} {ts : List String}
    (hb : ∀ x ∈ r.head?, x.isDigit = false ∧ x ≠ '.' ∧ x ≠ 'e' ∧ x ≠ 'E' ∧ x ≠ 'f')
    (h : LexOK r ts) : LexOK ((finiteText q false).toList ++ r) (realToks q ++ ts) := by
  unfold realToks
  by_cases hq : q.num < 0
  · simp only [hq, ↓reduceIte]
    rw [finiteText_neg htq (lt_of_num hq)]
    have := lexOK_minus (lexOK_dec (neg_nonneg_of hq) hb h)
    simpa [String.toList_append, dec] using this
  · simp only [hq, ↓reduceIte]
    exact lexOK_dec (num_nonneg hq) hb h

theorem finiteText_head {q : Rat} (htq : Terminating q) :
    (finiteText q false).toList.head? ≠ some '(' ∧ (finiteText q false).toList ≠ [] ∧
    ((finiteText q false).toList.head? = some '-' ↔ q.num < 0) := by
  by_cases hq : q.num < 0
  · rw [finiteText_neg htq (lt_of_num hq)]; simp [String.toList_append, hq]
  · obtain ⟨c, cs, hl, hd⟩ := finiteText_nonneg_head (num_nonneg hq)
    rw [hl]
    refine ⟨?_, by simp, ?_⟩
    · intro h; simp at h; subst h; exact absurd hd (by decide)
    · simp only [List.head?_cons, Option.some.injEq, hq, iff_false]
      intro h; subst h; exact absurd hd (by decide)

theorem intercalate_one (a : String) : String.intercalate ", " [a] = a := rfl

theorem intercalate_two (a b : String) : String.intercalate ", " [a, b] = a ++ ", " ++ b := rfl

theorem combine_prefix1 (n s s' : String) (hn : n.toList ≠ []) (hs : stripBrackets s = .ok s') :
    combineOpWithInputs n [s] = .ok (n ++ "(" ++ s' ++ ")") := by
  unfold combineOpWithInputs
  simp [hs, intercalate_one]
  rfl

/-- The infix layout with master's signed-base bracket (`src/Strings.jl:107-119`). -/
theorem combine_infix (n a b : String) (hn : infixName n = true) (ha : a.toList ≠ []) :
    combineOpWithInputs n [a, b] = .ok ("(" ++
      (if n = "^" ∧ a.toList.head? = some '-' then "(" ++ a ++ ")" else a) ++
      " " ++ n ++ " " ++ b ++ ")") := by
  obtain ⟨c, hl, _⟩ := infix_toList hn
  have hhead : n.toList.head? = some c := by rw [hl]; rfl
  have hc : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c) = true := by
    rcases infixName_cases hn with
      rfl | rfl | rfl | rfl | rfl <;> (simp at hl; subst hl; decide)
  obtain ⟨a0, as, hal⟩ : ∃ a0 as, a.toList = a0 :: as := by
    cases h : a.toList with
    | nil => exact absurd h ha
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hlast : (n.toList.getLast? == some '^') = decide (n = "^") := by
    rcases infixName_cases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  unfold combineOpWithInputs
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, beq_self_eq_true, ↓reduceIte,
    hhead, hc, Bool.true_or, bind, Except.bind, pure, Except.pure, List.getElem?_cons_zero,
    Option.getD_some, List.getElem?_cons_succ, hlast, hal, List.head?_cons]
  by_cases hn' : n = "^" <;> by_cases ha0 : a0 = '-' <;> simp [hn', ha0]

theorem combine_prefix2 (n a b a' b' : String) (hp : plainName n = true)
    (ha : stripBrackets a = .ok a') (hb : stripBrackets b = .ok b') :
    combineOpWithInputs n [a, b] = .ok (n ++ "(" ++ a' ++ ", " ++ b' ++ ")") := by
  obtain ⟨_, c, cs, hl, hal, hd⟩ := ident_facts hp
  have hc : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || n == "!=") = false := by
    have hne : n ≠ "!=" := by
      intro h; rw [h] at hl; simp at hl
      obtain ⟨rfl, _⟩ := hl; exact absurd hal (by decide)
    have hcc : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c) = false := by
      cases hcx : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c)
      · rfl
      · exfalso
        rcases (by simpa using hcx : c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '/' ∨ c = '^' ∨ c = '.' ∨
          c = '>' ∨ c = '<' ∨ c = '=') with h | h | h | h | h | h | h | h | h <;>
          (subst h; exact absurd hal (by decide))
    rw [hcc, Bool.false_or]
    simpa using hne
  unfold combineOpWithInputs
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, beq_self_eq_true, ↓reduceIte, hl,
    List.head?_cons]
  rw [hc]
  simp [ha, hb, intercalate_two, String.append_assoc]
  rfl

theorem dispatch_clean {ops : Operators} (hops : CleanOps ops) {d idx : Nat} (hd : 0 < d)
    (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    dispatchOpName (some ops) d idx false = .ok (opName ops d idx) := by
  have hget : (ops[d - 1]?.getD [])[idx - 1]? = some ((table ops d)[idx - 1]'(by omega)) :=
    List.getElem?_eq_getElem (l := table ops d) (by omega)
  rw [General.dispatchNames ops _ d idx false hd (by omega) hget]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [opName_eq hi hl]
  exact congrArg Except.ok ((cleanOps_table hops d).2.2 _ (List.getElem_mem _)).2.1

/-- Every admissible tree renders, strips, and lexes to its token
specification. -/
theorem renderFacts {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) : RenderFacts ops names t := by
  induction t using Tree.induction with
  | hc v =>
    match v, ha with
    | .real (.fin q), ha =>
      simp only [Admissible, CleanConst] at ha
      obtain ⟨hh, hne, hm⟩ := finiteText_head ha
      refine ⟨⟨finiteText q false, finiteText q false, rfl, strip_plain hne hh, by simp [wrapped],
        hne, fun _ => hh, by simpa [MinusLed] using hm, ?_⟩⟩
      intro r ts hr h
      simpa [bare] using lexOK_real ha (bd_num hr) h
    | .complex (.fin r) (.fin i), ha =>
      simp only [Admissible, CleanConst] at ha
      obtain ⟨_, htr, hti⟩ := ha
      have hmag : 0 ≤ imagMag i := by
        unfold imagMag; split
        · exact neg_nonneg_of ‹_›
        · exact num_nonneg ‹_›
      have hmagT : realToks (imagMag i) = [dec (imagMag i)] := by
        have : ¬ (imagMag i).num < 0 := by have := Rat.num_nonneg.mpr hmag; omega
        simp [realToks, this]
      -- The imaginary part and its sign, as `scalarText` renders them.
      have hsc : scalarText (.complex (.fin r) (.fin i)) =
          finiteText r false ++ (if i.num < 0 then " - " else " + ") ++
            finiteText (imagMag i) false ++ "im" := by
        unfold scalarText imagMag
        by_cases h : i.num < 0
        · simp [h, realText]; rfl
        · simp [h, realText]
      obtain ⟨s', hs'⟩ : ∃ s', s' = scalarText (.complex (.fin r) (.fin i)) := ⟨_, rfl⟩
      have hs'l : s'.toList = (finiteText r false).toList ++ ' ' :: (imagSign i).toList ++
          ' ' :: (finiteText (imagMag i) false).toList ++ ['i', 'm'] := by
        rw [hs', hsc]
        unfold imagSign
        by_cases h : i.num < 0
        · simp [h, String.toList_append, toList_minus_sp, toList_im]
        · simp [h, String.toList_append, toList_plus_sp, toList_im]
      have hsgn : infixName (imagSign i) = true := by unfold imagSign; split <;> decide
      have hne : s'.toList ≠ [] := by rw [hs'l]; simp [(finiteText_head htr).2.1]
      refine ⟨⟨"(" ++ s' ++ ")", s', by rw [hs']; rfl, ?_, ?_, hne, fun h => by simp [wrapped] at h,
        by simp [MinusLed, String.toList_append, toList_lp], ?_⟩⟩
      · have hwrap : ("(" ++ s' ++ ")").toList = '(' :: s'.toList ++ [')'] := by
          simp [String.toList_append, toList_lp, toList_rp]
        rw [strip_wrapped hwrap, String.ofList_toList]
      · simp [wrapped, String.toList_append, toList_lp, toList_rp]
      · intro r' ts hr h
        rw [hs'l]
        have him : LexOK (['i', 'm'] ++ r') ("im" :: ts) := by
          have := lexOK_ident (s := "im") (by decide) (bd_ident hr) h
          simpa [toList_im] using this
        have hD := lexOK_dec hmag (r := ['i', 'm'] ++ r') (by intro x hx; simp at hx; subst hx; decide) him
        have hsg := lexOK_infix hsgn (lexOK_ws hD)
        have hR := lexOK_real htr (q := r) (r := ' ' :: ((imagSign i).toList ++
          ' ' :: ((dec (imagMag i)).toList ++ (['i', 'm'] ++ r'))))
          (by intro x hx; simp at hx; subst hx; decide) (lexOK_ws hsg)
        simpa [bare, dec, List.append_assoc] using hR
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
    have hpn := hn.2.2 _ (List.getElem_mem hk)
    obtain ⟨_, c, cs, hl, hal, _⟩ := ident_facts hpn
    have hhead : names[k - 1].toList.head? ≠ some '(' := by
      rw [hl]; intro h; simp at h; subst h; exact absurd hal (by decide)
    have hne : names[k - 1].toList ≠ [] := by rw [hl]; simp
    have hraw : rawTree (rcfg ops names) (.feature k) = .ok names[k - 1] := by
      have hz : k ≠ 0 := by omega
      simp [rawTree, rcfg, stringVariable, hz, List.getElem?_eq_getElem hk]
    refine ⟨⟨names[k - 1], names[k - 1], hraw, strip_plain hne hhead, by simp [wrapped], hne,
      fun _ => hhead, ?_, ?_⟩⟩
    · rw [hl]; simp only [MinusLed, List.head?_cons, Option.some.injEq, Bool.false_eq_true, iff_false]
      intro h; subst h; exact absurd hal (by decide)
    intro r ts hr h
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    simpa [bare, hname] using lexOK_ident (ascii_of_plain hpn) (bd_ident hr) h
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have ha' := ha
    simp only [Admissible] at ha'
    match cs, hl1, hl2, hi2, ih, hcs, ha' with
    | [c], _, _, hi2, ih, hcs, ha' =>
      simp only [List.length_singleton] at hi2
      obtain ⟨⟨sc, sc', hrc, hsc, hscl, hne', _, _, hlc⟩⟩ := ih c (by simp) (hcs c (by simp)) (ha' c (by simp))
      have hok := opName_ok hops hi1 (table_len (by decide) hi2)
      have hokf := opNameOK_facts hok
      generalize hnn' : opName ops 1 idx = n at hok hokf
      have hnn : n = opName ops 1 idx := hnn'.symm
      have hdisp : dispatchOpName (some ops) 1 idx false = .ok n := by
        rw [hnn]; exact dispatch_clean hops (by decide) hi1 (table_len (by decide) hi2)
      -- Head of the operator name.
      have hnl : ∃ c0 cs0, n.toList = c0 :: cs0 ∧ c0 ≠ '(' := by
        by_cases hi : infixName n = true
        · obtain ⟨c0, hl0, _, _, _, _, _, _, hp⟩ := infix_toList hi
          exact ⟨c0, [], hl0, hp⟩
        · obtain ⟨hp, _⟩ := hokf.2.2.2 (by simpa using hi)
          obtain ⟨_, c0, cs0, hl0, hal, _⟩ := ident_facts hp
          exact ⟨c0, cs0, hl0, by intro h; subst h; exact absurd hal (by decide)⟩
      obtain ⟨c0, cs0, hnl0, hc0⟩ := hnl
      have hraw : rawTree (rcfg ops names) (.branch idx [c]) = .ok (n ++ "(" ++ sc' ++ ")") := by
        simp only [rawTree, rawForest, hrc, bind, Except.bind, pure, Except.pure]
        simp only [rcfg, resolvePretty, Option.getD_none, Option.map_none, List.length_cons,
          List.length_nil, Nat.zero_add] at hdisp ⊢
        rw [hdisp]
        exact combine_prefix1 n sc sc' (by rw [hnl0]; simp) hsc
      have htl : (n ++ "(" ++ sc' ++ ")").toList = n.toList ++ '(' :: sc'.toList ++ [')'] := by
        simp [String.toList_append, toList_lp, toList_rp]
      have hne : (n ++ "(" ++ sc' ++ ")").toList ≠ [] := by rw [htl]; simp
      have hhead : (n ++ "(" ++ sc' ++ ")").toList.head? ≠ some '(' := by
        rw [htl, hnl0]; simpa using hc0
      have hminus : (n ++ "(" ++ sc' ++ ")").toList.head? = some '-' ↔
          MinusLed ops (.branch idx [c]) = true := by
        rw [htl, hnl0]
        simp only [MinusLed, ← hnn, List.cons_append, List.head?_cons, Option.some.injEq,
          beq_iff_eq]
        by_cases hi : infixName n = true
        · rcases infixName_cases hi with rfl | rfl | rfl | rfl | rfl
          · rw [show ("+" : String).toList = ['+'] by decide] at hnl0
            simp only [List.cons.injEq] at hnl0; obtain ⟨rfl, rfl⟩ := hnl0; decide
          · rw [show ("-" : String).toList = ['-'] by decide] at hnl0
            simp only [List.cons.injEq] at hnl0; obtain ⟨rfl, rfl⟩ := hnl0; decide
          · rw [show ("*" : String).toList = ['*'] by decide] at hnl0
            simp only [List.cons.injEq] at hnl0; obtain ⟨rfl, rfl⟩ := hnl0; decide
          · rw [show ("/" : String).toList = ['/'] by decide] at hnl0
            simp only [List.cons.injEq] at hnl0; obtain ⟨rfl, rfl⟩ := hnl0; decide
          · rw [show ("^" : String).toList = ['^'] by decide] at hnl0
            simp only [List.cons.injEq] at hnl0; obtain ⟨rfl, rfl⟩ := hnl0; decide
        · obtain ⟨hp, hpt⟩ := hokf.2.2.2 (by simpa using hi)
          obtain ⟨_, c1, cs1, hl1, hal1, _⟩ := ident_facts hp
          rw [hnl0] at hl1
          simp only [List.cons.injEq] at hl1
          obtain ⟨rfl, _⟩ := hl1
          constructor
          · intro h; subst h; exact absurd hal1 (by decide)
          · intro h; exact absurd h hpt.2.2.1
      refine ⟨⟨_, _, hraw, strip_plain hne hhead, by simp [wrapped], hne, fun _ => hhead,
        hminus, ?_⟩⟩
      intro r ts hr h
      rw [htl]
      have hin : LexOK (sc'.toList ++ ')' :: r) (bare ops names c ++ ")" :: ts) :=
        hlc (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp) (lexOK_rp h)
      have hlp := lexOK_lp hin
      have hnamelex : LexOK (n.toList ++ '(' :: (sc'.toList ++ ')' :: r))
          (n :: "(" :: (bare ops names c ++ ")" :: ts)) := by
        by_cases hi : infixName n = true
        · exact lexOK_infix hi hlp
        · obtain ⟨hp, _⟩ := hokf.2.2.2 (by simpa using hi)
          exact lexOK_ident (ascii_of_plain hp) (identChar_lp _) hlp
      simpa [bare, hnn, List.append_assoc] using hnamelex
    | [a, b], _, _, hi2, ih, hcs, ha' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      obtain ⟨⟨sa, sa', hra, hsa, hsal, hnea, hpa, hma, hla⟩⟩ :=
        ih a (by simp) (hcs a (by simp)) (ha' a (by simp))
      obtain ⟨⟨sb, sb', hrb, hsb, hsbl, hneb, _, _, hlb⟩⟩ :=
        ih b (by simp) (hcs b (by simp)) (ha' b (by simp))
      have hok := opName_ok hops hi1 (table_len (by decide) hi2)
      have hokf := opNameOK_facts hok
      generalize hnn' : opName ops 2 idx = n at hok hokf
      have hnn : n = opName ops 2 idx := hnn'.symm
      have hdisp : dispatchOpName (some ops) 2 idx false = .ok n := by
        rw [hnn]; exact dispatch_clean hops (by decide) hi1 (table_len (by decide) hi2)
      have hcomb : ∀ text, combineOpWithInputs n [sa, sb] = .ok text →
          rawTree (rcfg ops names) (.branch idx [a, b]) = .ok text := by
        intro text hc
        simp only [rawTree, rawForest, hra, hrb, bind, Except.bind, pure, Except.pure]
        simp only [rcfg, resolvePretty, Option.getD_none, Option.map_none, List.length_cons,
          List.length_nil, Nat.zero_add, Nat.reduceAdd] at hdisp ⊢
        rw [hdisp]
        exact hc
      by_cases hinf : infixName n = true
      · have hsane : sa.toList ≠ [] := by
          rw [hsal]; split
          · simp
          · exact hnea
        obtain ⟨sl, hsl⟩ : ∃ sl, sl =
            (if n = "^" ∧ sa.toList.head? = some '-' then "(" ++ sa ++ ")" else sa) := ⟨_, rfl⟩
        obtain ⟨s', hs'⟩ : ∃ s', s' = sl ++ " " ++ n ++ " " ++ sb := ⟨_, rfl⟩
        have hraw := hcomb _ (combine_infix n sa sb hinf hsane)
        rw [← hsl] at hraw
        have htl : s'.toList = sl.toList ++ ' ' :: n.toList ++ ' ' :: sb.toList := by
          simp [hs', String.toList_append, toList_sp]
        have hwrap : ("(" ++ sl ++ " " ++ n ++ " " ++ sb ++ ")").toList = '(' :: s'.toList ++ [')'] := by
          simp [hs', String.toList_append, toList_sp, toList_lp, toList_rp]
        -- The left operand lexes to the `lhs` token specification.
        have hlhs : ∀ r ts, Bd r → LexOK r ts →
            LexOK (sl.toList ++ r) (lhs ops names n a ++ ts) := by
          intro r ts hr h
          cases hwa : wrapped ops a
          · have hsa' : sa.toList = sa'.toList := by simpa [hwa] using hsal
            have hfa : full ops names a = bare ops names a := by simp [full, hwa]
            by_cases hsg : n = "^" ∧ MinusLed ops a = true
            · have hif : n = "^" ∧ sa.toList.head? = some '-' := ⟨hsg.1, hma.mpr hsg.2⟩
              have hsl' : sl = "(" ++ sa ++ ")" := by rw [hsl, if_pos hif]
              have hlw : lhsWrap ops n a = true := by simp [lhsWrap, hsg.1, hsg.2]
              rw [hsl', show lhs ops names n a = "(" :: bare ops names a ++ [")"] by simp [lhs, hlw]]
              have hin := hla (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp)
                (lexOK_rp h)
              have := lexOK_lp hin
              simpa [String.toList_append, toList_lp, toList_rp, hsa', List.append_assoc] using this
            · have hnif : ¬ (n = "^" ∧ sa.toList.head? = some '-') :=
                fun hif => hsg ⟨hif.1, hma.mp hif.2⟩
              have hsl' : sl = sa := by rw [hsl, if_neg hnif]
              have hlw : lhsWrap ops n a = false := by
                cases hm : MinusLed ops a
                · simp [lhsWrap, hwa, hm]
                · by_cases hn' : n = "^"
                  · exact absurd ⟨hn', hm⟩ hsg
                  · simp [lhsWrap, hwa, hn']
              rw [hsl', show lhs ops names n a = full ops names a by simp [lhs, hlw, hfa]]
              exact lex_full hsal hla hr h
          · have hhead : sa.toList.head? = some '(' := by simp [hsal, hwa]
            have hnif : ¬ (n = "^" ∧ sa.toList.head? = some '-') := by
              rw [hhead]; intro h; simp at h
            have hsl' : sl = sa := by rw [hsl, if_neg hnif]
            have hlw : lhsWrap ops n a = true := by simp [lhsWrap, hwa]
            rw [hsl', show lhs ops names n a = full ops names a by simp [lhs, hlw, full, hwa]]
            exact lex_full hsal hla hr h
        have hne : s'.toList ≠ [] := by
          rw [htl, hsl]
          split
          · simp [String.toList_append, toList_lp]
          · intro h
            exact hsane (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
        refine ⟨⟨_, s', hraw, ?_, ?_, hne, fun h => by simp [wrapped, hnn.symm, hinf] at h,
          by simp [MinusLed, String.toList_append, toList_lp], ?_⟩⟩
        · rw [strip_wrapped hwrap, String.ofList_toList]
        · simp only [wrapped, ← hnn, hinf, ↓reduceIte]; exact hwrap
        · intro r ts hr h
          rw [htl]
          have hB := lex_full hsbl hlb hr h
          have hN := lexOK_infix hinf (lexOK_ws hB)
          have hA := hlhs (' ' :: (n.toList ++ ' ' :: (sb.toList ++ r))) _
            (by intro x hx; simp at hx; subst hx; simp) (lexOK_ws hN)
          have hbare : bare ops names (.branch idx [a, b]) =
              lhs ops names n a ++ n :: full ops names b := by
            simp [bare, hnn.symm, hinf, full, lhs]
          rw [hbare]
          simpa [List.append_assoc] using hA
      · have hinf' : infixName n = false := by simpa using hinf
        obtain ⟨hp, _⟩ := hokf.2.2.2 hinf'
        obtain ⟨_, c0, cs0, hnl0, hal, _⟩ := ident_facts hp
        obtain ⟨s, hs⟩ : ∃ s, s = n ++ "(" ++ sa' ++ ", " ++ sb' ++ ")" := ⟨_, rfl⟩
        have hraw := hcomb _ (combine_prefix2 n sa sb sa' sb' hp hsa hsb)
        rw [← hs] at hraw
        have htl : s.toList = n.toList ++ '(' :: sa'.toList ++ ',' :: ' ' :: sb'.toList ++ [')'] := by
          simp [hs, String.toList_append, toList_lp, toList_rp, toList_csp]
        have hne : s.toList ≠ [] := by rw [htl, hnl0]; simp
        have hhead : s.toList.head? ≠ some '(' := by
          rw [htl, hnl0]; intro h; simp at h; subst h; exact absurd hal (by decide)
        refine ⟨⟨s, s, hraw, strip_plain hne hhead, by simp [wrapped, hnn.symm, hinf'], hne,
          fun _ => hhead, ?_, ?_⟩⟩
        · rw [htl, hnl0]
          simp only [MinusLed, List.cons_append, List.head?_cons, Option.some.injEq,
            Bool.false_eq_true, iff_false]
          intro h; subst h; exact absurd hal (by decide)
        intro r ts hr h
        rw [htl]
        have hB := hlb (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp) (lexOK_rp h)
        have hC := lexOK_comma (lexOK_ws hB)
        have hA := hla (',' :: ' ' :: (sb'.toList ++ ')' :: r)) ("," :: (bare ops names b ++ ")" :: ts))
          (by intro x hx; simp at hx; subst hx; simp) hC
        have hN := lexOK_ident (ascii_of_plain hp) (identChar_lp _) (lexOK_lp hA)
        have hbare : bare ops names (.branch idx [a, b]) =
            n :: "(" :: (bare ops names a ++ "," :: bare ops names b) ++ [")"] := by
          simp [bare, hnn.symm, hinf']
        rw [hbare]
        simpa [List.append_assoc] using hN
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

end DynExpr.StringsParse.Roundtrip
