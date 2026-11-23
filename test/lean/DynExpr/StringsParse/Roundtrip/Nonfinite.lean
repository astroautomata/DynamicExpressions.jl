import DynExpr.StringsParse.Roundtrip.Float32

/-! Printing and reparsing of every scalar constant, including NaN and the
infinities. `string` prints `NaN`, `Inf`, and `-Inf` (Float32 values print
without their suffix), and complex values with a nonfinite imaginary part as
`a + Inf*im` (`src/Strings.jl:87-93`). `Meta.parse` reads these as symbols and
unary/binary calls (`src/Parse.jl:297`), which
`_normalize_expression_for_parse` folds back into constants
(`src/Parse.jl:219-249`). -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-- Finite components are exact terminating decimals (Q21). -/
def FinOK : JF → Prop
  | .fin q => Terminating q
  | _ => True

def ConstOK : Scalar → Prop
  | .real v => FinOK v
  | .float32 v => FinOK v
  | .complex r i => FinOK r ∧ FinOK i

/-- Tokens of `realText v`. -/
def toksR : JF → List String
  | .fin q => realToks q
  | .nan => ["NaN"]
  | .posInf => ["Inf"]
  | .negInf => ["-", "Inf"]

/-- Sign token between the two parts of a complex constant. -/
def signJ : JF → String
  | .fin q => imagSign q
  | .negInf => "-"
  | _ => "+"

/-- Text of the imaginary part after its sign. -/
def imagText : JF → String
  | .fin q => dec (imagMag q) ++ "im"
  | .nan => "NaN*im"
  | _ => "Inf*im"

/-- Tokens of the imaginary part after its sign. -/
def toksI : JF → List String
  | .fin q => [dec (imagMag q), "im"]
  | .nan => ["NaN", "*", "im"]
  | _ => ["Inf", "*", "im"]

/-- Magnitude printed after the sign. -/
def imagVal : JF → JF
  | .fin q => .fin (imagMag q)
  | .nan => .nan
  | _ => .posInf

def toksC : Scalar → List String
  | .real v => toksR v
  | .float32 v => toksR v
  | .complex r i => toksR r ++ signJ i :: toksI i

def surfR : JF → Surface
  | .fin q => .literal (.real (.fin q))
  | .nan => .symbol "NaN"
  | .posInf => .symbol "Inf"
  | .negInf => .call "-" [.symbol "Inf"]

def surfI : JF → Surface
  | .fin q => .call "*" [.literal (.real (.fin (imagMag q))), .symbol "im"]
  | .nan => .call "*" [.symbol "NaN", .symbol "im"]
  | _ => .call "*" [.symbol "Inf", .symbol "im"]

def surfC : Scalar → Surface
  | .real v => surfR v
  | .float32 v => surfR v
  | .complex r i => .call (signJ i) [surfR r, surfI i]

/-! ## Rendering -/

theorem realText_facts (w : JF) (hw : FinOK w) :
    (realText w).toList ≠ [] ∧ (realText w).toList.head? ≠ some '(' := by
  cases w with
  | fin q => exact ⟨(finiteText_head hw).2.1, (finiteText_head hw).1⟩
  | nan => exact ⟨by decide, by decide⟩
  | posInf => exact ⟨by decide, by decide⟩
  | negInf => exact ⟨by decide, by decide⟩

theorem scalarText_complex (r i : JF) :
    (scalarText (.complex r i)).toList =
      (realText r).toList ++ ' ' :: (signJ i).toList ++ ' ' :: (imagText i).toList := by
  cases i with
  | fin q =>
    unfold scalarText signJ imagText imagSign imagMag
    by_cases h : q.num < 0
    · simp [h, realText, String.toList_append, toList_minus_sp, dec]; rfl
    · simp [h, realText, String.toList_append, toList_plus_sp, dec]
  | nan => simp [scalarText, signJ, imagText, realText, String.toList_append, toList_plus_sp]
  | posInf => simp [scalarText, signJ, imagText, realText, String.toList_append, toList_plus_sp]
  | negInf =>
    simp [scalarText, signJ, imagText, realText, String.toList_append, toList_minus_sp]
    rfl

theorem stringTree_const (ops : Operators) (names : List String) (v : Scalar) (hv : ConstOK v) :
    stringTree {operators := some ops, names := some names} (.const v) = .ok (scalarText v) := by
  cases v with
  | real w =>
    obtain ⟨hne, hh⟩ := realText_facts w hv
    exact strip_plain hne hh
  | float32 w =>
    obtain ⟨hne, hh⟩ := realText_facts w hv
    exact strip_plain hne hh
  | complex r i =>
    have hwrap : ("(" ++ scalarText (.complex r i) ++ ")").toList =
        '(' :: (scalarText (.complex r i)).toList ++ [')'] := by
      simp [String.toList_append, toList_lp, toList_rp]
    show stripBrackets ("(" ++ scalarText (.complex r i) ++ ")") = _
    rw [strip_wrapped hwrap, String.ofList_toList]

/-! ## Lexing -/

theorem lexOK_R (w : JF) (hw : FinOK w) {r : List Char} {ts : List String}
    (hb : ∀ x ∈ r.head?, x = ' ') (h : LexOK r ts) :
    LexOK ((realText w).toList ++ r) (toksR w ++ ts) := by
  have hi : ∀ x ∈ r.head?, identChar x = false := by
    intro x hx; rw [hb x hx]; decide
  cases w with
  | fin q => exact lexOK_real hw (by intro x hx; rw [hb x hx]; decide) h
  | nan => simpa [realText, toksR] using lexOK_ident (s := "NaN") (by decide) hi h
  | posInf => simpa [realText, toksR] using lexOK_ident (s := "Inf") (by decide) hi h
  | negInf =>
    have := lexOK_minus (lexOK_ident (s := "Inf") (by decide) hi h)
    have hl : (realText .negInf).toList = '-' :: "Inf".toList := by decide
    rw [hl]
    simpa [toksR] using this

theorem lexOK_im : LexOK "im".toList ["im"] := by
  simpa using lexOK_ident (s := "im") (r := []) (ts := []) (by decide) (by simp) lexOK_nil

theorem lexOK_I (w : JF) (hw : FinOK w) : LexOK (imagText w).toList (toksI w) := by
  have hstar : LexOK ("*".toList ++ "im".toList) ["*", "im"] :=
    lexOK_infix (n := "*") (by decide) lexOK_im
  cases w with
  | fin q =>
    have hmag : 0 ≤ imagMag q := by
      unfold imagMag; split
      · exact neg_nonneg_of ‹_›
      · exact num_nonneg ‹_›
    have := lexOK_dec hmag (r := "im".toList) (by intro x hx; simp [toList_im] at hx; subst hx; decide)
      lexOK_im
    simpa [imagText, toksI, String.toList_append] using this
  | nan =>
    have := lexOK_ident (s := "NaN") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this
  | posInf =>
    have := lexOK_ident (s := "Inf") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this
  | negInf =>
    have := lexOK_ident (s := "Inf") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this

theorem signJ_cases (i : JF) : signJ i = "+" ∨ signJ i = "-" := by
  cases i with
  | fin q =>
    by_cases h : q.num < 0
    · exact Or.inr (by simp [signJ, imagSign, h])
    · exact Or.inl (by simp [signJ, imagSign, h])
  | nan => exact Or.inl rfl
  | posInf => exact Or.inl rfl
  | negInf => exact Or.inr rfl

theorem signJ_infix (i : JF) : infixName (signJ i) = true := by
  rcases signJ_cases i with h | h <;> rw [h] <;> decide

theorem lexOK_C (v : Scalar) (hv : ConstOK v) : LexOK (scalarText v).toList (toksC v) := by
  cases v with
  | real w => simpa [scalarText, toksC] using lexOK_R w hv (r := []) (ts := []) (by simp) lexOK_nil
  | float32 w => simpa [scalarText, toksC] using lexOK_R w hv (r := []) (ts := []) (by simp) lexOK_nil
  | complex r i =>
    rw [scalarText_complex]
    have hI := lexOK_infix (signJ_infix i) (lexOK_ws (lexOK_I i hv.2))
    have := lexOK_R r hv.1 (r := ' ' :: ((signJ i).toList ++ ' ' :: (imagText i).toList))
      (by simp) (lexOK_ws hI)
    simpa [toksC, List.append_assoc] using this

/-! ## Token parsing -/

theorem parse_ident {s : String} (hs : plainName s = true) (fuel : Nat) (hf : 1 ≤ fuel) :
    metaParseTokens fuel [s] = .ok (.symbol s) := by
  obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := [s]) (by simp) (by simpa using hf)
  rw [mpt_succ, mpt_single _ (ident_facts hs).1, numericToken_ident hs]

theorem mpt_neg_sym (rec : List String → Jl Surface) {tok : String} (h : plainTok tok)
    (hrec : rec [tok] = .ok (.symbol tok)) :
    mptBody rec ["-", tok] = .ok (.call "-" [.symbol tok]) := by
  obtain ⟨h1, h2, _⟩ := h
  have ho : outerP ["-", tok] = false := outerP_head (by simp)
  have ht : ftAux ["-", tok] none 0 0 = [] := by
    simp [ftAux, h1, h2, opTok]
  unfold mptBody
  rw [tops_eq, ht]
  simp [ho, h1, hrec]
  try rfl

/-- A `+`/`-` split whose later top-level positions hold no other `+`/`-`. -/
theorem mpt_low (rec : List String → Jl Surface) {A B : List String} {n : String}
    (hn : n = "+" ∨ n = "-") (ho : outerP (A ++ n :: B) = false)
    (post : List (Nat × String)) (hpost : ∀ p ∈ post, p.2 ≠ "+" ∧ p.2 ≠ "-")
    (ht : ftAux (A ++ n :: B) none 0 0 = (A.length, n) :: post)
    {sa sb : Surface} (ha : rec A = .ok sa) (hb : rec B = .ok sb) :
    mptBody rec (A ++ n :: B) = .ok (.call n [sa, sb]) := by
  have hlow : post.filter (fun p => p.2 == "+" || p.2 == "-") = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    simp [(hpost p hp).1, (hpost p hp).2]
  have hne : (A ++ n :: B).isEmpty = false := by simp
  have htake : (A ++ n :: B).take A.length = A := by simp
  have hdrop : (A ++ n :: B).drop (A.length + 1) = B := by simp
  unfold mptBody
  rw [tops_eq, ht]
  rcases hn with rfl | rfl
  · simp [hne, ho, hlow, htake, hdrop, ha, hb]; try rfl
  · simp [hne, ho, hlow, htake, hdrop, ha, hb]; try rfl

theorem toksR_facts (w : JF) :
    Bal (toksR w) ∧ toksR w ≠ [] ∧ ftAux (toksR w) none 0 0 = [] ∧
    (∀ x ∈ (toksR w).getLast?, opTok x = false) ∧ (toksR w).head? ≠ some "(" := by
  cases w with
  | fin q =>
    obtain ⟨b, ne, ft, last, _, hp, _⟩ := realToks_facts q
    refine ⟨b, ne, ft none 0 (Or.inl rfl), last, ?_⟩
    show (realToks q).head? ≠ some "("
    cases h : realToks q with
    | nil => exact absurd h ne
    | cons x xs => rw [h] at hp; simpa using hp
  | nan => exact ⟨Bal.single (by decide) (by decide), by simp [toksR], by decide, by decide, by decide⟩
  | posInf => exact ⟨Bal.single (by decide) (by decide), by simp [toksR], by decide, by decide, by decide⟩
  | negInf =>
    exact ⟨.tok (by decide) (by decide) (Bal.single (by decide) (by decide)), by simp [toksR], by decide,
      by decide, by decide⟩

theorem parse_R (w : JF) (hw : FinOK w) (fuel : Nat) (hf : (toksR w).length ≤ fuel) :
    metaParseTokens fuel (toksR w) = .ok (surfR w) := by
  cases w with
  | fin q => exact parse_real hw fuel hf
  | nan => exact parse_ident (by decide) fuel hf
  | posInf => exact parse_ident (by decide) fuel hf
  | negInf =>
    simp only [toksR, List.length_cons, List.length_nil] at hf
    obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := ["-", "Inf"]) (by simp) (by simpa using hf)
    show metaParseTokens (f + 1) ["-", "Inf"] = .ok (.call "-" [.symbol "Inf"])
    rw [mpt_succ, mpt_neg_sym _ (ident_facts (by decide : plainName "Inf" = true)).1
      (parse_ident (by decide) f (by omega))]

theorem parse_I (w : JF) (hw : FinOK w) (fuel : Nat) (hf : (toksI w).length ≤ fuel) :
    metaParseTokens fuel (toksI w) = .ok (surfI w) := by
  have hstar : ∀ {x : String}, plainName x = true → ∀ g, 3 ≤ g →
      metaParseTokens g [x, "*", "im"] = .ok (.call "*" [.symbol x, .symbol "im"]) := by
    intro x hx g hg
    obtain ⟨f, rfl, _⟩ := mpt_fuel (ts := [x, "*", "im"]) (by simp) (by simpa using hg)
    have hp := (ident_facts hx).1
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    have ht : ftAux ([x] ++ "*" :: ["im"]) none 0 0 = ([x].length, "*") :: [] := by
      simp [ftAux, opTok, h1, h2, h3, h4, h5, h6, h7, h8]
    have := mpt_infix (metaParseTokens f) (A := [x]) (B := ["im"]) (n := "*") (by decide) (by simp)
      (outerP_head (by simpa using h1)) [] (by simp) ht (fun h => absurd h (by decide))
      (parse_ident hx f (by omega)) (parse_ident (by decide) f (by omega))
    rw [mpt_succ]
    simpa using this
  cases w with
  | fin q =>
    have hmag : 0 ≤ imagMag q := by
      unfold imagMag; split
      · exact neg_nonneg_of ‹_›
      · exact num_nonneg ‹_›
    have htm : Terminating (imagMag q) := by
      unfold imagMag; split
      · exact terminating_neg hw
      · exact hw
    simp only [toksI, List.length_cons, List.length_nil] at hf
    obtain ⟨g, rfl, _⟩ := mpt_fuel (ts := [dec (imagMag q), "im"]) (by simp) (by simpa using hf)
    show metaParseTokens (g + 1) [dec (imagMag q), "im"] =
      .ok (.call "*" [.literal (.real (.fin (imagMag q))), .symbol "im"])
    rw [mpt_succ, mpt_im _ (dec_facts hmag).1 (parse_dec hmag htm g (by omega))]
  | nan => exact hstar (by decide) fuel (by simpa [toksI] using hf)
  | posInf => exact hstar (by decide) fuel (by simpa [toksI] using hf)
  | negInf => exact hstar (by decide) fuel (by simpa [toksI] using hf)

theorem parse_C (v : Scalar) (hv : ConstOK v) (fuel : Nat) (hf : (toksC v).length ≤ fuel) :
    metaParseTokens fuel (toksC v) = .ok (surfC v) := by
  cases v with
  | real w => exact parse_R w hv fuel hf
  | float32 w => exact parse_R w hv fuel hf
  | complex r i =>
    obtain ⟨rb, rne, rft, rlast, rhead⟩ := toksR_facts r
    simp only [toksC] at hf ⊢
    obtain ⟨f, rfl, hf'⟩ := mpt_fuel (ts := toksR r ++ signJ i :: toksI i) (by simp) hf
    have hlo := lastOr_ne rne rlast
    have hpos : 0 < (toksR r).length := len_pos rne
    have hsgn := signJ_cases i
    have hsop : opTok (signJ i) = true := by rcases hsgn with h | h <;> rw [h] <;> decide
    have hs1 : signJ i ≠ "(" := by rcases hsgn with h | h <;> rw [h] <;> decide
    have hs2 : signJ i ≠ ")" := by rcases hsgn with h | h <;> rw [h] <;> decide
    obtain ⟨t, ht, htc⟩ : ∃ t, ftAux (toksI i) (some (signJ i)) ((toksR r).length + 1) 0 =
        [((toksR r).length + 2, t)] ∧ t ≠ "+" ∧ t ≠ "-" := by
      cases i with
      | fin q =>
        have hmag : 0 ≤ imagMag q := by
          unfold imagMag; split
          · exact neg_nonneg_of ‹_›
          · exact num_nonneg ‹_›
        have hD := (dec_facts hmag).1
        refine ⟨"im", ?_, by decide, by decide⟩
        simp only [toksI, ftAux, ne_beq hD.1, ne_beq hD.2.1, Bool.false_eq_true, ↓reduceIte,
          beq_self_eq_true, Option.getD_some, hsop, opTok_plain hD,
          ne_beq (show ("im" : String) ≠ "(" by decide), ne_beq (show ("im" : String) ≠ ")" by decide)]
        simp
      | nan => exact ⟨"*", by simp [toksI, ftAux, signJ, opTok], by decide, by decide⟩
      | posInf => exact ⟨"*", by simp [toksI, ftAux, signJ, opTok], by decide, by decide⟩
      | negInf => exact ⟨"*", by simp [toksI, ftAux, signJ, opTok], by decide, by decide⟩
    have hft : ftAux (toksR r ++ signJ i :: toksI i) none 0 0 =
        ((toksR r).length, signJ i) :: [((toksR r).length + 2, t)] := by
      rw [ftAux_top rb, rft, List.nil_append]
      simp only [ftAux, ne_beq hs1, ne_beq hs2, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, hlo,
        beq_self_eq_true]
      simp only [hpos, decide_true, Bool.not_false, Bool.and_self, ↓reduceIte, ht]
    have ho : outerP (toksR r ++ signJ i :: toksI i) = false := outerP_head (by
      cases h : toksR r with
      | nil => exact absurd h rne
      | cons x xs => rw [h] at rhead; simpa using rhead)
    have hR := parse_R r hv.1 f (by simp at hf'; omega)
    have hI := parse_I i hv.2 f (by simp at hf'; omega)
    rw [mpt_succ, mpt_low (metaParseTokens f) hsgn ho _ (by simpa using htc) hft hR hI]
    rfl

/-! ## Normalization -/

theorem normalize_NaN {names : List String} (h : names.contains "NaN" = false) :
    normalize (some names) (.symbol "NaN") = .literal (.real .nan) := by
  unfold normalize normalizeSymbol
  have hc : ¬ (((some names).map (fun ns => ns.contains "NaN")).getD false = true) := by
    show ¬ (names.contains "NaN" = true)
    rw [h]
    decide
  rw [if_neg hc, if_neg (by decide), if_pos (by decide)]

theorem normalize_Inf {names : List String} (h : names.contains "Inf" = false) :
    normalize (some names) (.symbol "Inf") = .literal (.real .posInf) := by
  unfold normalize normalizeSymbol
  have hc : ¬ (((some names).map (fun ns => ns.contains "Inf")).getD false = true) := by
    show ¬ (names.contains "Inf" = true)
    rw [h]
    decide
  rw [if_neg hc, if_neg (by decide), if_neg (by decide), if_pos (by decide)]

theorem normalize_R {names : List String} (hnan : names.contains "NaN" = false)
    (hinf : names.contains "Inf" = false) (w : JF) :
    normalize (some names) (surfR w) = .literal (.real w) := by
  cases w with
  | fin q => exact normalize_literal _ _
  | nan => exact normalize_NaN hnan
  | posInf => exact normalize_Inf hinf
  | negInf =>
    simp only [surfR]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_nil, normalize_Inf hinf]
    rfl

theorem mul_fin_one (x : JF) : x * JF.fin 1 = x := by
  cases x with
  | fin q => show JF.fin (q * 1) = JF.fin q; rw [Rat.mul_one]
  | nan => rfl
  | posInf => rfl
  | negInf => rfl

theorem normalize_I {names : List String} (hnan : names.contains "NaN" = false)
    (hinf : names.contains "Inf" = false) (him : names.contains "im" = false) (w : JF) :
    normalize (some names) (surfI w) = .literal (.complex (.fin 0) (imagVal w)) := by
  cases w with
  | fin q =>
    simp only [surfI]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil,
      normalize_literal, normalize_im him]
    show Surface.literal (.complex (.fin 0) (JF.fin (imagMag q) * JF.fin 1)) = _
    rw [mul_fin_one]
    rfl
  | nan =>
    simp only [surfI]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil,
      normalize_NaN hnan, normalize_im him]
    rfl
  | posInf =>
    simp only [surfI]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil,
      normalize_Inf hinf, normalize_im him]
    rfl
  | negInf =>
    simp only [surfI]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil,
      normalize_Inf hinf, normalize_im him]
    rfl

theorem normalize_C {names : List String} (hnan : names.contains "NaN" = false)
    (hinf : names.contains "Inf" = false) (v : Scalar)
    (him : ∀ r i, v = .complex r i → names.contains "im" = false) :
    normalize (some names) (surfC v) = .literal (demoteScalar v) := by
  cases v with
  | real w => exact normalize_R hnan hinf w
  | float32 w => exact normalize_R hnan hinf w
  | complex r i =>
    simp only [surfC]
    rw [normalize_call, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil,
      normalize_R hnan hinf, normalize_I hnan hinf (him r i rfl)]
    cases i with
    | fin q =>
      unfold signJ imagSign imagVal imagMag
      by_cases h : q.num < 0
      · simp only [h, ↓reduceIte]
        show Surface.literal (.complex r (-(JF.fin (-q)))) = _
        show Surface.literal (.complex r (JF.fin (-(-q)))) = _
        rw [Rat.neg_neg]
        rfl
      · simp only [h, ↓reduceIte]
        rfl
    | nan => rfl
    | posInf => rfl
    | negInf => rfl

/-! ## Roundtrip -/

/-- Every constant whose finite parts are terminating decimals prints and parses
back to the same value, with Float32 values read as Float64 (Q19), when the
names vector does not declare `NaN` or `Inf` (Q41), nor `im` for complex
constants (Q21). -/
theorem constRoundtrip (ops : Operators) (names : List String) (v : Scalar) (hv : ConstOK v)
    (hnan : names.contains "NaN" = false) (hinf : names.contains "Inf" = false)
    (him : ∀ r i, v = .complex r i → names.contains "im" = false) :
    ∃ text, stringTree {operators := some ops, names := some names} (.const v) = .ok text ∧
      parseString {operators := ops, names := some names} text =
        .ok ⟨"Node", .const (demoteScalar v)⟩ := by
  refine ⟨scalarText v, stringTree_const ops names v hv, ?_⟩
  have hlexed : lex ((scalarText v).length + 1) (scalarText v).toList = toksC v :=
    lexOK_C v hv _ (by rw [String.length_toList]; omega)
  have hfuel : (toksC v).length ≤ (scalarText v).length + 1 := by
    rw [← hlexed]; exact lex_length _ _
  unfold parseString metaParse
  rw [hlexed, parse_C v hv _ hfuel]
  show parseCore _ _ (normalize (some names) (surfC v)) = _
  rw [normalize_C hnan hinf v him]
  rfl

end DynExpr.StringsParse.Roundtrip
