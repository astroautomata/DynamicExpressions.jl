import DynExpr.StringsParse.Roundtrip.Domain

/-! Character-level lexing of rendered text (`lex` in `Surface.lean`, modelling
`Meta.parse` at `src/Parse.jl:297`). -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-- Lexing `cs` with any sufficient fuel yields `ts`. -/
def LexOK (cs : List Char) (ts : List String) : Prop :=
  ∀ fuel, cs.length < fuel → lex fuel cs = ts

/-- Characters that may follow a rendered subexpression. -/
def Bd (r : List Char) : Prop := ∀ x ∈ r.head?, x = ' ' ∨ x = ')' ∨ x = ','

theorem lex_length (fuel : Nat) (cs : List Char) : (lex fuel cs).length ≤ fuel := by
  induction fuel generalizing cs with
  | zero => simp [lex]
  | succ f ih =>
    cases cs with
    | nil => simp [lex]
    | cons c rest =>
      rw [lex]
      split
      · have := ih rest; omega
      · split
        · simp only [List.length_cons]; exact Nat.succ_le_succ (ih _)
        · split
          · simp only [List.length_cons]; exact Nat.succ_le_succ (ih _)
          · simp only [List.length_cons]; have := ih rest; omega

theorem lexOK_nil : LexOK [] [] := by
  intro fuel h
  cases fuel with
  | zero => simp at h
  | succ f => simp [lex]

theorem lexOK_step {c : Char} {tok : String}
    (hlex : ∀ f rest, lex (f + 1) (c :: rest) = tok :: lex f rest)
    {r : List Char} {ts : List String} (hr : LexOK r ts) : LexOK (c :: r) (tok :: ts) := by
  intro fuel h
  cases fuel with
  | zero => simp at h
  | succ f =>
    rw [hlex, hr f (by simp at h; omega)]

theorem lexOK_ws {r : List Char} {ts : List String} (hr : LexOK r ts) : LexOK (' ' :: r) ts := by
  intro fuel h
  cases fuel with
  | zero => simp at h
  | succ f =>
    rw [lex]
    simp only [show (' ').isWhitespace = true by decide, ↓reduceIte]
    exact hr f (by simp at h; omega)

theorem lex_punct {c : Char} (h1 : c.isWhitespace = false) (h2 : c.isDigit = false)
    (h3 : c.isAlpha = false) (h4 : (c == '_') = false) (h5 : ¬ c.toNat > 127)
    (f : Nat) (rest : List Char) : lex (f + 1) (c :: rest) = String.singleton c :: lex f rest := by
  rw [lex]
  simp [h1, h2, h3, h4, h5]

theorem singleton_lp : String.singleton '(' = "(" := by decide
theorem singleton_rp : String.singleton ')' = ")" := by decide
theorem singleton_comma : String.singleton ',' = "," := by decide
theorem singleton_plus : String.singleton '+' = "+" := by decide
theorem singleton_minus : String.singleton '-' = "-" := by decide
theorem singleton_star : String.singleton '*' = "*" := by decide
theorem singleton_slash : String.singleton '/' = "/" := by decide
theorem singleton_caret : String.singleton '^' = "^" := by decide

theorem lexOK_lp {r ts} (h : LexOK r ts) : LexOK ('(' :: r) ("(" :: ts) :=
  lexOK_step (fun f rest => by
    rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide), singleton_lp]) h
theorem lexOK_rp {r ts} (h : LexOK r ts) : LexOK (')' :: r) (")" :: ts) :=
  lexOK_step (fun f rest => by
    rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide), singleton_rp]) h
theorem lexOK_comma {r ts} (h : LexOK r ts) : LexOK (',' :: r) ("," :: ts) :=
  lexOK_step (fun f rest => by
    rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide), singleton_comma]) h
theorem lexOK_minus {r ts} (h : LexOK r ts) : LexOK ('-' :: r) ("-" :: ts) :=
  lexOK_step (fun f rest => by
    rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide), singleton_minus]) h

theorem infix_toList {n : String} (h : infixName n = true) :
    ∃ c, n.toList = [c] ∧ String.singleton c = n ∧ c.isWhitespace = false ∧ c.isDigit = false ∧
      c.isAlpha = false ∧ (c == '_') = false ∧ ¬ c.toNat > 127 ∧ c ≠ '(' := by
  rcases infixName_cases h with
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨'+', by decide, singleton_plus, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨'-', by decide, singleton_minus, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨'*', by decide, singleton_star, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨'/', by decide, singleton_slash, by decide, by decide, by decide, by decide, by decide, by decide⟩
  · exact ⟨'^', by decide, singleton_caret, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem lexOK_infix {n : String} (h : infixName n = true) {r ts} (hr : LexOK r ts) :
    LexOK (n.toList ++ r) (n :: ts) := by
  obtain ⟨c, hl, hs, h1, h2, h3, h4, h5, _⟩ := infix_toList h
  rw [hl, List.singleton_append, ← hs]
  exact lexOK_step (fun f rest => lex_punct h1 h2 h3 h4 h5 f rest) hr

/-- Identifier characters as the lexer reads them. -/
def identChar (x : Char) : Bool := x.isAlphanum || x == '_' || decide (x.toNat > 127)

theorem span_append (p : Char → Bool) (xs ys : List Char)
    (hx : ∀ x ∈ xs, p x = true) (hy : ∀ y ∈ ys.head?, p y = false) :
    (xs ++ ys).span p = (xs, ys) := by
  unfold List.span
  rw [span_loop_append p xs ys [] hx hy]
  simp

theorem lex_ident {s : String} (hs : asciiIdent s = true) {rest : List Char}
    (hb : ∀ x ∈ rest.head?, identChar x = false) (f : Nat) :
    lex (f + 1) (s.toList ++ rest) = s :: lex f rest := by
  unfold asciiIdent at hs
  cases hl : s.toList with
  | nil => rw [hl] at hs; simp at hs
  | cons c cs =>
    rw [hl] at hs
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    obtain ⟨⟨⟨ha, hw⟩, hd⟩, hall⟩ := hs
    have hspan : (cs ++ rest).span identChar = (cs, rest) := by
      apply span_append
      · intro x hx
        have := List.all_eq_true.mp hall x hx
        simp only [identChar]
        simp only [Bool.or_eq_true] at this ⊢
        rcases this with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · exact hb
    rw [List.cons_append, lex]
    have hstr : String.ofList (c :: cs) = s := by rw [← hl, String.ofList_toList]
    simp only [hw, hd, Bool.false_eq_true, ↓reduceIte]
    have hA : (c.isAlpha || c == '_' || decide (c.toNat > 127)) = true := by
      simp only [Bool.or_eq_true] at ha ⊢
      exact Or.inl ha
    simp only [hA, ↓reduceIte]
    show (match (cs ++ rest).span identChar with
      | (body, rest) => String.ofList (c :: body) :: lex f rest) = s :: lex f rest
    rw [hspan]
    show String.ofList (c :: cs) :: lex f rest = _
    rw [hstr]

theorem lexOK_ident {s : String} (hs : asciiIdent s = true) {r : List Char} {ts : List String}
    (hb : ∀ x ∈ r.head?, identChar x = false) (hr : LexOK r ts) : LexOK (s.toList ++ r) (s :: ts) := by
  intro fuel h
  have hne : s.toList ≠ [] := by
    intro he; unfold asciiIdent at hs; rw [he] at hs; simp at hs
  have hlen : 0 < s.toList.length := by
    cases h : s.toList with
    | nil => exact absurd h hne
    | cons _ _ => simp
  cases fuel with
  | zero => simp at h
  | succ f =>
    rw [lex_ident hs hb, hr f (by simp at h; omega)]

theorem bd_ident {r : List Char} (h : Bd r) : ∀ x ∈ r.head?, identChar x = false := by
  intro x hx
  rcases h x hx with rfl | rfl | rfl <;> decide

theorem paren_ident : ∀ x ∈ ('(' :: ([] : List Char)).head?, identChar x = false := by
  intro x hx; simp at hx; subst hx; decide

theorem identChar_lp (r : List Char) : ∀ x ∈ ('(' :: r).head?, identChar x = false := by
  intro x hx; simp at hx; subst hx; decide

end DynExpr.StringsParse.Roundtrip
