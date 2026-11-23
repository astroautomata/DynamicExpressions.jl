import DynExpr.StringsParse.Roundtrip.Loops
import DynExpr.StringsParse.Roundtrip.Domain

/-! Single steps of `metaParseTokens` on the token shapes of rendered trees
(`src/Parse.jl:297`, mirrored in `Surface.lean`). -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

theorem tops_eq (ts : List String) :
    (topPos ts).filter (fun p => p.1 > 0 &&
      !( ["+", "-", "*", "/", "^", "(", ","].contains (ts[p.1 - 1]?.getD ""))) = ftAux ts none 0 0 := by
  rw [topPos_eq]
  exact filter_topAux ts [] 0

/-- Tokens that are not operator, parenthesis, or comma tokens. -/
def plainTok (t : String) : Prop :=
  t ≠ "(" ∧ t ≠ ")" ∧ t ≠ "-" ∧ t ≠ "+" ∧ t ≠ "*" ∧ t ≠ "/" ∧ t ≠ "^" ∧ t ≠ ","

theorem plainTok_opTok {t : String} (h : plainTok t) : opTok t = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp [opTok, h1, h3, h4, h5, h6, h7, h8]

theorem mpt_single (rec : List String → Jl Surface) {tok : String} (h : plainTok tok) :
    mptBody rec [tok] = .ok (match numericToken tok with
      | some v => .literal v
      | none => .symbol tok) := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  have ho : outerP [tok] = false := outerP_head (by simpa using h1)
  have ht : ftAux [tok] none 0 0 = [] := by simp [ftAux, h1, h2]
  unfold mptBody
  rw [tops_eq, ht]
  simp [ho, h3, h4]
  try rfl

theorem mpt_neg (rec : List String → Jl Surface) {tok : String} (h : plainTok tok) {w : Scalar}
    (hrec : rec [tok] = .ok (.literal w)) :
    mptBody rec ["-", tok] = .ok (.literal w.neg) := by
  obtain ⟨h1, h2, _⟩ := h
  have ho : outerP ["-", tok] = false := outerP_head (by simp)
  have ht : ftAux ["-", tok] none 0 0 = [] := by
    simp [ftAux, h1, h2, opTok]
  unfold mptBody
  rw [tops_eq, ht]
  simp [ho, h1, hrec]
  try rfl

theorem mpt_im (rec : List String → Jl Surface) {tok : String} (h : plainTok tok) {s : Surface}
    (hrec : rec [tok] = .ok s) :
    mptBody rec [tok, "im"] = .ok (.call "*" [s, .symbol "im"]) := by
  have hop := plainTok_opTok h
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  have ho : outerP [tok, "im"] = false := outerP_head (by simpa using h1)
  have ht : ftAux [tok, "im"] none 0 0 = [(1, "im")] := by
    simp [ftAux, h1, h2, hop]
  unfold mptBody
  rw [tops_eq, ht]
  simp [ho, h3, h4, hrec]
  try rfl

theorem mpt_outer (rec : List String → Jl Surface) {x : List String} (hx : Bal x) {s : Surface}
    (hrec : rec x = .ok s) :
    mptBody rec ("(" :: (x ++ [")"])) = .ok s := by
  have ho : outerP ("(" :: (x ++ [")"])) = true := outerP_group hx
  unfold mptBody
  simp [ho, hrec]
  try rfl

/-- Result of a prefix call with parsed arguments (`src/Parse.jl:297`). -/
def prefixResult (n : String) (args : List Surface) : Surface :=
  if n == "-" || n == "+" then
    match args with
    | [.literal v] => .literal (if n == "-" then v.neg else v)
    | _ => .call n args
  else .call n args

theorem mpt_prefix (rec : List String → Jl Surface) {n : String} {x : List String}
    (hn1 : n ≠ "(") (hn2 : n ≠ ")") (hx : Bal x) (args : List Surface)
    (hargs : (splitC x).mapM rec = .ok args) :
    mptBody rec (n :: "(" :: (x ++ [")"])) = .ok (prefixResult n args) := by
  have ho : outerP (n :: "(" :: (x ++ [")"])) = false := outerP_head (by simpa using hn1)
  have ht : ftAux (n :: "(" :: (x ++ [")"])) none 0 0 = [] := ftAux_prefix hn1 hn2 hx
  have hdrop : ((n :: "(" :: (x ++ [")"])).drop 2).take ((n :: "(" :: (x ++ [")"])).length - 3) = x := by
    simp
  have hlast : (n :: "(" :: (x ++ [")"])).getLast? = some ")" := by
    simp only [List.getLast?_cons, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    simp
  unfold mptBody
  rw [tops_eq, ht, hdrop, hargs]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ho, List.filter_nil,
    List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_and, List.head?_nil,
    List.getElem?_cons_succ, List.getElem?_cons_zero, hlast, beq_self_eq_true, Bool.and_self,
    List.head?_cons, Option.getD_some, bind, Except.bind, pure, Except.pure, prefixResult]
  by_cases hc : (n == "-" || n == "+") = true
  · simp only [hc, ↓reduceIte]
    split <;> split <;> simp_all
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]

/-- Tops containing exactly one arithmetic operator. -/
def opCat (s : String) : Bool := s == "+" || s == "-" || s == "*" || s == "/" || s == "^"

theorem mpt_infix (rec : List String → Jl Surface) {A B : List String} {n : String}
    (hn : infixName n = true) (hA : A ≠ []) (ho : outerP (A ++ n :: B) = false)
    (post : List (Nat × String)) (hpost : ∀ p ∈ post, opCat p.2 = false)
    (ht : ftAux (A ++ n :: B) none 0 0 = (A.length, n) :: post)
    (hsign : n = "^" → A.head? ≠ some "-" ∧ A.head? ≠ some "+")
    {sa sb : Surface} (ha : rec A = .ok sa) (hb : rec B = .ok sb) :
    mptBody rec (A ++ n :: B) = .ok (.call n [sa, sb]) := by
  have hpost' : ∀ cat : String → Bool, (∀ s, cat s = true → opCat s = true) →
      post.filter (fun p => cat p.2) = [] := by
    intro cat hcat
    rw [List.filter_eq_nil_iff]
    intro p hp hc
    have := hcat _ hc
    rw [hpost p hp] at this
    cases this
  have hlow := hpost' (fun s => s == "+" || s == "-") (by
    intro s h; simp only [opCat, Bool.or_eq_true, beq_iff_eq] at h ⊢
    first | (rcases h with h | h <;> simp [h]) | simp [h])
  have hmid := hpost' (fun s => s == "*" || s == "/") (by
    intro s h; simp only [opCat, Bool.or_eq_true, beq_iff_eq] at h ⊢
    first | (rcases h with h | h <;> simp [h]) | simp [h])
  have hhigh := hpost' (fun s => s == "^") (by
    intro s h; simp only [opCat, Bool.or_eq_true, beq_iff_eq] at h ⊢
    first | (rcases h with h | h <;> simp [h]) | simp [h])
  have hne : (A ++ n :: B).isEmpty = false := by simp
  have htake : (A ++ n :: B).take A.length = A := by simp
  have hdrop : (A ++ n :: B).drop (A.length + 1) = B := by simp
  unfold mptBody
  rw [tops_eq, ht]
  simp only [hne, ho, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hlow, hmid, hhigh]
  rcases infixName_cases hn with
    rfl | rfl | rfl | rfl | rfl
  · simp [htake, hdrop, ha, hb]; try rfl
  · simp [htake, hdrop, ha, hb]; try rfl
  · simp [htake, hdrop, ha, hb]; try rfl
  · simp [htake, hdrop, ha, hb]; try rfl
  have hh := hsign rfl
  have hhead : (A ++ "^" :: B).head? = A.head? := by
    cases A with
    | nil => exact absurd rfl hA
    | cons a l => rfl
  simp [hhead, hh.1, hh.2, htake, hdrop, ha, hb]
  try rfl

end DynExpr.StringsParse.Roundtrip
