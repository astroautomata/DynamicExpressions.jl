import DynExpr.StringsParse.Parse

/-! Token-level facts about the `Meta.parse` subset of `src/Parse.jl:297`
(mirrored in `Surface.lean`). The mirror's helpers are private, so this file
restates them verbatim and bridges `metaParseTokens` to the restatement by
definitional unfolding. -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-! ## Verbatim restatements of the private helpers of `Surface.lean` -/

def topPos (ts : List String) : List (Nat × String) := Id.run do
  let mut depth := 0
  let mut out := []
  for (t, i) in ts.zipIdx do
    if t == "(" then depth := depth + 1
    else if t == ")" then depth := depth - 1
    else if depth == 0 then out := out ++ [(i, t)]
  return out

def outerP (ts : List String) : Bool := Id.run do
  if ts.head? != some "(" || ts.getLast? != some ")" then return false
  let mut depth := 0
  for (t, i) in ts.zipIdx do
    if t == "(" then depth := depth + 1
    if t == ")" then depth := depth - 1
    if depth == 0 && i + 1 < ts.length then return false
  return true

def splitC (ts : List String) : List (List String) := Id.run do
  if ts.isEmpty then return []
  let mut start := 0
  let mut result := []
  for (i, t) in topPos ts do
    if t == "," then
      result := result ++ [(ts.drop start).take (i - start)]
      start := i + 1
  return result ++ [ts.drop start]

def splitP (ts : List String) (positions : List Nat) : List (List String) := Id.run do
  let mut start := 0
  let mut out := []
  for i in positions do
    out := out ++ [(ts.drop start).take (i - start)]
    start := i + 1
  return out ++ [ts.drop start]

/-- Operator-position filter of `metaParseTokens`. -/
def opTok (s : String) : Bool := ["+", "-", "*", "/", "^", "(", ","].contains s

/-- One step of `metaParseTokens` with the recursive call abstracted. -/
def mptBody (rec : List String → Jl Surface) (ts : List String) : Jl Surface := do
      if ts.isEmpty then throw (.argumentError "empty expression")
      if outerP ts then return ← rec (ts.drop 1 |>.take (ts.length - 2))
      let tops := (topPos ts).filter (fun p => p.1 > 0 &&
        !( ["+", "-", "*", "/", "^", "(", ","].contains (ts[p.1 - 1]?.getD "")))
      let low := tops.filter (fun p => p.2 == "+" || p.2 == "-")
      let mid := tops.filter (fun p => p.2 == "*" || p.2 == "/")
      let high := tops.filter (fun p => p.2 == "^")
      if low.isEmpty && mid.isEmpty && !high.isEmpty &&
          (ts.head? == some "-" || ts.head? == some "+") then
        return .call (ts.head?.getD "") [← rec (ts.drop 1)]
      let split := if !low.isEmpty then low.getLast? else if !mid.isEmpty then mid.getLast? else high.head?
      if let some (i, op) := split then
        if op == "+" || op == "*" then
          let level := if op == "+" then low else mid
          let suffix := level.reverse.takeWhile (fun p => p.2 == op) |>.reverse
          if suffix.length > 1 then
            return .call op (← (splitP ts (suffix.map Prod.fst)).mapM rec)
        return .call op [← rec (ts.take i), ← rec (ts.drop (i + 1))]
      if ts[1]? == some "(" && ts.getLast? == some ")" then
        let args ← (splitC (ts.drop 2 |>.take (ts.length - 3))).mapM rec
        let name := ts.head?.getD ""
        if name == "-" || name == "+" then
          if let [.literal v] := args then
            return .literal (if name == "-" then v.neg else v)
        return .call name args
      if ts.head? == some "-" || ts.head? == some "+" then
        let arg ← rec (ts.drop 1)
        return match arg with
          | .literal v => .literal (if ts.head? == some "-" then v.neg else v)
          | _ => .call (ts.head?.getD "") [arg]
      if ts.length == 2 && ts[1]? == some "im" then
        return .call "*" [← rec (ts.take 1), .symbol "im"]
      if ts.length == 1 then
        let t := ts.head?.getD ""
        return match numericToken t with
          | some v => .literal v
          | none => .symbol t
      if ts[1]? == some "." && ts[2]? == some "(" && ts.getLast? == some ")" then
        let args ← (splitC (ts.drop 3 |>.take (ts.length - 4))).mapM rec
        return .dotCall (ts.head?.getD "") args
      if ts.head? == some "{" && ts.getLast? == some "}" then return .unsupported "braces"
      if ts.head? == some "[" && ts.getLast? == some "]" then return .unsupported "vect"
      return .unsupported (if ts.contains "." then "." else "syntax")

theorem mpt_succ (fuel : Nat) (ts : List String) :
    metaParseTokens (fuel + 1) ts = mptBody (metaParseTokens fuel) ts := by
  first
    | rfl
    | (rw [metaParseTokens]; rfl)
    | (simp only [metaParseTokens]; rfl)

/-! ## Loops in `Id` -/

def runSteps {α σ : Type} (step : α → σ → ForInStep σ) : List α → σ → σ
  | [], s => s
  | a :: l, s =>
      match step a s with
      | .done s' => s'
      | .yield s' => runSteps step l s'

theorem forIn_id {α σ : Type} (l : List α) (s : σ) (step : α → σ → Id (ForInStep σ)) :
    (forIn l s step : Id σ) = runSteps step l s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons]
    cases h : step a s with
    | done b =>
      simp only [runSteps, h]
      rfl
    | yield b =>
      simp only [runSteps, h]
      exact ih b

theorem runSteps_congr {α σ : Type} (step G : α → σ → ForInStep σ)
    (h : ∀ a s, step a s = G a s) (l : List α) (s : σ) :
    runSteps step l s = runSteps G l s := by
  have : step = G := funext fun a => funext fun s => h a s
  rw [this]

/-! ## Balanced token lists and top-level positions -/

/-- Token lists with balanced parentheses. -/
inductive Bal : List String → Prop
  | nil : Bal []
  | tok {t : String} {rest : List String} : t ≠ "(" → t ≠ ")" → Bal rest → Bal (t :: rest)
  | grp {x rest : List String} : Bal x → Bal rest → Bal ("(" :: (x ++ ")" :: rest))

theorem Bal.append {x y : List String} (hx : Bal x) (hy : Bal y) : Bal (x ++ y) := by
  induction hx with
  | nil => simpa using hy
  | tok h1 h2 _ ih => exact .tok h1 h2 ih
  | @grp x rest hx _ _ ihr =>
    have := Bal.grp hx ihr
    simpa [List.append_assoc] using this

theorem Bal.group {x : List String} (hx : Bal x) : Bal ("(" :: x ++ [")"]) := by
  have := Bal.grp hx Bal.nil
  simpa using this

theorem Bal.single {t : String} (h1 : t ≠ "(") (h2 : t ≠ ")") : Bal [t] := .tok h1 h2 .nil

/-- Clean recursive form of the top-level position loop. -/
def topAux : List String → Nat → Nat → List (Nat × String)
  | [], _, _ => []
  | t :: ts, i, d =>
    if t == "(" then topAux ts (i + 1) (d + 1)
    else if t == ")" then topAux ts (i + 1) (d - 1)
    else if d == 0 then (i, t) :: topAux ts (i + 1) d
    else topAux ts (i + 1) d

theorem ne_beq {a b : String} (h : a ≠ b) : (a == b) = false := by
  simp [h]

theorem topAux_deep {x : List String} (hx : Bal x) :
    ∀ (y : List String) (i d : Nat), 0 < d → topAux (x ++ y) i d = topAux y (i + x.length) d := by
  induction hx with
  | nil => intro y i d _; simp
  | @tok t rest h1 h2 _ ih =>
    intro y i d hd
    have hd' : (d == 0) = false := by simp; omega
    simp only [List.cons_append, topAux, ne_beq h1, ne_beq h2, hd', Bool.false_eq_true, ↓reduceIte]
    rw [ih y (i + 1) d hd]
    simp only [List.length_cons]
    congr 1
    omega
  | @grp x rest _ _ ihx ihr =>
    intro y i d hd
    simp only [List.cons_append, List.append_assoc, topAux, beq_self_eq_true, ↓reduceIte]
    rw [ihx (")" :: (rest ++ y)) (i + 1) (d + 1) (by omega)]
    have hrp : ((")" : String) == "(") = false := by decide
    simp only [topAux, hrp, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [ihr y _ d hd]
    simp only [List.length_cons, List.length_append]
    congr 1
    omega

theorem topAux_top {x : List String} (hx : Bal x) :
    ∀ (y : List String) (i : Nat), topAux (x ++ y) i 0 = topAux x i 0 ++ topAux y (i + x.length) 0 := by
  induction hx with
  | nil => intro y i; simp [topAux]
  | @tok t rest h1 h2 _ ih =>
    intro y i
    simp only [List.cons_append, topAux, ne_beq h1, ne_beq h2, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, List.cons_append]
    rw [ih y (i + 1)]
    have hl : i + 1 + rest.length = i + (rest.length + 1) := by omega
    simp only [List.length_cons, hl, List.cons_append]
  | @grp x rest hx _ _ ihr =>
    intro y i
    have hrp : ((")" : String) == "(") = false := by decide
    simp only [List.cons_append, List.append_assoc, topAux, beq_self_eq_true, ↓reduceIte]
    rw [topAux_deep hx (")" :: (rest ++ y)) (i + 1) 1 (by omega),
      topAux_deep hx (")" :: rest) (i + 1) 1 (by omega)]
    simp only [topAux, hrp, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.sub_self]
    rw [ihr y]
    simp only [List.length_cons, List.length_append]
    congr 2
    omega

theorem topAux_group {x : List String} (hx : Bal x) (y : List String) (i : Nat) :
    topAux ("(" :: x ++ ")" :: y) i 0 = topAux y (i + x.length + 2) 0 := by
  have hrp : ((")" : String) == "(") = false := by decide
  simp only [List.cons_append, topAux, beq_self_eq_true, ↓reduceIte]
  rw [topAux_deep hx (")" :: y) (i + 1) 1 (by omega)]
  simp only [topAux, hrp, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.sub_self]
  congr 1
  omega

/-! ## Filtered top-level operator positions -/

/-- Top-level tokens kept by the operator-position filter, tracking the
previous token. -/
def ftAux : List String → Option String → Nat → Nat → List (Nat × String)
  | [], _, _, _ => []
  | t :: ts, prev, i, d =>
    if t == "(" then ftAux ts (some t) (i + 1) (d + 1)
    else if t == ")" then ftAux ts (some t) (i + 1) (d - 1)
    else if d == 0 then
      if (i > 0 && !opTok (prev.getD "")) = true then (i, t) :: ftAux ts (some t) (i + 1) d
      else ftAux ts (some t) (i + 1) d
    else ftAux ts (some t) (i + 1) d

def keep (ws : List String) (p : Nat × String) : Bool :=
  p.1 > 0 && !( ["+", "-", "*", "/", "^", "(", ","].contains (ws[p.1 - 1]?.getD ""))

theorem getElem?_pre_last (pre ts : List String) (h : pre ≠ []) :
    (pre ++ ts)[pre.length - 1]? = pre.getLast? := by
  rw [List.getElem?_append_left (by
    cases pre with
    | nil => exact absurd rfl h
    | cons a l => simp)]
  rw [List.getLast?_eq_getElem?]

theorem filter_topAux (ts : List String) :
    ∀ (pre : List String) (d : Nat),
      (topAux ts pre.length d).filter (keep (pre ++ ts)) = ftAux ts pre.getLast? pre.length d := by
  induction ts with
  | nil => intro pre d; simp [topAux, ftAux]
  | cons t ts ih =>
    intro pre d
    have hstep := ih (pre ++ [t])
    simp only [List.length_append, List.length_cons, List.length_nil, List.getLast?_append,
      List.getLast?_singleton, Option.some_or, List.append_assoc, List.cons_append,
      List.nil_append] at hstep
    simp only [topAux, ftAux]
    by_cases h1 : t = "("
    · subst h1
      simp only [beq_self_eq_true, ↓reduceIte]
      exact hstep (d + 1)
    by_cases h2 : t = ")"
    · subst h2
      simp only [beq_self_eq_true, ↓reduceIte, ne_beq (show (")" : String) ≠ "(" by decide),
        Bool.false_eq_true]
      exact hstep (d - 1)
    simp only [ne_beq h1, ne_beq h2, Bool.false_eq_true, ↓reduceIte]
    by_cases hd : d = 0
    · subst hd
      simp only [beq_self_eq_true, ↓reduceIte, List.filter_cons]
      have hk : keep (pre ++ t :: ts) (pre.length, t) =
          (pre.length > 0 && !opTok (pre.getLast?.getD "")) := by
        cases pre with
        | nil => simp [keep]
        | cons a l =>
          have := getElem?_pre_last (a :: l) (t :: ts) (by simp)
          simp only [keep, opTok, this]
          try simp
      rw [hk]
      split <;> simp [hstep 0]
    · have hd' : (d == 0) = false := by simp [hd]
      simp only [hd', Bool.false_eq_true, ↓reduceIte]
      exact hstep d

/-- Previous token after scanning `x`. -/
def lastOr (x : List String) (prev : Option String) : Option String :=
  match x.getLast? with
  | some t => some t
  | none => prev

theorem lastOr_cons (t : String) (x : List String) (prev : Option String) :
    lastOr x (some t) = lastOr (t :: x) prev := by
  unfold lastOr
  cases h : x.getLast? with
  | none =>
    have : x = [] := List.getLast?_eq_none_iff.mp h
    subst this; rfl
  | some u =>
    rw [List.getLast?_cons, h]
    rfl

theorem lastOr_suffix (pre rest : List String) (t : String) (prev : Option String) :
    lastOr rest (some t) = lastOr (pre ++ t :: rest) prev := by
  unfold lastOr
  simp only [List.getLast?_append, List.getLast?_cons, Option.some_or]
  cases h : rest.getLast? <;> simp [h]

theorem ftAux_deep {x : List String} (hx : Bal x) :
    ∀ (y : List String) (prev : Option String) (i d : Nat), 0 < d →
      ftAux (x ++ y) prev i d = ftAux y (lastOr x prev) (i + x.length) d := by
  induction hx with
  | nil => intro y prev i d _; simp [lastOr]
  | @tok t rest h1 h2 _ ih =>
    intro y prev i d hd
    have hd' : (d == 0) = false := by simp; omega
    simp only [List.cons_append, ftAux, ne_beq h1, ne_beq h2, hd', Bool.false_eq_true, ↓reduceIte]
    rw [ih y (some t) (i + 1) d hd, lastOr_cons t rest prev]
    simp only [List.length_cons]
    congr 1
    omega
  | @grp x rest _ _ ihx ihr =>
    intro y prev i d hd
    simp only [List.cons_append, List.append_assoc, ftAux, beq_self_eq_true, ↓reduceIte]
    rw [ihx (")" :: (rest ++ y)) (some "(") (i + 1) (d + 1) (by omega)]
    have hrp : ((")" : String) == "(") = false := by decide
    simp only [ftAux, hrp, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [ihr y _ _ d hd]
    have hl : lastOr rest (some ")") = lastOr ("(" :: (x ++ ")" :: rest)) prev := by
      have := lastOr_suffix ("(" :: x) rest ")" prev
      simpa using this
    rw [hl]
    simp only [List.length_cons, List.length_append]
    congr 1
    omega

theorem ftAux_group {x : List String} (hx : Bal x) (y : List String) (prev : Option String) (i : Nat) :
    ftAux ("(" :: x ++ ")" :: y) prev i 0 = ftAux y (some ")") (i + x.length + 2) 0 := by
  have hrp : ((")" : String) == "(") = false := by decide
  simp only [List.cons_append, ftAux, beq_self_eq_true, ↓reduceIte]
  rw [ftAux_deep hx (")" :: y) (some "(") (i + 1) 1 (by omega)]
  simp only [ftAux, hrp, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Nat.sub_self]
  congr 1
  omega

theorem ftAux_top {x : List String} (hx : Bal x) :
    ∀ (y : List String) (prev : Option String) (i : Nat),
      ftAux (x ++ y) prev i 0 = ftAux x prev i 0 ++ ftAux y (lastOr x prev) (i + x.length) 0 := by
  induction hx with
  | nil => intro y prev i; simp [ftAux, lastOr]
  | @tok t rest h1 h2 _ ih =>
    intro y prev i
    simp only [List.cons_append, ftAux, ne_beq h1, ne_beq h2, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte]
    rw [ih y (some t) (i + 1), lastOr_cons t rest prev]
    have hl : i + 1 + rest.length = i + (rest.length + 1) := by omega
    split <;> simp [hl]
  | @grp x rest hx hr _ ihr =>
    intro y prev i
    have e1 := ftAux_group hx (rest ++ y) prev i
    have e2 := ftAux_group hx rest prev i
    simp only [List.cons_append, List.append_assoc] at e1 e2 ⊢
    rw [e1, e2, ihr y _ _]
    have hl : lastOr rest (some ")") = lastOr ("(" :: (x ++ ")" :: rest)) prev := by
      have := lastOr_suffix ("(" :: x) rest ")" prev
      simpa using this
    rw [hl]
    simp only [List.length_cons, List.length_append]
    congr 2
    omega

theorem ftAux_prefix_any {n : String} {x : List String} (hn1 : n ≠ "(") (hn2 : n ≠ ")") (hx : Bal x)
    (prev : Option String) (j : Nat) (hj : j = 0 ∨ opTok (prev.getD "") = true) :
    ftAux (n :: "(" :: x ++ [")"]) prev j 0 = [] := by
  have e := ftAux_group hx [] (some n) (j + 1)
  have hk : (decide (j > 0) && !opTok (prev.getD "")) = false := by
    rcases hj with rfl | hj
    · simp
    · simp [hj]
  simp only [List.cons_append] at e ⊢
  rw [ftAux]
  simp only [ne_beq hn1, ne_beq hn2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, hk]
  rw [e]; rfl

theorem ftAux_prefix {n : String} {x : List String} (hn1 : n ≠ "(") (hn2 : n ≠ ")") (hx : Bal x) :
    ftAux (n :: "(" :: x ++ [")"]) none 0 0 = [] :=
  ftAux_prefix_any hn1 hn2 hx none 0 (Or.inl rfl)

theorem topAux_prefix_any {n : String} {x : List String} (hn1 : n ≠ "(") (hn2 : n ≠ ")") (hx : Bal x)
    (i : Nat) : topAux (n :: "(" :: x ++ [")"]) i 0 = [(i, n)] := by
  have e := topAux_group hx [] (i + 1)
  simp only [List.cons_append] at e ⊢
  rw [topAux]
  simp only [ne_beq hn1, ne_beq hn2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  rw [e]; rfl

theorem ftAux_wrapped {x : List String} (hx : Bal x) (prev : Option String) (j : Nat) :
    ftAux ("(" :: x ++ [")"]) prev j 0 = [] := by
  have e := ftAux_group hx [] prev j
  simp only [List.cons_append] at e ⊢
  rw [e]; rfl

theorem topAux_wrapped {x : List String} (hx : Bal x) (i : Nat) :
    topAux ("(" :: x ++ [")"]) i 0 = [] := by
  have e := topAux_group hx [] i
  simp only [List.cons_append] at e ⊢
  rw [e]; rfl

end DynExpr.StringsParse.Roundtrip
