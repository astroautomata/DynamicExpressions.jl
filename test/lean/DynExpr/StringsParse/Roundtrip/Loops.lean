import DynExpr.StringsParse.Roundtrip.Tokens

/-! The `for` loops of the restated helpers as clean recursions. Each step
function restates the elaborated loop body. -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

def stepTop (x : String × Nat) (s : Nat × List (Nat × String)) :
    ForInStep (Nat × List (Nat × String)) :=
  match x with
  | (t, i) =>
    if (t == "(") = true then .yield (s.1 + 1, s.2)
    else if (t == ")") = true then .yield (s.1 - 1, s.2)
    else if (s.1 == 0) = true then .yield (s.1, s.2 ++ [(i, t)])
    else .yield (s.1, s.2)

theorem runSteps_top (l : List String) :
    ∀ (i d : Nat) (out : List (Nat × String)),
      (runSteps stepTop (l.zipIdx i) (d, out)).2 = out ++ topAux l i d := by
  induction l with
  | nil => intro i d out; simp [runSteps, topAux]
  | cons t l ih =>
    intro i d out
    rw [List.zipIdx_cons]
    simp only [runSteps, stepTop, topAux]
    by_cases h1 : (t == "(") = true
    · simp only [h1, ↓reduceIte]; exact ih _ _ _
    by_cases h2 : (t == ")") = true
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]; exact ih _ _ _
    by_cases h3 : (d == 0) = true
    · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
      rw [ih]; simp
    · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
      exact ih _ _ _

theorem topPos_eq (ts : List String) : topPos ts = topAux ts 0 0 := by
  have h : topPos ts = (runSteps stepTop (ts.zipIdx) (0, [])).2 := by
    unfold topPos
    simp only [Id.run, forIn_id]
    rfl
  rw [h, runSteps_top]
  simp

theorem outerP_head {ts : List String} (h : ts.head? ≠ some "(") : outerP ts = false := by
  have : (ts.head? != some "(") = true := by simpa using h
  unfold outerP
  simp [Id.run, this]
  rfl

/-- The outer-parenthesis loop never exits inside a balanced group. -/
theorem runSteps_deep_spec {step : String × Nat → Option Bool × Nat → ForInStep (Option Bool × Nat)}
    (hplain : ∀ t i d, t ≠ "(" → t ≠ ")" → 0 < d → step (t, i) (none, d) = .yield (none, d))
    (hopen : ∀ i d, 0 < d → step ("(", i) (none, d) = .yield (none, d + 1))
    (hclose : ∀ i d, 0 < d → step (")", i) (none, d + 1) = .yield (none, d))
    {x : List String} (hx : Bal x) :
    ∀ (z : List String) (i d : Nat), 0 < d →
      runSteps step ((x ++ z).zipIdx i) (none, d) = runSteps step (z.zipIdx (i + x.length)) (none, d) := by
  induction hx with
  | nil => intro z i d _; simp
  | @tok t rest h1 h2 _ ih =>
    intro z i d hd
    rw [List.cons_append, List.zipIdx_cons]
    simp only [runSteps, hplain t i d h1 h2 hd]
    rw [ih z (i + 1) d hd]
    simp only [List.length_cons]
    congr 2
    omega
  | @grp x rest _ _ ihx ihr =>
    intro z i d hd
    rw [List.cons_append, List.zipIdx_cons, List.append_assoc]
    simp only [runSteps, hopen i d hd]
    rw [ihx ((")" :: rest) ++ z) (i + 1) (d + 1) (by omega), List.cons_append, List.zipIdx_cons]
    simp only [runSteps, hclose _ d hd]
    rw [ihr z _ d hd]
    simp only [List.length_cons, List.length_append]
    congr 2
    omega

theorem outerP_group {x : List String} (hx : Bal x) : outerP ("(" :: x ++ [")"]) = true := by
  have hh : ((("(" :: x ++ [")"]) : List String).head? != some "(") = false := by simp
  have hl : ((("(" :: x ++ [")"]) : List String).getLast? != some ")") = false := by
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]; decide
  have hn : ¬ (1 + x.length + 1 < ("(" :: x ++ [")"]).length) := by simp; omega
  unfold outerP
  simp only [Id.run, forIn_id, hh, hl, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [List.cons_append, List.zipIdx_cons]
  simp only [runSteps, beq_self_eq_true, ↓reduceIte,
    ne_beq (show ("(" : String) ≠ ")" by decide), Bool.false_eq_true, Bool.false_and,
    Nat.zero_add, show ((0 : Nat) + 1 == 0) = false by decide,
    show ((1 : Nat) == 0) = false by decide, bind, pure]
  rw [runSteps_deep_spec ?_ ?_ ?_ hx [")"] 1 1 (by omega)]
  · have hrp : ((")" : String) == "(") = false := by decide
    have hn' : ¬ (1 + x.length < x.length + 1) := by omega
    simp [runSteps, hrp, hn']
  · intro t i d h1 h2 hd
    simp [ne_beq h1, ne_beq h2, Nat.pos_iff_ne_zero.mp hd]
  · intro i d hd
    simp [Nat.pos_iff_ne_zero.mp hd]
  · intro i d hd
    have hrp : ((")" : String) == "(") = false := by decide
    simp [hrp, Nat.pos_iff_ne_zero.mp hd]

theorem outerP_group_more {x y : List String} (hx : Bal x) (hy : y ≠ []) :
    outerP ("(" :: x ++ ")" :: y) = false := by
  unfold outerP
  simp only [Id.run, forIn_id]
  split
  · rfl
  · have hlt : 1 + x.length + 1 < ("(" :: x ++ ")" :: y).length := by
      cases y with
      | nil => exact absurd rfl hy
      | cons a l => simp; omega
    rw [List.cons_append, List.zipIdx_cons]
    simp only [runSteps, beq_self_eq_true, ↓reduceIte,
      ne_beq (show ("(" : String) ≠ ")" by decide), Bool.false_eq_true, Bool.false_and,
      Nat.zero_add, show ((0 : Nat) + 1 == 0) = false by decide,
      show ((1 : Nat) == 0) = false by decide, bind, pure]
    rw [runSteps_deep_spec ?_ ?_ ?_ hx (")" :: y) 1 1 (by omega), List.zipIdx_cons]
    · have hrp : ((")" : String) == "(") = false := by decide
      have hlt' : 1 + x.length < x.length + (y.length + 1) := by
        have : y.length ≠ 0 := by simpa using hy
        omega
      simp [runSteps, hrp, hlt']
    · intro t i d h1 h2 hd
      simp [ne_beq h1, ne_beq h2, Nat.pos_iff_ne_zero.mp hd]
    · intro i d hd
      simp [Nat.pos_iff_ne_zero.mp hd]
    · intro i d hd
      have hrp : ((")" : String) == "(") = false := by decide
      simp [hrp, Nat.pos_iff_ne_zero.mp hd]

def stepSplit (ts : List String) (x : Nat × String) (s : Nat × List (List String)) :
    ForInStep (Nat × List (List String)) :=
  match x with
  | (i, t) =>
    if (t == ",") = true then .yield (i + 1, s.2 ++ [List.take (i - s.1) (List.drop s.1 ts)])
    else .yield (s.1, s.2)

theorem splitC_eq {ts : List String} (hne : ts ≠ []) :
    splitC ts = (runSteps (stepSplit ts) (topPos ts) (0, [])).2 ++
      [ts.drop (runSteps (stepSplit ts) (topPos ts) (0, [])).1] := by
  have he : ts.isEmpty = false := by cases ts <;> simp_all
  unfold splitC
  simp only [Id.run, forIn_id, he, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem runSteps_split_none (ts : List String) (l : List (Nat × String))
    (h : ∀ p ∈ l, p.2 ≠ ",") (s : Nat × List (List String)) :
    runSteps (stepSplit ts) l s = (s.1, s.2) := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    have hp : (p.2 == ",") = false := by simpa using h p (by simp)
    obtain ⟨i, t⟩ := p
    simp only [runSteps, stepSplit]
    simp only at hp
    simp only [hp, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun q hq => h q (by simp [hq])) _

theorem splitC_single {x : List String} (hne : x ≠ []) (hc : ∀ p ∈ topAux x 0 0, p.2 ≠ ",") :
    splitC x = [x] := by
  rw [splitC_eq hne, topPos_eq, runSteps_split_none x _ hc]
  simp

theorem splitC_pair {x y : List String} (hx : Bal x) (hne : x ≠ [])
    (hcx : ∀ p ∈ topAux x 0 0, p.2 ≠ ",") (hcy : ∀ p ∈ topAux y (x.length + 1) 0, p.2 ≠ ",") :
    splitC (x ++ "," :: y) = [x, y] := by
  rw [splitC_eq (by simp), topPos_eq, topAux_top hx]
  have hcomma : topAux ("," :: y) (0 + x.length) 0 = (x.length, ",") :: topAux y (x.length + 1) 0 := by
    simp [topAux]
  rw [hcomma]
  have hrun : ∀ (l : List (Nat × String)) (s : Nat × List (List String)), (∀ p ∈ l, p.2 ≠ ",") →
      runSteps (stepSplit (x ++ "," :: y)) (l ++ (x.length, ",") :: topAux y (x.length + 1) 0) s =
        (x.length + 1, s.2 ++ [List.take (x.length - s.1) (List.drop s.1 (x ++ "," :: y))]) := by
    intro l
    induction l with
    | nil =>
      intro s _
      simp only [List.nil_append, runSteps, stepSplit, beq_self_eq_true, ↓reduceIte]
      rw [runSteps_split_none _ _ hcy]
    | cons p l ih =>
      intro s h
      have hp : (p.2 == ",") = false := by simpa using h p (by simp)
      obtain ⟨i, t⟩ := p
      simp only [List.cons_append, runSteps, stepSplit]
      simp only at hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact ih _ (fun q hq => h q (by simp [hq]))
  rw [hrun _ _ hcx]
  simp

end DynExpr.StringsParse.Roundtrip
