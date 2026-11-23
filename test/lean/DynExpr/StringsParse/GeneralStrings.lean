import DynExpr.StringsParse.Properties

namespace DynExpr.StringsParse.General

set_option maxRecDepth 1000
set_option maxHeartbeats 400000

/-! ## General prefix rendering (`stringsparse-prefix-stripping`) -/

/-- Julia's infix-head test: a two-argument call whose operator name starts
with one of these characters renders infix (`src/Strings.jl:106-133`). -/
def infixHeadChar (c : Char) : Bool :=
  ['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c

/-- The prefix layout is selected: either the call does not have exactly two
arguments (Julia then never inspects the operator name), or the name is
nonempty with first character `c`, `c` is not an infix head, and the name is
not `!=` (`src/Strings.jl:106-133`). -/
def IsPrefixCall (op : String) (args : List String) : Prop :=
  (args.length == 2) = false ∨
    ∃ c, (args.length == 2) = true ∧ op.toList.head? = some c ∧
      (infixHeadChar c || op == "!=") = false

/-- Independent specification of one-pair stripping: drop exactly one
enclosing parenthesis pair when the text is wrapped in one
(`src/Strings.jl:71-77`). -/
def stripOnce (s : String) : String :=
  if s.toList.head? == some '(' && s.toList.getLast? == some ')' then
    String.ofList (s.toList.drop 1 |>.take (s.length - 2))
  else s

/-- Independent prefix-layout specification (`src/Strings.jl:119-133`): the
operator name applied to each argument stripped of one enclosing parenthesis
pair, joined by comma-space. -/
def prefixLayout (op : String) (args : List String) : String :=
  op ++ "(" ++ String.intercalate ", " (args.map stripOnce) ++ ")"

/-- For every operator name and every nonempty argument list taking the
prefix layout with nonempty arguments, rendering equals the independent
prefix specification: one-pair stripping per argument and comma-separated
argument text (`src/Strings.jl:106-133`). -/
def PrefixStripping : Prop := ∀ (op : String) (args : List String),
  args.isEmpty = false → (∀ a ∈ args, a.isEmpty = false) → IsPrefixCall op args →
  combineOpWithInputs op args = .ok (prefixLayout op args)

private theorem stripBrackets_stripOnce (s : String) (h : s.isEmpty = false) :
    stripBrackets s = .ok (stripOnce s) := by
  simp only [stripBrackets, stripOnce, h, Bool.false_eq_true, ↓reduceIte]
  by_cases hc : s.toList.head? == some '(' && s.toList.getLast? == some ')'
  · simp only [hc]; rfl
  · simp only [hc]; rfl

private theorem mapM_stripBrackets (args : List String)
    (h : ∀ a ∈ args, a.isEmpty = false) :
    args.mapM stripBrackets = .ok (args.map stripOnce) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      rw [List.mapM_cons, stripBrackets_stripOnce a (h a (by simp)),
        ih (fun y hy => h y (by simp [hy]))]
      simp only [bind, pure, Except.bind, Except.pure, List.map_cons]

/-- The infix-selection guard of `combineOpWithInputs` decides the layout. -/
private theorem combine_of_guardFalse (op : String) (args : List String)
    (hne : args.isEmpty = false) (hnn : ∀ a ∈ args, a.isEmpty = false)
    (h : (if args.length == 2 then
        match op.toList.head? with
        | none => Except.error JlError.boundsError
        | some c => Except.ok (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || op == "!=")
      else Except.ok false) = Except.ok false) :
    combineOpWithInputs op args = .ok (prefixLayout op args) := by
  simp only [combineOpWithInputs, prefixLayout, hne, Bool.false_eq_true, ↓reduceIte,
    mapM_stripBrackets args hnn, bind, pure, Except.bind, Except.pure]
  by_cases h2 : (args.length == 2) = true
  · rw [ite_eq_left h2] at h
    cases hh : op.toList.head? with
    | none => rw [hh] at h; simp at h
    | some c =>
        rw [hh] at h
        simp only [Except.ok.injEq] at h
        rw [ite_eq_left h2]
        simp only [h, Bool.false_eq_true, ↓reduceIte]
  · rw [ite_eq_right h2]

theorem prefixStripping : PrefixStripping := by
  intro op args hne hnn hpre
  refine combine_of_guardFalse op args hne hnn ?_
  rcases hpre with hL | ⟨c, hL2, hc, hfalse⟩
  · simp only [hL, Bool.false_eq_true, ↓reduceIte]
  · simp only [infixHeadChar] at hfalse
    rw [ite_eq_left hL2, hc]
    simp only [hfalse]

-- Witnesses: the hypotheses of `PrefixStripping` are satisfiable on both
-- disjuncts of `IsPrefixCall`, and the general theorem reproduces the
-- registered worked examples.
example : stripOnce "(x1 + x2)" = "x1 + x2" := rfl
example : stripOnce "((x))" = "(x)" := rfl
example : IsPrefixCall "twice" ["(x1 + x2)"] := Or.inl rfl
example : IsPrefixCall "min" ["(a + b)", "c"] := Or.inr ⟨'m', rfl, rfl, by decide⟩
example : combineOpWithInputs "twice" ["(x1 + x2)"] = .ok "twice(x1 + x2)" := by
  rw [prefixStripping "twice" ["(x1 + x2)"] rfl (by simp) (Or.inl rfl)]
  rfl
example : combineOpWithInputs "min" ["(a + b)", "c"] = .ok "min(a + b, c)" := by
  rw [prefixStripping "min" ["(a + b)", "c"] rfl (by simp) (Or.inr ⟨'m', rfl, rfl, by decide⟩)]
  rfl
example : combineOpWithInputs "h" ["(a)", "(b)", "c"] = .ok "h(a, b, c)" := by
  rw [prefixStripping "h" ["(a)", "(b)", "c"] rfl (by simp) (Or.inl rfl)]
  rfl

/-! ## General shared-subtree marker (`stringsparse-shared-marker`) -/

/-- Revisiting an address whose rendering is already the cache's first entry
returns that rendering wrapped in braces and leaves the cache exactly as it
was, for every render config, graph, positive fuel, address, cache, and
cached text (`src/Strings.jl:188-195`, `src/base.jl:77-121`). -/
def SharedMarker : Prop := ∀ (cfg : RenderConfig) (g : Graph Scalar) (fuel : Nat)
    (a : Addr) (cache : List (Addr × String)) (s : String),
  cache.find? (fun p => p.1 == a) = some (a, s) →
  rawGraph cfg g (fuel + 1) a cache = .ok ("{" ++ s ++ "}", cache)

theorem sharedMarker : SharedMarker := by
  intro cfg g fuel a cache s h
  simp only [rawGraph, h, pure, Except.pure]

-- Witness: for any config, graph, and address there is a cache whose first
-- entry matches, and the theorem then predicts the braced revisit.
example (cfg : RenderConfig) (g : Graph Scalar) (a : Addr) :
    rawGraph cfg g 5 a [(a, "x1")] = .ok ("{" ++ "x1" ++ "}", [(a, "x1")]) :=
  sharedMarker cfg g 4 a [(a, "x1")] "x1" (by simp [List.find?])

/-! ## General operator-name dispatch (`stringsparse-dispatch-names`) -/

/-- For every operator enum, degree, index, and pretty flag with a valid
positive lookup, dispatch returns the operator's pretty name exactly when
requested and its display name otherwise, independent of every other table
entry (`src/Strings.jl:7-42`). -/
def DispatchNames : Prop := ∀ (ops : Operators) (op : NamedOp) (degree idx : Nat)
    (pretty : Bool),
  0 < degree → 0 < idx → (ops[degree - 1]?.getD [])[idx - 1]? = some op →
  dispatchOpName (some ops) degree idx pretty = .ok (if pretty then op.pretty else op.display)

theorem dispatchNames : DispatchNames := by
  intro ops op degree idx pretty hdeg hidx hop
  have hd0 : degree ≠ 0 := Nat.ne_of_gt hdeg
  have hi0 : idx ≠ 0 := Nat.ne_of_gt hidx
  simp only [dispatchOpName]
  split
  · rename_i hg
    first
      | omega
      | simp [hd0, hi0] at hg
  · simp only [hop, bind, pure, Except.bind, Except.pure]

/-- Degree placeholder used when no operator enum is supplied
(`src/Strings.jl:7-19`); as in Julia, it does not depend on `pretty`. -/
def placeholderName (degree idx : Nat) : String :=
  (if degree == 1 then "unary_operator[" else if degree == 2
    then "binary_operator[" else "operator_deg" ++ toString degree ++ "[") ++ toString idx ++ "]"

example (degree idx : Nat) :
    dispatchOpName none degree idx false = .ok (placeholderName degree idx) := rfl
example : placeholderName 3 2 = "operator_deg3[2]" := rfl
example : placeholderName 1 4 = "unary_operator[4]" := rfl
example : broadcastName "+" = ".+" := rfl
example : broadcastName "cos" = "cos." := rfl

-- Witness: a one-operator table satisfies the positive valid lookup
-- hypotheses for both pretty settings.
def dnOps : Operators := [[{named "f" (fun _ => zero) with pretty := "F"}]]

example : dispatchOpName (some dnOps) 1 1 true = .ok "F" :=
  dispatchNames dnOps {named "f" (fun _ => zero) with pretty := "F"} 1 1 true
    (by decide) (by decide) (by rfl)

example : dispatchOpName (some dnOps) 1 1 false = .ok "f" :=
  dispatchNames dnOps {named "f" (fun _ => zero) with pretty := "F"} 1 1 false
    (by decide) (by decide) (by rfl)

end DynExpr.StringsParse.General
