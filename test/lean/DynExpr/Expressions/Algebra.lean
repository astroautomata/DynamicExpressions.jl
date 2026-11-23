import DynExpr.Expressions.Wrapper

namespace DynExpr.Expressions.Algebra

/-- Operator identities are tokens; aliasing can map any stored identity to any
user identity, src/ExpressionAlgebra.jl:38-55. Functions remain arbitrary in
OpEnum; this catalog models the additional identity comparisons, not values. -/
abbrev Catalog := List (List String)
structure Context where
  operators : Catalog
  typeId : Nat
  maxDegree : Nat := 2
  deriving DecidableEq
abbrev Expr := Expression JF Context
inductive Arg where
  | scalar (value : JF)
  | expr (expression : Expr)
instance : Inhabited Arg := ⟨.scalar (.fin 0)⟩

inductive Error where
  | julia (error : JlError)
  | missingOperator
  deriving DecidableEq, Repr

/-- src/ExpressionAlgebra.jl:55. -/
def declare_operator_alias (op : String) (_arity : Nat) := op
/-- src/ExpressionAlgebra.jl:57-59. -/
def allow_chaining (op : String) := op == "+" || op == "*"
/-- src/ExpressionAlgebra.jl:62-63. `findfirst(...)::Int` fails if the recursive
call has only scalar arguments. -/
def firstExpression : List Arg → Option Expr
  | [] => none
  | .expr ex :: _ => some ex
  | .scalar _ :: xs => firstExpression xs
/-- src/ExpressionAlgebra.jl:65. Julia requires identical concrete expression
types, including metadata NamedTuple field types, not only compatible values. -/
def sameType (exemplar : Expr) : Arg → Bool
  | .scalar _ => true
  | .expr ex => ex.metadata.typeId == exemplar.metadata.typeId
/-- src/ExpressionAlgebra.jl:15-24. Scalar values are promoted to the expression
scalar type and become constant leaves; expression contents are passed through.
Metadata of a promoted scalar is copied from the first expression. -/
def promoteArg (exemplar : Expr) : Arg → Expr
  | .scalar v => ⟨.const v, exemplar.metadata⟩
  | .expr ex => ex
/-- src/ExpressionAlgebra.jl:12-27. The result retains metadata from the first
argument after scalar promotion, and tree construction enforces max degree. -/
def insert_operator_index (op : Nat) (args : List Arg) (exemplar : Expr) : Except Error Expr :=
  let expressions := args.map (promoteArg exemplar)
  if expressions.length > exemplar.metadata.maxDegree then
    .error (.julia (.assertionError "length(children) <= max_degree(N)"))
  else if op > 255 || expressions.length > 255 then
    .error (.julia (.userError "InexactError: UInt8 conversion"))
  else match expressions with
    | [] => .error (.julia .boundsError)
    | first :: _ => .ok (with_contents first (.branch op (expressions.map get_contents)))
/-- One-based identity lookup; an absent degree slot gives `nothing`,
src/ExpressionAlgebra.jl:68-72. -/
def lookupIndex (alias : String → Nat → String) (op : String) (degree : Nat) (ops : Catalog) : Option Nat :=
  if degree = 0 then none
  else match ops[degree - 1]? with
    | none => none
    | some entries => (entries.findIdx? (fun e => alias e degree == op)).map (· + 1)
/-- Base `+` / `*` on two plain scalars (the only chaining operators,
src/ExpressionAlgebra.jl:57-59). -/
def scalarOp (op : String) (a b : JF) : JF := if op == "*" then a * b else a + b
/-- The argument values when no argument is an expression. -/
def scalarsOf : List Arg → Option (List JF)
  | [] => some []
  | .scalar v :: xs => (scalarsOf xs).map (v :: ·)
  | .expr _ :: _ => none
mutual
/-- src/ExpressionAlgebra.jl:61-88. Fuel bounds the recursion; it decreases
through chaining. A missing operator raises MissingOperatorError whether or not
its degree slot exists (src/ExpressionAlgebra.jl:80-86). -/
def applyAux (alias : String → Nat → String) (op : String) : Nat → List Arg → Except Error Expr
  | 0, _ => .error (.julia (.undefinedBehavior "insufficient recursion fuel"))
  | fuel + 1, args =>
    match firstExpression args with
    | none => .error (.julia (.userError "TypeError: findfirst result is not Int"))
    | some exemplar =>
      if !(args.all (sameType exemplar)) then
        .error (.julia (.assertionError "expression types must match"))
      else match lookupIndex alias op args.length exemplar.metadata.operators with
        | some idx => insert_operator_index idx args exemplar
        | none =>
          if allow_chaining op && args.length > 2 then do
            let inner ← callOp alias op fuel (args.take (args.length - 1))
            applyAux alias op fuel [inner, args.getLast!]
          else .error .missingOperator
/-- Julia dispatch of `op(args[1:(end - 1)]...)` at src/ExpressionAlgebra.jl:77
for `+` and `*`: all-scalar calls use Base arithmetic, folded left for three or
more arguments; calls of two or three arguments containing an expression hit the
declared expression methods (src/ExpressionAlgebra.jl:164-176), which forward to
apply_operator; longer calls fold left through Base's binary varargs method. -/
def callOp (alias : String → Nat → String) (op : String) : Nat → List Arg → Except Error Arg
  | 0, _ => .error (.julia (.undefinedBehavior "insufficient recursion fuel"))
  | fuel + 1, args =>
    match scalarsOf args with
    | some (v :: vs) => .ok (.scalar (vs.foldl (scalarOp op) v))
    | some [] => .error (.julia (.userError "MethodError: no zero-argument method"))
    | none =>
      if args.length ≤ 3 then (applyAux alias op fuel args).map .expr
      else match args with
        | a :: b :: rest => do
            let first ← callOp alias op fuel [a, b]
            rest.foldlM (fun acc x => callOp alias op fuel [acc, x]) first
        | _ => .error (.julia .boundsError)
end
/-- src/ExpressionAlgebra.jl:61-88. -/
def apply_operator (alias : String → Nat → String) (op : String) (args : List Arg) :=
  applyAux alias op ((2 * args.length + 1) + 1) args

/-- The four macro signature forms, src/ExpressionAlgebra.jl:110. -/
inductive WrapperKind where
  | abstractExpr | typedExpr | scalarT | number
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr
/-- Exact signature exclusions in src/ExpressionAlgebra.jl:113-131. -/
def allowedSignature (types : List WrapperKind) : Bool :=
  let bare := types.contains .abstractExpr
  let typed := types.contains .typedExpr
  let plain := types.contains .scalarT
  !(!(bare || typed) || (bare && typed) || (plain != typed))
/-- Iterators.product enumerates every argument wrapper choice,
src/ExpressionAlgebra.jl:100,110-144. -/
def signatures : Nat → List (List WrapperKind)
  | 0 => [[]]
  | n + 1 => [WrapperKind.abstractExpr, .typedExpr, .scalarT, .number].flatMap
      (fun k => (signatures n).map (k :: ·))
/-- src/ExpressionAlgebra.jl:99-147. Unary methods have exactly one expression
argument; higher arities retain the permitted signatures, whose bodies all
forward to apply_operator. -/
def declare_expression_operator (arity : Nat) :=
  if arity = 1 then [[WrapperKind.abstractExpr]]
  else (signatures arity).filter allowedSignature

private def ctx : Context := ⟨[[], ["+", "*"]], 0, 2⟩
private def x : Expr := ⟨.feature 1, ctx⟩
private def alias := declare_operator_alias

def indexProperty : Prop := ∀ (aliasFn : String → Nat → String) (op : String)
    (degree : Nat) (catalog : Catalog) (entries : List String) (i : Nat),
  0 < degree → catalog[degree - 1]? = some entries → entries.length ≤ 255 →
  (lookupIndex aliasFn op degree catalog = some (i + 1) ↔
    ∃ h : i < entries.length, aliasFn entries[i] degree = op ∧
      (∀ j (hj : j < i), aliasFn (entries[j]'(Nat.lt_trans hj h)) degree ≠ op) ∧
      i + 1 ≤ 255)
theorem index_proven : indexProperty := by
  intro aliasFn op degree catalog entries i hd hs hb
  simp only [lookupIndex, show degree ≠ 0 by omega, ↓reduceIte, hs]
  simp only [Option.map_eq_some_iff, Nat.add_right_cancel_iff, exists_eq_right]
  rw [List.findIdx?_eq_some_iff_getElem]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨h, hm, hf⟩
    exact ⟨h, hm, hf, by omega⟩
  · rintro ⟨h, hm, hf, _⟩
    exact ⟨h, hm, hf⟩

private theorem apply_lookup (aliasFn : String → Nat → String) (op : String)
    (args : List Arg) (ex : Expr) (idx fuel : Nat)
    (hfirst : firstExpression args = some ex)
    (htypes : args.all (sameType ex) = true)
    (hlookup : lookupIndex aliasFn op args.length ex.metadata.operators = some idx) :
    applyAux aliasFn op (fuel + 1) args = insert_operator_index idx args ex := by
  simp [applyAux, hfirst, htypes, hlookup]

private theorem apply_chain (aliasFn : String → Nat → String) (op : String)
    (args : List Arg) (ex : Expr) (fuel : Nat)
    (hfirst : firstExpression args = some ex)
    (htypes : args.all (sameType ex) = true)
    (hlookup : lookupIndex aliasFn op args.length ex.metadata.operators = none)
    (hchain : allow_chaining op = true) (hlen : 2 < args.length) :
    applyAux aliasFn op (fuel + 1) args =
      (callOp aliasFn op fuel (args.take (args.length - 1))).bind
        (fun inner => applyAux aliasFn op fuel [inner, args.getLast!]) := by
  simp [applyAux, hfirst, htypes, hlookup, hchain, hlen, bind]

private theorem scalarsOf_map (l : List JF) : scalarsOf (l.map Arg.scalar) = some l := by
  induction l with
  | nil => rfl
  | cons v vs ih => simp [scalarsOf, ih]

private theorem call_scalars (aliasFn : String → Nat → String) (op : String)
    (v : JF) (vs : List JF) (fuel : Nat) :
    callOp aliasFn op (fuel + 1) ((v :: vs).map Arg.scalar) =
      .ok (.scalar (vs.foldl (scalarOp op) v)) := by
  simp only [callOp, scalarsOf_map]

def promotionProperty : Prop := ∀ (aliasFn : String → Nat → String) (op : String)
    (ex : Expr) (value : JF) (idx : Nat),
  lookupIndex aliasFn op 2 ex.metadata.operators = some idx → idx ≤ 255 →
  2 ≤ ex.metadata.maxDegree →
  apply_operator aliasFn op [.scalar value, .expr ex] =
    .ok ⟨.branch idx [.const value, ex.tree], ex.metadata⟩ ∧
  apply_operator aliasFn op [.expr ex, .scalar value] =
    .ok ⟨.branch idx [ex.tree, .const value], ex.metadata⟩
theorem promotion_proven : promotionProperty := by
  intro aliasFn op ex value idx hl hi hd
  simp [apply_operator, applyAux, firstExpression, sameType, hl, insert_operator_index,
    promoteArg, with_contents, get_contents, get_metadata,
    show ¬idx > 255 by omega, show ¬2 > ex.metadata.maxDegree by omega]

def aliasProperty : Prop := ∀ (aliasFn : String → Nat → String) (op : String)
    (ex : Expr) (idx : Nat),
  lookupIndex aliasFn op 1 ex.metadata.operators = some idx → idx ≤ 255 →
  1 ≤ ex.metadata.maxDegree →
  apply_operator aliasFn op [.expr ex] = .ok ⟨.branch idx [ex.tree], ex.metadata⟩
theorem alias_proven : aliasProperty := by
  intro aliasFn op ex idx hl hi hd
  simp [apply_operator, applyAux, firstExpression, sameType, hl, insert_operator_index,
    promoteArg, with_contents, get_contents, get_metadata,
    show ¬idx > 255 by omega, show ¬1 > ex.metadata.maxDegree by omega]

def typesProperty : Prop := ∀ (aliasFn : String → Nat → String) (op : String)
    (args : List Arg) (ex other : Expr),
  firstExpression args = some ex → .expr other ∈ args →
  other.metadata.typeId ≠ ex.metadata.typeId →
  apply_operator aliasFn op args =
    .error (.julia (.assertionError "expression types must match"))
theorem types_proven : typesProperty := by
  intro aliasFn op args ex other hf hm hn
  have ht : args.all (sameType ex) = false := by
    cases h : args.all (sameType ex) with
    | false => rfl
    | true =>
      have := (List.all_eq_true.mp h) (.expr other) hm
      simp [sameType, hn] at this
  simp [apply_operator, applyAux, hf, ht]

def chainProperty : Prop := ∀ (aliasFn : String → Nat → String) (op : String)
    (left middle right : Arg) (ex : Expr) (idx : Nat),
  allow_chaining op = true → firstExpression [left, middle] = some ex →
  [left, middle, right].all (sameType ex) = true →
  lookupIndex aliasFn op 3 ex.metadata.operators = none →
  lookupIndex aliasFn op 2 ex.metadata.operators = some idx → idx ≤ 255 →
  2 ≤ ex.metadata.maxDegree →
  apply_operator aliasFn op [left, middle, right] =
    .ok ⟨.branch idx [.branch idx [(promoteArg ex left).tree, (promoteArg ex middle).tree],
      (promoteArg ex right).tree], ex.metadata⟩
theorem chain_proven : chainProperty := by
  intro aliasFn op left middle right ex idx hc hf ht h3 h2 hi hd
  cases left <;> cases middle <;> cases right <;>
    simp_all [apply_operator, applyAux, callOp, scalarsOf, firstExpression, sameType,
      insert_operator_index, promoteArg, with_contents, get_contents, get_metadata,
      bind, Except.bind, Except.map] <;>
    simp [firstExpression, sameType, Nat.not_lt.mpr hd, Nat.not_lt.mpr hi, h2]

private theorem mem_signatures (arity : Nat) (types : List WrapperKind) :
    types ∈ signatures arity ↔ types.length = arity := by
  induction arity generalizing types with
  | zero => simp [signatures, List.length_eq_zero_iff]
  | succ arity ih =>
    cases types with
    | nil => simp [signatures]
    | cons k ks =>
      cases k <;> simp [signatures, ih]

def signatureAdmissible (types : List WrapperKind) : Prop :=
  (.abstractExpr ∈ types ∨ .typedExpr ∈ types) ∧
  (.abstractExpr ∉ types ∨ .typedExpr ∉ types) ∧
  (.scalarT ∈ types ↔ .typedExpr ∈ types)

private theorem allowedSignature_spec (types : List WrapperKind) :
    allowedSignature types = true ↔ signatureAdmissible types := by
  by_cases hb : WrapperKind.abstractExpr ∈ types <;>
    by_cases ht : WrapperKind.typedExpr ∈ types <;>
    by_cases hp : WrapperKind.scalarT ∈ types <;>
    simp [allowedSignature, signatureAdmissible, hb, ht, hp]

def macroProperty : Prop := ∀ (arity : Nat) (types : List WrapperKind),
  (types ∈ declare_expression_operator arity ↔
    types.length = arity ∧
      (if arity = 1 then types = [.abstractExpr] else signatureAdmissible types)) ∧
  (types ∈ declare_expression_operator arity →
    .abstractExpr ∈ types ∨ .typedExpr ∈ types)
theorem macro_proven : macroProperty := by
  intro arity types
  have hm : types ∈ declare_expression_operator arity ↔
      types.length = arity ∧
        (if arity = 1 then types = [.abstractExpr] else signatureAdmissible types) := by
    by_cases h : arity = 1
    · subst arity
      simp [declare_expression_operator]
      intro he
      subst types
      rfl
    · simp [declare_expression_operator, h, mem_signatures, allowedSignature_spec]
  refine ⟨hm, ?_⟩
  intro ht
  obtain ⟨_, ha⟩ := hm.mp ht
  by_cases h : arity = 1
  · simp [h] at ha
    simp [ha]
  · simp only [h, ↓reduceIte] at ha
    exact ha.1

def missingPresentDegreeProperty : Prop := ∀ (aliasFn : String → Nat → String)
    (op : String) (args : List Arg) (ex : Expr),
  firstExpression args = some ex → args.all (sameType ex) = true →
  lookupIndex aliasFn op args.length ex.metadata.operators = none →
  (allow_chaining op = false ∨ args.length ≤ 2) →
  args.length ≤ ex.metadata.operators.length →
  apply_operator aliasFn op args = .error .missingOperator
theorem missingPresentDegree_proven : missingPresentDegreeProperty := by
  intro aliasFn op args ex hf ht hl hc hd
  rcases hc with hc | hc
  · simp [apply_operator, applyAux, hf, ht, hl, hc, hd]
  · simp [apply_operator, applyAux, hf, ht, hl, hd, show ¬args.length > 2 by omega]

/-- A missing nonchained operator raises MissingOperatorError even when its
degree exceeds the enum's stored degree count (fixed in PR #253). -/
def missingDegreeProperty : Prop := ∀ (aliasFn : String → Nat → String)
    (op : String) (args : List Arg) (ex : Expr),
  firstExpression args = some ex → args.all (sameType ex) = true →
  lookupIndex aliasFn op args.length ex.metadata.operators = none →
  (allow_chaining op = false ∨ args.length ≤ 2) →
  apply_operator aliasFn op args = .error .missingOperator
theorem missingDegree_proven : missingDegreeProperty := by
  intro aliasFn op args ex hf ht hl hc
  rcases hc with hc | hc
  · simp [apply_operator, applyAux, hf, ht, hl, hc]
  · simp [apply_operator, applyAux, hf, ht, hl, show ¬args.length > 2 by omega]
example : firstExpression [.expr x, .scalar (.fin 0), .scalar (.fin 1)] = some x ∧
    [.expr x, .scalar (.fin 0), .scalar (.fin 1)].all (sameType x) = true ∧
    lookupIndex alias "clamp" 3 ctx.operators = none ∧
    (allow_chaining "clamp" = false ∨ (3 : Nat) ≤ 2) := ⟨rfl, rfl, rfl, Or.inl rfl⟩

/-- Binary plus and multiplication support any nonempty scalar prefix followed
by one expression, including recursive chaining (fixed in PR #254). -/
def trailingExpressionProperty : Prop := ∀ (aliasFn : String → Nat → String)
    (op : String) (scalars : List JF) (ex : Expr) (idx : Nat),
  scalars ≠ [] → allow_chaining op = true →
  lookupIndex aliasFn op 2 ex.metadata.operators = some idx → idx ≤ 255 →
  2 ≤ ex.metadata.maxDegree →
  (∀ degree, 2 < degree → lookupIndex aliasFn op degree ex.metadata.operators = none) →
  ∃ out, apply_operator aliasFn op (scalars.map Arg.scalar ++ [.expr ex]) = .ok out
theorem trailingExpression_proven : trailingExpressionProperty := by
  intro aliasFn op scalars ex idx hne hc hl hi hd hnone
  have hfirst : ∀ l : List JF, firstExpression (l.map Arg.scalar ++ [Arg.expr ex]) = some ex := by
    intro l
    induction l with
    | nil => rfl
    | cons v vs ih => simpa [firstExpression] using ih
  have hall : ∀ l : List JF, (l.map Arg.scalar ++ [Arg.expr ex]).all (sameType ex) = true := by
    intro l
    simp [sameType]
  have hbin : ∀ (v : JF) (fuel : Nat),
      ∃ out, applyAux aliasFn op (fuel + 1) [Arg.scalar v, Arg.expr ex] = .ok out := by
    intro v fuel
    have hlook : lookupIndex aliasFn op ([v].map Arg.scalar ++ [Arg.expr ex]).length
        ex.metadata.operators = some idx := by simpa using hl
    have h := apply_lookup aliasFn op _ ex idx fuel (hfirst [v]) (hall [v]) hlook
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
    rw [h]
    simp [insert_operator_index, show ¬ idx > 255 by omega,
      show ¬ 2 > ex.metadata.maxDegree by omega]
  have htake : ∀ l : List Arg, (l ++ [Arg.expr ex]).take ((l ++ [Arg.expr ex]).length - 1) = l := by
    intro l
    simp
  have hlast : ∀ l : List Arg, (l ++ [Arg.expr ex]).getLast! = Arg.expr ex := by
    intro l
    simp
  cases scalars with
  | nil => exact absurd rfl hne
  | cons v vs =>
    cases vs with
    | nil => exact hbin v _
    | cons w ws =>
      have hlen : ((v :: w :: ws).map Arg.scalar ++ [Arg.expr ex]).length = ws.length + 3 := by
        simp
      have hl3 : lookupIndex aliasFn op ((v :: w :: ws).map Arg.scalar ++ [Arg.expr ex]).length
          ex.metadata.operators = none := by
        rw [hlen]; exact hnone _ (by omega)
      obtain ⟨out, hout⟩ := hbin ((w :: ws).foldl (scalarOp op) v) (2 * (ws.length + 3))
      refine ⟨out, ?_⟩
      unfold apply_operator
      rw [apply_chain aliasFn op _ ex _ (hfirst _) (hall _) hl3 hc (by rw [hlen]; omega),
        htake, hlast, hlen, call_scalars]
      exact hout
example : [JF.fin 1, .fin 2] ≠ [] ∧ allow_chaining "+" = true ∧
    lookupIndex alias "+" 2 x.metadata.operators = some 1 ∧ 1 ≤ 255 ∧
    2 ≤ x.metadata.maxDegree ∧
    (∀ degree, 2 < degree → lookupIndex alias "+" degree x.metadata.operators = none) := by
  refine ⟨by simp, rfl, rfl, by decide, by decide, ?_⟩
  intro degree hd
  have hslot : ctx.operators[degree - 1]? = none :=
    List.getElem?_eq_none (by simp [ctx]; omega)
  simp [x, lookupIndex, show degree ≠ 0 by omega, hslot]

/-- Construction preserves the ordered children and metadata for arbitrary
nonempty argument lists fitting the node's degree and index fields. -/
def constructionProperty : Prop := ∀ (aliasFn : String → Nat → String)
    (op : String) (args : List Arg) (ex : Expr) (idx : Nat),
  firstExpression args = some ex → args.all (sameType ex) = true →
  lookupIndex aliasFn op args.length ex.metadata.operators = some idx → idx ≤ 255 →
  args.length ≤ 255 → args.length ≤ ex.metadata.maxDegree →
  ∀ first rest, args = first :: rest →
  apply_operator aliasFn op args =
    .ok ⟨.branch idx ((args.map (promoteArg ex)).map get_contents),
      (promoteArg ex first).metadata⟩
theorem construction_proven : constructionProperty := by
  intro aliasFn op args ex idx hf ht hl hi ha hd first rest he
  rw [apply_operator, apply_lookup aliasFn op args ex idx (2 * args.length + 1) hf ht hl]
  subst args
  simp [insert_operator_index, with_contents, get_metadata,
    show ¬idx > 255 by omega, show ¬rest.length + 1 > 255 by simpa using ha,
    show ¬rest.length + 1 > ex.metadata.maxDegree by simpa using hd]

example : 0 < 2 ∧ [[], ["+"]][2 - 1]? = some ["+"] ∧ ["+"].length ≤ 255 := by decide
example : lookupIndex alias "+" 2 x.metadata.operators = some 1 ∧ 1 ≤ 255 ∧
    2 ≤ x.metadata.maxDegree := ⟨rfl, by decide, by decide⟩
example : let unary : Expr := ⟨.feature 1, ⟨[["*"]], 0, 2⟩⟩
    lookupIndex alias "*" 1 unary.metadata.operators = some 1 ∧ 1 ≤ 255 ∧
      1 ≤ unary.metadata.maxDegree := ⟨rfl, by decide, by decide⟩
example : firstExpression [.expr x, .expr ⟨.feature 2, {ctx with typeId := 1}⟩] = some x ∧
    Arg.expr ⟨.feature 2, {ctx with typeId := 1}⟩ ∈ [Arg.expr x, Arg.expr ⟨.feature 2, {ctx with typeId := 1}⟩] ∧
    1 ≠ x.metadata.typeId := ⟨rfl, by simp, by decide⟩
example : allow_chaining "+" = true ∧ firstExpression [.expr x, .scalar (.fin 2)] = some x ∧
    [.expr x, .scalar (.fin 2), .expr x].all (sameType x) = true ∧
    lookupIndex alias "+" 3 ctx.operators = none ∧
    lookupIndex alias "+" 2 ctx.operators = some 1 ∧ 1 ≤ 255 ∧ 2 ≤ ctx.maxDegree :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
example : firstExpression [.expr x] = some x ∧ [.expr x].all (sameType x) = true ∧
    lookupIndex alias "sin" 1 ctx.operators = none ∧
    (allow_chaining "sin" = false ∨ (1 : Nat) ≤ 2) ∧ 1 ≤ ctx.operators.length :=
  ⟨rfl, rfl, rfl, Or.inl rfl, by decide⟩
example : firstExpression [.expr x, .expr x] = some x ∧
    [.expr x, .expr x].all (sameType x) = true ∧
    lookupIndex alias "+" 2 ctx.operators = some 1 ∧ 1 ≤ 255 ∧
    (2 : Nat) ≤ 255 ∧ 2 ≤ ctx.maxDegree ∧
    [Arg.expr x, Arg.expr x] = Arg.expr x :: [Arg.expr x] :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, rfl⟩

end DynExpr.Expressions.Algebra
