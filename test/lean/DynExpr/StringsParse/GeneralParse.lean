import DynExpr.StringsParse.Properties

namespace DynExpr.StringsParse.General

set_option maxRecDepth 1000
set_option maxHeartbeats 400000

/-- Operator indices fit the Julia node field (`src/Parse.jl:426-449`). -/
def TableValid (ops : Operators) : Prop := ∀ os ∈ ops, os.length ≤ 255

/-- Function resolution, before recursive child parsing (`src/Parse.jl:394-409`). -/
def Resolved (cfg : ParseConfig) (name identity : String) (arity : Nat) : Prop :=
  (match cfg.env.builtin name with
    | some id => .ok id
    | none => findOperatorByName cfg.operators name arity) = (Except.ok identity : Jl String)

/-- No successful binary chaining route, and no out-of-bounds binary table
access (`src/Parse.jl:451-504`). -/
def NoChain (cfg : ParseConfig) (identity : String) (args : List Surface) : Prop :=
  (args.length > 2 ∧ ["+", "-", "*"].contains identity = true) →
    2 ≤ cfg.operators.length ∧ findOpIndex cfg.operators identity 2 = none

private theorem findPrefix {α : Type} (p : α → Bool) (before suffix : List α)
    (a : α) (hprefix : ∀ x ∈ before, p x = false) (ha : p a = true) :
    (before ++ a :: suffix).find? p = some a := by
  induction before with
  | nil => simp [ha]
  | cons x xs ih =>
    have hx := hprefix x (by simp)
    have hxs : ∀ y ∈ xs, p y = false := by
      intro y hy
      exact hprefix y (by simp [hy])
    simp [hx, ih hxs]

/-- First identity-or-alias match at the requested degree, independently of
all other degree tables (`src/Parse.jl:433-440`). The prefix describes the
operators preceding the selected operator, rather than assuming the lookup
result. Name resolution compares `nameof`, or the `get_op_name` spelling of a
broadcast callable, and rejects missing arities and ambiguity
(`src/Parse.jl:304-345`). -/
private def LookupAndName : Prop :=
  (∀ (ops : Operators) (identity : String) (degree index : Nat) (op : NamedOp)
      (before suffix : List (NamedOp × Nat)),
    TableValid ops → 0 < degree →
    ((ops[degree - 1]?.getD []).zipIdx) = before ++ (op, index) :: suffix →
    (∀ p ∈ before, (p.1.identity == identity || p.1.alias == identity) = false) →
    (op.identity = identity ∨ op.alias = identity) →
    findOpIndex ops identity degree = some (index + 1)) ∧
  (∀ (ops : Operators) (name : String) (degree : Nat), TableValid ops →
    let found := (ops.zipIdx).flatMap (fun (os, arity) =>
      (os.filter (fun op => op.parseName == name)).map (fun op => (op.identity, arity + 1)))
    found ≠ [] →
    (∀ identity arity, found.filter (fun p => p.2 == degree) = [(identity, arity)] →
      findOperatorByName ops name degree = .ok identity) ∧
    (found.filter (fun p => p.2 == degree) = [] →
      findOperatorByName ops name degree = .error (.argumentError "Operator found but not with this arity.")) ∧
    (∀ a b tail, found.filter (fun p => p.2 == degree) = a :: b :: tail →
      findOperatorByName ops name degree = .error (.argumentError "Ambiguous operator with this arity.")))

private theorem lookupAndName : LookupAndName := by
  constructor
  · intro ops identity degree index op before suffix _ hdegree htable hprefix hmatch
    have hzero : degree ≠ 0 := Nat.ne_of_gt hdegree
    have hm : (op.identity == identity || op.alias == identity) = true := by
      rcases hmatch with h | h <;> simp [h]
    have hf := findPrefix (fun p : NamedOp × Nat =>
      p.1.identity == identity || p.1.alias == identity) before suffix (op, index) hprefix hm
    simp [findOpIndex, hzero, htable, hf]
  · intro ops name degree _ found hnonempty
    have he : found.isEmpty = false := by
      cases hf : found with
      | nil => exact False.elim (hnonempty hf)
      | cons a as => rfl
    constructor
    · intro identity arity h
      unfold findOperatorByName
      change (if found.isEmpty then _ else match found.filter (fun p => p.2 == degree) with
        | [(id, _)] => Except.ok id
        | [] => .error (JlError.argumentError "Operator found but not with this arity.")
        | _ => .error (JlError.argumentError "Ambiguous operator with this arity.")) = _
      simp only [he, Bool.false_eq_true, ↓reduceIte, h]
    constructor
    · intro h
      unfold findOperatorByName
      change (if found.isEmpty then _ else match found.filter (fun p => p.2 == degree) with
        | [(id, _)] => Except.ok id
        | [] => .error (JlError.argumentError "Operator found but not with this arity.")
        | _ => .error (JlError.argumentError "Ambiguous operator with this arity.")) = _
      simp only [he, Bool.false_eq_true, ↓reduceIte, h]
    · intro a b tail h
      unfold findOperatorByName
      change (if found.isEmpty then _ else match found.filter (fun p => p.2 == degree) with
        | [(id, _)] => Except.ok id
        | [] => .error (JlError.argumentError "Operator found but not with this arity.")
        | _ => .error (JlError.argumentError "Ambiguous operator with this arity.")) = _
      simp only [he, Bool.false_eq_true, ↓reduceIte, h]

private theorem findNone {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x ∈ xs, p x = false) : xs.find? p = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ xs, p y = false := by
      intro y hy
      exact h y (by simp [hy])
    simp [hx, ih ht]

/-- Lookup respects exact degree and the first identity/alias match; unique
names resolve at their requested arity, wrong arities and ambiguity fail,
and a degree without any identity/alias match returns no index
(`src/Parse.jl:303-343,426-430`). -/
def ExactArityAlias : Prop := LookupAndName ∧
  (∀ (ops : Operators) (identity : String) (degree : Nat), TableValid ops →
    (∀ p ∈ ((ops[degree - 1]?.getD []).zipIdx),
      (p.1.identity == identity || p.1.alias == identity) = false) →
    findOpIndex ops identity degree = none)

theorem exactArityAlias : ExactArityAlias := by
  refine ⟨lookupAndName, ?_⟩
  intro ops identity degree _ h
  have hf := findNone (fun p : NamedOp × Nat =>
    p.1.identity == identity || p.1.alias == identity) _ h
  by_cases hz : degree = 0
  · simp [findOpIndex, hz]
  · simp [findOpIndex, hz, hf]

example : let ops := [[{named "custom" (fun _ => zero) with alias := "+"}], []]
    TableValid ops ∧ ∀ p ∈ ((ops[2 - 1]?.getD []).zipIdx),
      (p.1.identity == "+" || p.1.alias == "+") = false := by
  simp [TableValid, named]



/-- Exact-arity construction precedes every fallback, including evaluate_on
and binary chaining (`src/Parse.jl:426-449`). Child success is a recursive
prerequisite; the parent parse result is the conclusion. -/
theorem parseExact (cfg : ParseConfig) (fuel : Nat) (name identity : String)
    (args : List Surface) (children : List ParsedNode) (idx : Nat)
    (hr : Resolved cfg name identity args.length) (hne : args.isEmpty = false)
    (hi : findOpIndex cfg.operators identity args.length = some idx)
    (hc : args.mapM (parseCore cfg fuel) = .ok children) :
    parseCore cfg (fuel + 1) (.call name args) =
      .ok ⟨cfg.nodeType, .branch idx (children.map ParsedNode.tree)⟩ := by
  unfold Resolved at hr
  cases hb : cfg.env.builtin name <;> simp only [hb, Except.ok.injEq] at hr
  all_goals subst_vars
  all_goals simp only [parseCore, hb]
  all_goals try rw [hr]
  all_goals simp only [bind, pure, Except.bind, Except.pure, hne, Bool.false_eq_true, ↓reduceIte, hi, hc]

/-- Binary chaining is the left fold over all parsed operands, for each of
+, -, and * (`src/Parse.jl:451-504`). Exact n-ary operators are absent. -/
def NaryChain : Prop := ∀ (cfg : ParseConfig) (fuel : Nat) (name identity : String)
    (args : List Surface) (first second : ParsedNode) (rest : List ParsedNode) (idx : Nat),
  TableValid cfg.operators → Resolved cfg name identity args.length →
  2 < args.length → ["+", "-", "*"].contains identity = true →
  2 ≤ cfg.operators.length →
  findOpIndex cfg.operators identity args.length = none →
  findOpIndex cfg.operators identity 2 = some idx →
  args.mapM (parseCore cfg fuel) = .ok (first :: second :: rest) →
  parseCore cfg (fuel + 1) (.call name args) = .ok ⟨cfg.nodeType,
    (rest.map ParsedNode.tree).foldl (fun acc tree => .branch idx [acc, tree])
      (.branch idx [first.tree, second.tree])⟩

theorem naryChain : NaryChain := by
  intro cfg fuel name identity args first second rest idx _ hr hlen hop htables hexact hbinary hc
  have hne : args.isEmpty = false := by
    cases args with
    | nil => simp at hlen
    | cons a as => rfl
  have ht : ¬cfg.operators.length < 2 := Nat.not_lt.mpr htables
  unfold Resolved at hr
  cases hb : cfg.env.builtin name <;> simp only [hb, Except.ok.injEq] at hr
  all_goals subst_vars
  all_goals simp only [parseCore, hb]
  all_goals try rw [hr]
  all_goals simp only [bind, pure, Except.bind, Except.pure, hne, Bool.false_eq_true, ↓reduceIte, hexact, hlen, hop, decide_true, Bool.true_and, ht, hbinary, hc]
  all_goals simp [chain]

private theorem externalRoute (cfg : ParseConfig) (fuel : Nat) (name identity : String)
    (args : List Surface) (hr : Resolved cfg name identity args.length)
    (hne : args.isEmpty = false) (hi : findOpIndex cfg.operators identity args.length = none)
    (hn : NoChain cfg identity args) :
    parseCore cfg (fuel + 1) (.call name args) =
      (if cfg.evaluateOn.contains identity then do
        let out ← cfg.env.external identity (← args.mapM (parseCore cfg fuel))
        pure {out with tag := cfg.nodeType}
      else .error (.argumentError "Unrecognized operator; pass external functions to evaluate_on.")) := by
  unfold Resolved at hr
  cases hb : cfg.env.builtin name <;> simp only [hb, Except.ok.injEq] at hr
  all_goals try (rename_i val; subst val)
  all_goals simp only [parseCore, hb]
  all_goals try rw [hr]
  all_goals simp only [bind, pure, Except.bind, Except.pure, hne, Bool.false_eq_true, ↓reduceIte, hi]
  all_goals
    by_cases hlen : args.length > 2
    · by_cases hop : ["+", "-", "*"].contains identity = true
      · obtain ⟨htables, hbinary⟩ := hn ⟨hlen, hop⟩
        have ht : ¬cfg.operators.length < 2 := Nat.not_lt.mpr htables
        simp only [hlen, decide_true, hop, Bool.true_and, ↓reduceIte, ht, hbinary]
        rfl
      · simp only [hlen, decide_true, Bool.true_and, hop, Bool.false_eq_true, ↓reduceIte]
        rfl
    · simp only [hlen, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rfl

/-- External calls require opt-in after operator and chaining routes fail;
all child nodes and compatible callback outputs are arbitrary
(`src/Parse.jl:506-544`). -/
def ExternalOptIn : Prop := ∀ (cfg : ParseConfig) (fuel : Nat) (name identity : String)
    (args : List Surface) (children : List ParsedNode) (out : ParsedNode),
  TableValid cfg.operators → Resolved cfg name identity args.length →
  args.isEmpty = false → findOpIndex cfg.operators identity args.length = none →
  NoChain cfg identity args → args.mapM (parseCore cfg fuel) = .ok children →
  cfg.env.external identity children = .ok out →
  (cfg.evaluateOn.contains identity = true →
    parseCore cfg (fuel + 1) (.call name args) = .ok {out with tag := cfg.nodeType}) ∧
  (cfg.evaluateOn.contains identity = false →
    parseCore cfg (fuel + 1) (.call name args) =
      .error (.argumentError "Unrecognized operator; pass external functions to evaluate_on."))

theorem externalOptIn : ExternalOptIn := by
  intro cfg fuel name identity args children out _ hr hne hi hn hc hout
  rw [externalRoute cfg fuel name identity args hr hne hi hn]
  constructor <;> intro h <;> simp only [h, Bool.false_eq_true, ↓reduceIte, hc, bind, pure, Except.bind, Except.pure, hout]

/-- Constructor routes convert arbitrary child/callback families to the
requested family (`src/Parse.jl:433-448,506-522,547-558`), and a direct node
leaf is converted to it as well (`src/Parse.jl:594-595`). -/
def ConstructorFamilyConversion : Prop :=
  (∀ (cfg : ParseConfig) (fuel : Nat) (name identity : String)
      (args : List Surface) (children : List ParsedNode) (idx : Nat),
    TableValid cfg.operators → Resolved cfg name identity args.length → args.isEmpty = false →
    findOpIndex cfg.operators identity args.length = some idx →
    args.mapM (parseCore cfg fuel) = .ok children →
    (parseCore cfg (fuel + 1) (.call name args)).toOption.map ParsedNode.tag = some cfg.nodeType) ∧
  (∀ (cfg : ParseConfig) (fuel : Nat) (name identity : String)
      (args : List Surface) (children : List ParsedNode) (out : ParsedNode),
    TableValid cfg.operators → Resolved cfg name identity args.length → args.isEmpty = false →
    findOpIndex cfg.operators identity args.length = none → NoChain cfg identity args →
    args.mapM (parseCore cfg fuel) = .ok children → cfg.env.external identity children = .ok out →
    cfg.evaluateOn.contains identity = true →
    (parseCore cfg (fuel + 1) (.call name args)).toOption.map ParsedNode.tag = some cfg.nodeType) ∧
  (∀ (cfg : ParseConfig) (tag : String) (tree : Tree Scalar),
    parseLeaf cfg (.node tag tree) = .ok ⟨cfg.nodeType, tree⟩)

theorem constructorFamilyConversion : ConstructorFamilyConversion := by
  constructor
  · intro cfg fuel name identity args children idx _ hr hne hi hc
    rw [parseExact cfg fuel name identity args children idx hr hne hi hc]
    rfl
  constructor
  · intro cfg fuel name identity args children out ht hr hne hi hn hc ho he
    rw [(externalOptIn cfg fuel name identity args children out ht hr hne hi hn hc ho).1 he]
    rfl
  · intro cfg tag tree
    rfl

/-- For every n-ary arithmetic call with both n-ary and binary operators,
the n-ary operator wins, regardless of aliases, operand trees, operator
implementations, or external opt-in (`src/Parse.jl:426-504`). -/
def VariadicArityPriority : Prop := ∀ (cfg : ParseConfig) (fuel : Nat)
    (name identity : String) (args : List Surface) (children : List ParsedNode)
    (naryIdx binaryIdx : Nat),
  TableValid cfg.operators → Resolved cfg name identity args.length →
  2 < args.length → ["+", "-", "*"].contains identity = true →
  findOpIndex cfg.operators identity args.length = some naryIdx →
  findOpIndex cfg.operators identity 2 = some binaryIdx →
  args.mapM (parseCore cfg fuel) = .ok children →
  parseCore cfg (fuel + 1) (.call name args) =
    .ok ⟨cfg.nodeType, .branch naryIdx (children.map ParsedNode.tree)⟩

theorem variadicArityPriority : VariadicArityPriority := by
  intro cfg fuel name identity args children naryIdx binaryIdx _ hr hlen _ hi _ hc
  have hne : args.isEmpty = false := by
    cases args with
    | nil => simp at hlen
    | cons a as => rfl
  exact parseExact cfg fuel name identity args children naryIdx hr hne hi hc

/-- Witnesses exhibit the prerequisites separately from parent parse results. -/
private def operandArgs : List Surface :=
  [.node "Node" (.feature 1), .node "Node" (.feature 2), .node "Node" (.feature 3)]
private def operandNodes : List ParsedNode :=
  [⟨"GraphNode", .feature 1⟩, ⟨"GraphNode", .feature 2⟩, ⟨"GraphNode", .feature 3⟩]
private def binaryCfg : ParseConfig :=
  { operators := [[], [named "-" (fun _ => zero)]], nodeType := "GraphNode" }
private def variadicCfg : ParseConfig :=
  { binaryCfg with operators := [[], [named "-" (fun _ => zero)],
      [named "-" (fun _ => zero)]] }
private def externalCfg : ParseConfig :=
  { nodeType := "GraphNode", evaluateOn := ["external"],
    env := { builtin := (fun _ => some "external"),
             external := (fun _ _ => .ok ⟨"Node", .feature 8⟩) } }

example : let op := {named "custom" (fun _ => zero) with alias := "+"}
    let other := named "other" (fun _ => zero)
    let ops := [[other, op], []]
    TableValid ops ∧ 0 < (1 : Nat) ∧
      ((ops[1 - 1]?.getD []).zipIdx) = [(other, 0)] ++ (op, 1) :: [] ∧
      (∀ p ∈ [(other, 0)], (p.1.identity == "+" || p.1.alias == "+") = false) ∧
      op.alias = "+" := by
  simp [TableValid, named]

example : let ops := [[named "f" (fun _ => zero)], [named "f" (fun _ => zero)]]
    let found := (ops.zipIdx).flatMap (fun (os, arity) =>
      (os.filter (fun op => op.name == "f")).map (fun op => (op.identity, arity + 1)))
    TableValid ops ∧ found ≠ [] ∧
      found.filter (fun p => p.2 == 2) = [("f", 2)] ∧
      found.filter (fun p => p.2 == 3) = [] := by
  simp [TableValid, named, List.zipIdx_cons]

example : let ops := [[named "f" (fun _ => zero), named "f" (fun _ => zero)]]
    let found := (ops.zipIdx).flatMap (fun (os, arity) =>
      (os.filter (fun op => op.name == "f")).map (fun op => (op.identity, arity + 1)))
    TableValid ops ∧ found ≠ [] ∧
      found.filter (fun p => p.2 == 1) = [("f", 1), ("f", 1)] := by
  simp [TableValid, named, List.zipIdx_cons]

example : TableValid binaryCfg.operators ∧ Resolved binaryCfg "-" "-" operandArgs.length ∧
    2 < operandArgs.length ∧ ["+", "-", "*"].contains "-" = true ∧
    2 ≤ binaryCfg.operators.length ∧
    findOpIndex binaryCfg.operators "-" operandArgs.length = none ∧
    findOpIndex binaryCfg.operators "-" 2 = some 1 ∧
    operandArgs.mapM (parseCore binaryCfg 1) = .ok operandNodes := by
  constructor
  · simp [TableValid, binaryCfg]
  exact ⟨rfl, by decide, rfl, by decide, rfl, rfl, rfl⟩

example : TableValid variadicCfg.operators ∧ Resolved variadicCfg "-" "-" operandArgs.length ∧
    2 < operandArgs.length ∧ ["+", "-", "*"].contains "-" = true ∧
    operandArgs.isEmpty = false ∧
    findOpIndex variadicCfg.operators "-" operandArgs.length = some 1 ∧
    findOpIndex variadicCfg.operators "-" 2 = some 1 ∧
    operandArgs.mapM (parseCore variadicCfg 1) = .ok operandNodes ∧
    variadicCfg.nodeType = "GraphNode" := by
  constructor
  · simp [TableValid, variadicCfg]
  exact ⟨rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩

example : TableValid externalCfg.operators ∧ Resolved externalCfg "external" "external" operandArgs.length ∧
    operandArgs.isEmpty = false ∧ findOpIndex externalCfg.operators "external" operandArgs.length = none ∧
    NoChain externalCfg "external" operandArgs ∧
    operandArgs.mapM (parseCore externalCfg 1) = .ok operandNodes ∧
    externalCfg.env.external "external" operandNodes = .ok ⟨"Node", .feature 8⟩ ∧
    externalCfg.evaluateOn.contains "external" = true ∧
    ({externalCfg with evaluateOn := []} : ParseConfig).evaluateOn.contains "external" = false := by
  constructor
  · simp [TableValid, externalCfg]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp [NoChain]
  exact ⟨rfl, rfl, rfl, rfl⟩

mutual
  /-- A finite input grammar and its expected tree/family, independent of
  parser success. Function resolution and operator indices are checked before
  construction (`src/Parse.jl:303-343,394-522,560-599`). -/
  inductive ParseGrammar (cfg : ParseConfig) : Surface → ParsedNode → Prop where
    | literal (v : Scalar) : ParseGrammar cfg (.literal v) ⟨cfg.nodeType, .const v⟩
    | symbol (name : String) (index : Nat) (found : variableIndex name cfg.names = some index) :
        ParseGrammar cfg (.symbol name) ⟨cfg.nodeType, .feature index⟩
    | node (tag : String) (tree : Tree Scalar) :
        ParseGrammar cfg (.node tag tree) ⟨cfg.nodeType, tree⟩
    | exact (name identity : String) (args : List Surface) (children : List ParsedNode) (idx : Nat)
        (resolved : Resolved cfg name identity args.length) (nonempty : args.isEmpty = false)
        (operator : findOpIndex cfg.operators identity args.length = some idx)
        (operands : ForestGrammar cfg args children) :
        ParseGrammar cfg (.call name args) ⟨cfg.nodeType, .branch idx (children.map ParsedNode.tree)⟩
    | nary (name identity : String) (args : List Surface)
        (first second : ParsedNode) (rest : List ParsedNode) (idx : Nat)
        (resolved : Resolved cfg name identity args.length) (arity : 2 < args.length)
        (arithmetic : ["+", "-", "*"].contains identity = true)
        (tables : 2 ≤ cfg.operators.length)
        (noExact : findOpIndex cfg.operators identity args.length = none)
        (binary : findOpIndex cfg.operators identity 2 = some idx)
        (operands : ForestGrammar cfg args (first :: second :: rest)) :
        ParseGrammar cfg (.call name args) ⟨cfg.nodeType,
          (rest.map ParsedNode.tree).foldl (fun acc tree => .branch idx [acc, tree])
            (.branch idx [first.tree, second.tree])⟩
    | external (name identity : String) (args : List Surface)
        (children : List ParsedNode) (out : ParsedNode)
        (resolved : Resolved cfg name identity args.length) (nonempty : args.isEmpty = false)
        (noExact : findOpIndex cfg.operators identity args.length = none)
        (noChain : NoChain cfg identity args) (enabled : cfg.evaluateOn.contains identity = true)
        (operands : ForestGrammar cfg args children)
        (callback : cfg.env.external identity children = .ok out) :
        ParseGrammar cfg (.call name args) {out with tag := cfg.nodeType}
  inductive ForestGrammar (cfg : ParseConfig) : List Surface → List ParsedNode → Prop where
    | nil : ForestGrammar cfg [] []
    | cons {arg : Surface} {node : ParsedNode} {args : List Surface} {nodes : List ParsedNode}
        (head : ParseGrammar cfg arg node) (tail : ForestGrammar cfg args nodes) :
        ForestGrammar cfg (arg :: args) (node :: nodes)
end

private theorem forestSuccessAt (cfg : ParseConfig) (fuel : Nat)
    (one : ∀ ex node, ParseGrammar cfg ex node → surfaceDepth ex < fuel →
      parseCore cfg fuel ex = .ok node)
    (args : List Surface) (nodes : List ParsedNode)
    (grammar : ForestGrammar cfg args nodes) (depth : argsDepth args < fuel) :
    args.mapM (parseCore cfg fuel) = .ok nodes := by
  induction args generalizing nodes with
  | nil => cases grammar; rfl
  | cons arg args ih =>
    cases grammar with
    | cons head tail =>
      have hd : surfaceDepth arg < fuel := by
        simp only [argsDepth] at depth
        omega
      have ht : argsDepth args < fuel := by
        simp only [argsDepth] at depth
        omega
      simp only [List.mapM_cons, one _ _ head hd, ih _ tail ht, bind, pure, Except.bind, Except.pure]

private theorem parseSuccessAt (fuel : Nat) (cfg : ParseConfig) (ex : Surface) (node : ParsedNode)
    (tables : TableValid cfg.operators) (grammar : ParseGrammar cfg ex node)
    (depth : surfaceDepth ex < fuel) : parseCore cfg fuel ex = .ok node := by
  induction fuel generalizing ex node with
  | zero => omega
  | succ fuel ih =>
    cases grammar with
    | literal v => rfl
    | symbol name index found => simp only [parseCore, parseLeaf, found]
    | node tag tree => rfl
    | exact name identity args children idx resolved nonempty operator operands =>
      have hd : argsDepth args < fuel := by
        simp only [surfaceDepth] at depth
        omega
      exact parseExact cfg fuel name identity args children idx resolved nonempty operator
        (forestSuccessAt cfg fuel (fun ex node hg hd => ih ex node hg hd) args children operands hd)
    | nary name identity args first second rest idx resolved arity arithmetic ht noExact binary operands =>
      have hd : argsDepth args < fuel := by
        simp only [surfaceDepth] at depth
        omega
      exact naryChain cfg fuel name identity args first second rest idx tables resolved arity arithmetic ht
        noExact binary (forestSuccessAt cfg fuel (fun ex node hg hd => ih ex node hg hd)
          args (first :: second :: rest) operands hd)
    | external name identity args children out resolved nonempty noExact noChain enabled operands callback =>
      have hd : argsDepth args < fuel := by
        simp only [surfaceDepth] at depth
        omega
      exact (externalOptIn cfg fuel name identity args children out tables resolved nonempty noExact noChain
        (forestSuccessAt cfg fuel (fun ex node hg hd => ih ex node hg hd) args children operands hd) callback).1 enabled

/-- Every finite grammar-valid AST and operand list parses successfully with
sufficient depth. This establishes the recursive-success prerequisites of
the route properties without assuming any parseCore result
(`src/Parse.jl:433-446,460-501,508-521,560-599`). -/
def GrammarSuccess : Prop :=
  (∀ (cfg : ParseConfig) (ex : Surface) (node : ParsedNode) (fuel : Nat),
    TableValid cfg.operators → ParseGrammar cfg ex node → surfaceDepth ex < fuel →
    parseCore cfg fuel ex = .ok node) ∧
  (∀ (cfg : ParseConfig) (args : List Surface) (nodes : List ParsedNode) (fuel : Nat),
    TableValid cfg.operators → ForestGrammar cfg args nodes → argsDepth args < fuel →
    args.mapM (parseCore cfg fuel) = .ok nodes)

theorem grammarSuccess : GrammarSuccess := by
  constructor
  · intro cfg ex node fuel tables grammar depth
    exact parseSuccessAt fuel cfg ex node tables grammar depth
  · intro cfg args nodes fuel tables grammar depth
    exact forestSuccessAt cfg fuel (fun ex node hg hd => parseSuccessAt fuel cfg ex node tables hg hd)
      args nodes grammar depth

example : TableValid binaryCfg.operators ∧
    ParseGrammar binaryCfg (.call "-" operandArgs)
      ⟨"GraphNode", .branch 1 [.branch 1 [.feature 1, .feature 2], .feature 3]⟩ ∧
    surfaceDepth (.call "-" operandArgs) < 3 := by
  refine ⟨?_, ?_, by decide⟩
  · simp [TableValid, binaryCfg]
  · apply ParseGrammar.nary (identity := "-") (first := ⟨"GraphNode", .feature 1⟩)
      (second := ⟨"GraphNode", .feature 2⟩) (rest := [⟨"GraphNode", .feature 3⟩])
    · rfl
    · decide
    · rfl
    · decide
    · rfl
    · rfl
    · exact .cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil))

example : let cfg : ParseConfig := { names := some ["x"] }
    TableValid cfg.operators ∧ ForestGrammar cfg
      [.literal zero, .symbol "x", .node "GraphNode" (.feature 1)]
      [⟨"Node", .const zero⟩, ⟨"Node", .feature 1⟩, ⟨"Node", .feature 1⟩] ∧
    argsDepth [.literal zero, .symbol "x", .node "GraphNode" (.feature 1)] < 2 := by
  refine ⟨?_, .cons (.literal _) (.cons (.symbol "x" 1 rfl) (.cons (.node _ _) .nil)), by decide⟩
  simp [TableValid]


example : ParseGrammar variadicCfg (.call "-" operandArgs)
    ⟨"GraphNode", .branch 1 (operandNodes.map ParsedNode.tree)⟩ :=
  .exact "-" "-" operandArgs operandNodes 1 rfl rfl rfl
    (.cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil)))

example : ParseGrammar externalCfg (.call "external" operandArgs)
    ⟨"GraphNode", .feature 8⟩ := by
  apply ParseGrammar.external (identity := "external") (children := operandNodes)
    (out := ⟨"Node", .feature 8⟩)
  · rfl
  · rfl
  · rfl
  · simp [NoChain]
  · rfl
  · exact .cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil))
  · rfl

/-- Input-grammar version of variadic chaining: no recursive parse result is
assumed, src/Parse.jl:451-504. -/
def GrammarNaryChain : Prop := ∀ cfg fuel name identity args first second rest idx,
  TableValid cfg.operators → Resolved cfg name identity args.length →
  2 < args.length → ["+", "-", "*"].contains identity = true →
  2 ≤ cfg.operators.length → findOpIndex cfg.operators identity args.length = none →
  findOpIndex cfg.operators identity 2 = some idx →
  ForestGrammar cfg args (first :: second :: rest) → argsDepth args < fuel →
  parseCore cfg (fuel + 1) (.call name args) = .ok ⟨cfg.nodeType,
    (rest.map ParsedNode.tree).foldl (fun acc tree => .branch idx [acc, tree])
      (.branch idx [first.tree, second.tree])⟩
theorem grammarNaryChain : GrammarNaryChain := by
  intro cfg fuel name identity args first second rest idx ht hr hn ho hd he hi hg hf
  exact naryChain cfg fuel name identity args first second rest idx ht hr hn ho hd he hi
    (grammarSuccess.2 cfg args (first :: second :: rest) fuel ht hg hf)
example : ForestGrammar binaryCfg operandArgs operandNodes ∧ argsDepth operandArgs < 2 :=
  ⟨.cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil)), by decide⟩

/-- Exact arity wins for every grammar-valid operand forest, src/Parse.jl:426-504. -/
def GrammarVariadicArity : Prop := ∀ cfg fuel name identity args children naryIdx binaryIdx,
  TableValid cfg.operators → Resolved cfg name identity args.length →
  2 < args.length → ["+", "-", "*"].contains identity = true →
  findOpIndex cfg.operators identity args.length = some naryIdx →
  findOpIndex cfg.operators identity 2 = some binaryIdx →
  ForestGrammar cfg args children → argsDepth args < fuel →
  parseCore cfg (fuel + 1) (.call name args) =
    .ok ⟨cfg.nodeType, .branch naryIdx (children.map ParsedNode.tree)⟩
theorem grammarVariadicArity : GrammarVariadicArity := by
  intro cfg fuel name identity args children naryIdx binaryIdx ht hr hn ho hi hb hg hf
  exact variadicArityPriority cfg fuel name identity args children naryIdx binaryIdx ht hr hn ho hi hb
    (grammarSuccess.2 cfg args children fuel ht hg hf)
example : ForestGrammar variadicCfg operandArgs operandNodes ∧ argsDepth operandArgs < 2 :=
  ⟨.cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil)), by decide⟩

/-- Input-grammar external routing, including the rejected opt-out case,
src/Parse.jl:506-544. The external callback result is explicit. -/
def GrammarExternalOptIn : Prop := ∀ cfg fuel name identity args children out,
  TableValid cfg.operators → Resolved cfg name identity args.length →
  args.isEmpty = false → findOpIndex cfg.operators identity args.length = none →
  NoChain cfg identity args → ForestGrammar cfg args children → argsDepth args < fuel →
  cfg.env.external identity children = .ok out →
  (cfg.evaluateOn.contains identity = true →
    parseCore cfg (fuel + 1) (.call name args) = .ok {out with tag := cfg.nodeType}) ∧
  (cfg.evaluateOn.contains identity = false →
    parseCore cfg (fuel + 1) (.call name args) =
      .error (.argumentError "Unrecognized operator; pass external functions to evaluate_on."))
theorem grammarExternalOptIn : GrammarExternalOptIn := by
  intro cfg fuel name identity args children out ht hr hn hi hc hg hf ho
  exact externalOptIn cfg fuel name identity args children out ht hr hn hi hc
    (grammarSuccess.2 cfg args children fuel ht hg hf) ho
example : ForestGrammar externalCfg operandArgs operandNodes ∧ argsDepth operandArgs < 2 :=
  ⟨.cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil)), by decide⟩

/-- Constructor-family selection for every grammar-valid operand forest,
including converted prebuilt leaves, src/Parse.jl:433-448,506-522,560-599. -/
def GrammarConstructorFamily : Prop :=
  (∀ cfg fuel name identity args children idx,
    TableValid cfg.operators → Resolved cfg name identity args.length → args.isEmpty = false →
    findOpIndex cfg.operators identity args.length = some idx →
    ForestGrammar cfg args children → argsDepth args < fuel →
    (parseCore cfg (fuel + 1) (.call name args)).toOption.map ParsedNode.tag = some cfg.nodeType) ∧
  (∀ cfg fuel name identity args children out,
    TableValid cfg.operators → Resolved cfg name identity args.length → args.isEmpty = false →
    findOpIndex cfg.operators identity args.length = none → NoChain cfg identity args →
    ForestGrammar cfg args children → argsDepth args < fuel →
    cfg.env.external identity children = .ok out → cfg.evaluateOn.contains identity = true →
    (parseCore cfg (fuel + 1) (.call name args)).toOption.map ParsedNode.tag = some cfg.nodeType) ∧
  (∀ cfg tag tree, parseLeaf cfg (.node tag tree) = .ok ⟨cfg.nodeType, tree⟩)
theorem grammarConstructorFamily : GrammarConstructorFamily := by
  constructor
  · intro cfg fuel name identity args children idx ht hr hn hi hg hf
    exact constructorFamilyConversion.1 cfg fuel name identity args children idx ht hr hn hi
      (grammarSuccess.2 cfg args children fuel ht hg hf)
  constructor
  · intro cfg fuel name identity args children out ht hr hn hi hc hg hf ho he
    exact constructorFamilyConversion.2.1 cfg fuel name identity args children out ht hr hn hi hc
      (grammarSuccess.2 cfg args children fuel ht hg hf) ho he
  · exact constructorFamilyConversion.2.2
example : ForestGrammar binaryCfg operandArgs operandNodes ∧ argsDepth operandArgs < 2 :=
  ⟨.cons (.node _ _) (.cons (.node _ _) (.cons (.node _ _) .nil)), by decide⟩

end DynExpr.StringsParse.General
