import DynExpr.StringsParse.Strings

namespace DynExpr.StringsParse

structure ParsedNode where
  tag : String
  tree : Tree Scalar
  deriving Repr

/-- Core.eval and eval_module are explicit environments (`src/Parse.jl:351-375,
394-409,578-583`). Arbitrary module calls can fail with any Julia error. -/
structure Environment where
  builtin : String → Option String := fun s =>
    if ["+", "-", "*", "/", "^", "sin", "cos", "exp"].contains s then some s else none
  globals : String → Option Scalar := fun _ => none
  functions : String → Bool := fun _ => false
  evaluate : Surface → List String → Jl Scalar := fun _ _ => .error (.argumentError "unresolved module expression")
  external : String → List ParsedNode → Jl ParsedNode := fun _ _ => .error (.methodError "external function")

structure ParseConfig where
  operators : Operators := []
  names : Option (List String) := none
  nodeType : String := "Node"
  evaluateOn : List String := []
  moduleEnv : Option Environment := none
  env : Environment := {}

/-- findfirst uses the first matching feature name (`src/Parse.jl:578-593`). -/
def variableIndex (name : String) (names : Option (List String)) : Option Nat := do
  let names ← names
  let i ← (names.zipIdx).find? (fun p => p.1 == name)
  return i.2 + 1

/-- Leaf dispatch (`src/Parse.jl:560-599`). A prebuilt node is returned as
`convert(node_type, ex)`, which keeps its tree and has the requested family
(`src/Parse.jl:594-595`, `src/base.jl:535-565`); `Ownership.lean` models the
object identities. -/
def parseLeaf (cfg : ParseConfig) : Surface → Jl ParsedNode
  | .expression => .error (.argumentError "Cannot parse an expression as a value in another expression.")
  | .symbol s =>
      match variableIndex s cfg.names with
      | some i => .ok ⟨cfg.nodeType, .feature i⟩
      | none => match cfg.moduleEnv.bind (fun e => e.globals s) with
        | some v => .ok ⟨cfg.nodeType, .const v⟩
        | none => .error (.argumentError ("Variable `" ++ s ++ "` not found in `variable_names`"))
  | .node _ t => .ok ⟨cfg.nodeType, t⟩
  | .literal v => .ok ⟨cfg.nodeType, .const v⟩
  | _ => .error (.argumentError "expected a leaf")

/-- The name `_find_operator_by_name` compares with the call head
(`src/Parse.jl:309`): a `Broadcast.BroadcastFunction` by its `get_op_name`
spelling (such as `cos.`), every other callable by `nameof`. -/
def NamedOp.parseName (op : NamedOp) : String := if op.broadcast then op.display else op.name

/-- Name resolution collects matches over all arities then enforces a unique
match at the requested arity (`src/Parse.jl:304-345`). -/
def findOperatorByName (ops : Operators) (name : String) (degree : Nat) : Jl String :=
  let all := (ops.zipIdx).flatMap (fun (os, arity) =>
    (os.filter (fun op => op.parseName == name)).map (fun op => (op.identity, arity + 1)))
  if all.isEmpty then .error (.argumentError "Function not found in operators.")
  else match all.filter (fun p => p.2 == degree) with
    | [(identity, _)] => .ok identity
    | [] => .error (.argumentError "Operator found but not with this arity.")
    | _ => .error (.argumentError "Ambiguous operator with this arity.")

/-- Matching functions or their declared aliases (`src/Parse.jl:426-431`). -/
def findOpIndex (ops : Operators) (identity : String) (degree : Nat) : Option Nat :=
  if degree = 0 then none else do
    let pair ← ((ops[degree - 1]?.getD []).zipIdx).find?
      (fun p => p.1.identity == identity || p.1.alias == identity)
    return pair.2 + 1

/-- Constant folds of the imaginary unit (`src/Parse.jl:236-247`). -/
def normalizeCall (name : String) (args : List Surface) : Surface :=
  match name, args with
  | "+", [.literal (.real a), .literal (.complex (.fin 0) b)] => .literal (.complex a b)
  | "+", [.literal (.complex (.fin 0) a), .literal (.real b)] => .literal (.complex b a)
  | "-", [.literal (.real a), .literal (.complex (.fin 0) b)] => .literal (.complex a (-b))
  | "*", [.literal (.real a), .literal (.complex (.fin 0) b)] => .literal (.complex (.fin 0) (a * b))
  | "*", [.literal (.complex (.fin 0) a), .literal (.real b)] => .literal (.complex (.fin 0) (a * b))
  | _, _ => .call name args

/-- Symbol rule (`src/Parse.jl:220-226`): a declared variable name is kept;
otherwise `im`, `NaN`, and `Inf` become Julia's constants. -/
def normalizeSymbol (names : Option (List String)) (s : String) : Surface :=
  if (names.map (fun ns => ns.contains s)).getD false then .symbol s
  else if s == "im" then .literal (.complex (.fin 0) (.fin 1))
  else if s == "NaN" then .literal (.real .nan)
  else if s == "Inf" then .literal (.real .posInf)
  else .symbol s

/-- A nonfinite `Real` operand (`src/Parse.jl:229`). -/
def nonfiniteReal : Surface → Option Scalar
  | .literal (.real v) => if v.valid then none else some (.real v)
  | .literal (.float32 v) => if v.valid then none else some (.float32 v)
  | _ => none

/-- Call rule on normalized arguments (`src/Parse.jl:229-248`): unary `-`/`+`
of a nonfinite real folds to a constant, then the imaginary-unit folds. -/
def normalizeCallExpr (name : String) (args : List Surface) : Surface :=
  match args with
  | [a] => match nonfiniteReal a with
    | some v => if name == "-" then .literal v.neg else if name == "+" then .literal v
      else normalizeCall name args
    | none => normalizeCall name args
  | _ => normalizeCall name args

mutual
  /-- `_normalize_expression_for_parse` (`src/Parse.jl:220-250`), applied
  bottom-up. Julia also maps the call head; heads `im`, `NaN`, and `Inf` then
  name the same non-Function values that `Core.eval(EmptyModule, head)` returns
  for the unnormalized symbol, so the head keeps its name here and resolution is
  left to `parseCore` (`src/Parse.jl:402-417`). A dot call `Expr(:., f, tuple)`
  normalizes its tuple arguments without call folds; its head keeps its name
  because `string` of the values `im`, `NaN`, and `Inf` spells the symbol, which
  is all `parseCore` reads (`src/Parse.jl:393`). -/
  def normalize (names : Option (List String)) : Surface → Surface
    | .symbol s => normalizeSymbol names s
    | .call name args => normalizeCallExpr name (normalizeArgs names args)
    | .dotCall f args => .dotCall f (normalizeArgs names args)
    | s => s
  def normalizeArgs (names : Option (List String)) : List Surface → List Surface
    | [] => []
    | s :: ss => normalize names s :: normalizeArgs names ss
end

def chain (idx : Nat) (first second : Tree Scalar) (rest : List (Tree Scalar)) : Tree Scalar :=
  rest.foldl (fun acc t => .branch idx [acc, t]) (.branch idx [first, second])

/-- Recursive parse order: rewrite a dot call `f.(args...)` to a call of the
symbol `f.` (`src/Parse.jl:389-394`), then resolve a function, try exact
arity/alias, chain +, -, *, evaluate_on, or error. Unknown function names fall
back to whole-AST module evaluation of the rewritten call
(`src/Parse.jl:379-553`), before parsing their children. -/
def parseCore (cfg : ParseConfig) : Nat → Surface → Jl ParsedNode
  | 0, _ => .error (.argumentError "parse depth exhausted")
  | fuel + 1, ex => do
      let ex : Surface := match ex with
        | .dotCall f args => .call (f ++ ".") args
        | ex => ex
      match ex with
      | .unsupported head => throw (.argumentError ("Unrecognized expression type: " ++ head))
      | .call name args =>
          let resolved := match cfg.env.builtin name with
            | some id => .ok id
            | none => findOperatorByName cfg.operators name args.length
          if let .error e := resolved then
            if let some env := cfg.moduleEnv then
              if env.functions name then
                return ⟨cfg.nodeType, .const (← env.evaluate ex (cfg.names.getD []))⟩
            throw e
          let identity ← resolved
          if args.isEmpty then throw .boundsError
          if let some idx := findOpIndex cfg.operators identity args.length then
            let children ← args.mapM (parseCore cfg fuel)
            return ⟨cfg.nodeType, .branch idx (children.map ParsedNode.tree)⟩
          if args.length > 2 && ["+", "-", "*"].contains identity then
            if cfg.operators.length < 2 then throw .boundsError
            if let some idx := findOpIndex cfg.operators identity 2 then
              let children ← args.mapM (parseCore cfg fuel)
              return ⟨cfg.nodeType, chain idx (children[0]?.map ParsedNode.tree |>.getD (.feature 0))
                (children[1]?.map ParsedNode.tree |>.getD (.feature 0))
                (children.drop 2 |>.map ParsedNode.tree)⟩
          if cfg.evaluateOn.contains identity then
            let out ← cfg.env.external identity (← args.mapM (parseCore cfg fuel))
            return {out with tag := cfg.nodeType}
          throw (.argumentError "Unrecognized operator; pass external functions to evaluate_on.")
      | _ => parseLeaf cfg ex

mutual
  def surfaceDepth : Surface → Nat
    | .call _ args => 1 + argsDepth args
    | .dotCall _ args => 1 + argsDepth args
    | _ => 1
  def argsDepth : List Surface → Nat
    | [] => 0
    | a :: as => max (surfaceDepth a) (argsDepth as)
end

/-- Public AST and String entry points and macro expansion all call the same
parser with normalized names and constants (`src/Parse.jl:95-111,252-297`). -/
def parseExpression (cfg : ParseConfig) (ex : Surface) : Jl ParsedNode :=
  parseCore cfg (surfaceDepth ex + 1) (normalize cfg.names ex)

def parseString (cfg : ParseConfig) (s : String) : Jl ParsedNode := do
  parseExpression cfg (← metaParse s)

/-- Accepted macro keywords (`src/Parse.jl:113-191`). -/
def macroKeywords : List String := ["operators", "variable_names", "node_type",
  "expression_type", "evaluate_on", "eval_module", "extra_metadata", "binary_operators", "unary_operators"]

def macroErrorKeywords : List String := ["operators", "variable_names", "node_type",
  "expression_type", "evaluate_on", "eval_module", "extra_metadata"]

/-- Error spelling for a Symbol keyword (`src/Parse.jl:186-190`). -/
def macroKeywordDiagnostic (bad : String) (available : List String) : String :=
  "Unrecognized argument: `" ++ bad ++ "`. The available arguments are " ++
    String.intercalate ", " ((available.take (available.length - 1)).map (fun name => "`" ++ name ++ "`")) ++
    ", and `" ++ (available.getLast?.getD "") ++ "`."

/-- _parse_kws selects the first invalid keyword and enforces mutually exclusive
operator sources (`src/Parse.jl:126-206`). Values are supplied by interpolation. -/
def parseMacroKeywords (keys : List String) : Jl Unit := do
  if let some bad := keys.find? (fun k => !macroKeywords.contains k) then
    throw (.argumentError (macroKeywordDiagnostic bad macroErrorKeywords))
  if keys.contains "operators" then
    if keys.contains "binary_operators" || keys.contains "unary_operators" then
      throw (.assertionError "conflicting operator keywords")
  else if !(keys.contains "binary_operators" || keys.contains "unary_operators") then
    throw (.assertionError "You must specify the operators")

def parseMacro (cfg : ParseConfig) (ex : Surface) : Jl ParsedNode := parseExpression cfg ex

end DynExpr.StringsParse
