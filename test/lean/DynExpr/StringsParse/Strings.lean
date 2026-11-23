import DynExpr.StringsParse.Surface
import DynExpr.Model.NodeHeap
import DynExpr.Model.Denote

namespace DynExpr.StringsParse

/-- Operator identity, Julia name, alias, renderer, and arbitrary semantics used
by `src/Strings.jl:7-69` and `src/Parse.jl:304-345,433-440`. `display` and
`pretty` are the `get_op_name`/`get_pretty_op_name` results, which
`stringsparse-cache-collision` proves are each callable's own text.
`broadcast` records `op isa Broadcast.BroadcastFunction`. -/
structure NamedOp where
  identity : String
  name : String
  display : String
  pretty : String
  alias : String
  broadcast : Bool := false
  apply : List Scalar → Scalar

abbrev Operators := List (List NamedOp)

def Operators.enum (ops : Operators) : OpEnum Scalar := ⟨ops.map (List.map NamedOp.apply)⟩

/-- Julia's broadcast-name cases of `_get_op_name` (`src/Strings.jl:53-66`). -/
def broadcastName (name : String) : String :=
  if name.length == 1 && ['+', '-', '*', '/', '^'].contains (name.toList.headD ' ')
  then "." ++ name else name ++ "."

/-- `get!` on the operator-name cache (`src/Strings.jl:44,48-50`): the first
entry with the key wins; a missing key stores and returns the rendered text. -/
def cachedName (cache : List (Nat × String)) (key : Nat) (render : String) :
    String × List (Nat × String) :=
  match cache.find? (fun p => p.1 == key) with
  | some p => (p.2, cache)
  | none => (render, (key, render) :: cache)

/-- A callable passed to `get_op_name`: `objectid(op)`, whether its type is a
singleton (`Base.issingletontype(F)`), and its current `_get_op_name(op)` text
(`src/Strings.jl:46-66`). Object identity is the `objectid` (Q44). -/
structure OpObject where
  objectId : Nat
  singleton : Bool
  name : String

/-- `get_op_name` (`src/Strings.jl:46-52`): singleton callables go through the
process-wide cache keyed by `objectid`; every other callable is rendered on each
call. -/
def getOpName (cache : List (Nat × String)) (op : OpObject) : String × List (Nat × String) :=
  if op.singleton then cachedName cache op.objectId op.name else (op.name, cache)

/-- The cache after a sequence of `get_op_name` calls from the empty
`OP_NAME_CACHE` created at module load (`src/Strings.jl:44`). -/
def runOpNames (calls : List OpObject) : List (Nat × String) :=
  calls.foldl (fun cache op => (getOpName cache op).2) []

/-- Degree dispatch and generic operator placeholders (`src/Strings.jl:7-42`). -/
def dispatchOpName (ops : Option Operators) (degree idx : Nat) (pretty : Bool) : Jl String :=
  match ops with
  | none => .ok ((if degree == 1 then "unary_operator[" else if degree == 2
      then "binary_operator[" else "operator_deg" ++ toString degree ++ "[") ++ toString idx ++ "]")
  | some os => do
      if degree = 0 || idx = 0 then throw .boundsError
      let op ← match (os[degree - 1]?.getD [])[idx - 1]? with
        | some op => .ok op | none => .error .boundsError
      return if pretty then op.pretty else op.display

/-- Exact outer-pair stripping, including the empty-vector bounds exception
(`src/Strings.jl:71-77`). No balanced-parenthesis validation is performed. -/
def stripBrackets (s : String) : Jl String :=
  if s.isEmpty then .error .boundsError
  else if s.toList.head? == some '(' && s.toList.getLast? == some ')'
  then .ok (String.ofList (s.toList.drop 1 |>.take (s.length - 2)))
  else .ok s

/-- Constant brackets distinguish complex from real values (`src/Strings.jl:81-93`). -/
def stringConstant (v : Scalar) : String :=
  match v with
  | .complex _ _ => "(" ++ scalarText v ++ ")"
  | _ => scalarText v

/-- One-based feature names and xN fallback (`src/Strings.jl:95-103`). -/
def stringVariable (feature : Nat) (names : Option (List String)) : String :=
  match names with
  | none => "x" ++ toString feature
  | some ns => if feature = 0 then "x0" else
      ns[feature - 1]?.getD ("x" ++ toString feature)

/-- Infix decision reads first(op) only for binary calls; a binary spelling
ending in `^` brackets a left operand that starts with `-`, reading `first` of
that operand; prefix arguments strip one outer pair (`src/Strings.jl:106-133`). -/
def combineOpWithInputs (op : String) (args : List String) : Jl String := do
  let isInfix ← if args.length == 2 then
      match op.toList.head? with
      | none => .error .boundsError
      | some c => .ok (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || op == "!=")
    else .ok false
  if isInfix then
    let left := args[0]?.getD ""
    let signedBase ← if op.toList.getLast? == some '^' then
        match left.toList.head? with
        | none => .error .boundsError
        | some c => .ok (c == '-')
      else .ok false
    let left := if signedBase then "(" ++ left ++ ")" else left
    return "(" ++ left ++ " " ++ op ++ " " ++ args[1]?.getD "" ++ ")"
  if args.isEmpty then throw .boundsError
  let args ← args.mapM stripBrackets
  return op ++ "(" ++ String.intercalate ", " args ++ ")"

/-- pretty overrides the deprecated raw flag (`src/Strings.jl:168-171,224-225`). -/
def resolvePretty (pretty raw : Option Bool) : Bool :=
  pretty.getD ((raw.map (!·)).getD false)

structure RenderConfig where
  operators : Option Operators := none
  names : Option (List String) := none
  varMap : Option (List String) := none
  pretty : Option Bool := none
  raw : Option Bool := none
  fVariable : Nat → Option (List String) → String := stringVariable
  fConstant : Scalar → String := stringConstant

mutual
  /-- Plain Node tree_mapreduce rendering (`src/Strings.jl:173-197`). -/
  def rawTree (cfg : RenderConfig) : Tree Scalar → Jl String
    | .const v => .ok (cfg.fConstant v)
    | .feature i => .ok (cfg.fVariable i cfg.names)
    | .branch idx cs => do
        let op ← dispatchOpName cfg.operators cs.length idx (resolvePretty cfg.pretty cfg.raw)
        combineOpWithInputs op (← rawForest cfg cs)
  def rawForest (cfg : RenderConfig) : List (Tree Scalar) → Jl (List String)
    | [] => .ok []
    | c :: cs => do return (← rawTree cfg c) :: (← rawForest cfg cs)
end

/-- Deprecated varMap resolution and mutual exclusion (`src/Strings.jl:172,217`
and `src/Utils.jl:23-29`). Deprecation warning visibility is controlled by Julia. -/
def resolveNames (names varMap : Option (List String)) : Jl (Option (List String)) :=
  match varMap with
  | none => .ok names
  | some ns => if names.isSome then .error (.assertionError "Cannot pass both varMap and variable_names")
      else .ok (some ns)

def stringTree (cfg : RenderConfig) (t : Tree Scalar) : Jl String := do
  let names ← resolveNames cfg.names cfg.varMap
  stripBrackets (← rawTree {cfg with names} t)

/-- GraphNode cache and shared-marker callback (`src/Strings.jl:188-195` and
`src/base.jl:77-121`). Cached plain text is wrapped on repeated object visits. -/
def rawGraph (cfg : RenderConfig) (g : Graph Scalar) :
    Nat → Addr → List (Addr × String) → Jl (String × List (Addr × String))
  | 0, _, _ => .error (.argumentError "cyclic graph or insufficient traversal depth")
  | fuel + 1, a, cache => do
      if let some p := cache.find? (fun p => p.1 == a) then
        return ("{" ++ p.2 ++ "}", cache)
      let c ← g.read a
      let (text, cache) ← if c.degree = 0 then
          if c.constant then
            match c.val with
            | some v => .ok (cfg.fConstant v, cache)
            | none => .error .undefRefError
          else .ok (cfg.fVariable c.feature cfg.names, cache)
        else do
          let op ← dispatchOpName cfg.operators c.degree c.op (resolvePretty cfg.pretty cfg.raw)
          let (args, cache) ← c.children.foldlM (fun (args, cache) child => do
            let (s, cache) ← rawGraph cfg g fuel child cache
            return (args ++ [s], cache)) ([], cache)
          let text ← combineOpWithInputs op args
          pure (text, cache)
      return (text, (a, text) :: cache)

def stringGraph (cfg : RenderConfig) (g : Graph Scalar) (fuel : Nat) (root : Addr) : Jl String := do
  let names ← resolveNames cfg.names cfg.varMap
  stripBrackets (← rawGraph {cfg with names} g fuel root []).1

/-- Both IO/stdout print_tree methods call println once (`src/Strings.jl:201-223`).
The returned string is the observable appended IO content. -/
def printTree (cfg : RenderConfig) (t : Tree Scalar) : Jl String := do
  return (← stringTree cfg t) ++ "\n"

/-- IO/stdout println effect and Nothing return (src/Strings.jl:218-221).
The heap records an append-only sink: stdout or a writable IOBuffer at its end. -/
def printTreeIO (cfg : RenderConfig) (t : Tree Scalar) (io : Heap String) (a : Addr) :
    Jl (Unit × Heap String) := do
  let before ← io.read a
  let text ← printTree cfg t
  let after ← io.write a (before ++ text)
  return ((), after)

end DynExpr.StringsParse
