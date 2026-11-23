import DynExpr.StringsParse.Parse
import DynExpr.StringsParse.DecimalCodec

/-! Input domain and independent specifications for the general
serialization roundtrip (`src/Strings.jl:71-197`, `src/Parse.jl:219-599`). -/

namespace DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-- ASCII Julia identifiers (`src/Strings.jl:95-103` emits names verbatim). The
head conditions beyond `isAlpha`/`_` are implied; they are stated for the lexer. -/
def asciiIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && !c.isWhitespace && !c.isDigit &&
      cs.all (fun c => c.isAlphanum || c == '_')

/-- Julia reserved words and word operators, which `Meta.parse` never reads as
plain symbols (`src/Parse.jl:297`). -/
def reservedWords : List String :=
  ["baremodule", "begin", "break", "catch", "const", "continue", "do", "else", "elseif",
   "end", "export", "false", "finally", "for", "function", "global", "if", "import", "in",
   "isa", "let", "local", "macro", "module", "quote", "return", "struct", "true", "try",
   "using", "where", "while"]

/-- Plain parseable names: ASCII identifiers that are not reserved words. -/
def plainName (s : String) : Bool := asciiIdent s && !reservedWords.contains s

/-- Operator names rendered infix for two arguments (`src/Strings.jl:106-120`). -/
def infixName (s : String) : Bool := ["+", "-", "*", "/", "^"].contains s

theorem infixName_cases {n : String} (h : infixName n = true) :
    n = "+" ∨ n = "-" ∨ n = "*" ∨ n = "/" ∨ n = "^" := by
  by_cases h1 : n = "+"; · exact Or.inl h1
  by_cases h2 : n = "-"; · exact Or.inr (Or.inl h2)
  by_cases h3 : n = "*"; · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : n = "/"; · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  by_cases h5 : n = "^"; · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
  exfalso
  simp [infixName, h1, h2, h3, h4, h5] at h

/-- Parseable operator names. `im` is excluded because the imaginary-unit pass
of `src/Parse.jl:219-249` rewrites that symbol. -/
def opNameOK (s : String) : Bool := (plainName s && s != "im") || infixName s

/-- Supported operator tables: at most two arities and 255 operators per arity
(`src/Node.jl:74-83`), unique names per arity (`src/Parse.jl:303-343`), and
display, identity, and alias equal to the name (`src/Strings.jl:7-42`,
`src/Parse.jl:426-430`). Semantics are arbitrary. -/
def CleanOps (ops : Operators) : Prop :=
  ops.length ≤ 2 ∧ ∀ os ∈ ops, os.length ≤ 255 ∧ (os.map NamedOp.name).Nodup ∧
    ∀ op ∈ os, opNameOK op.name = true ∧ op.display = op.name ∧
      op.identity = op.name ∧ op.alias = op.name

/-- Unique plain variable names fitting the UInt16 feature field. -/
def CleanNames (names : List String) : Prop :=
  names.length ≤ 65535 ∧ names.Nodup ∧ ∀ s ∈ names, plainName s = true

/-- Name of the operator at a one-based degree and index. -/
def opName (ops : Operators) (degree idx : Nat) : String :=
  (((ops[degree - 1]?.getD [])[idx - 1]?).map NamedOp.name).getD ""

/-- Admissible constants: finite terminating decimals (exactly printed), real
or complex, never Float32; complex constants only when `im` is not a variable
name (`src/Parse.jl:219-249`). -/
def CleanConst (complexOK : Bool) : Scalar → Prop
  | .real (.fin q) => Terminating q
  | .complex (.fin r) (.fin i) => complexOK = true ∧ Terminating r ∧ Terminating i
  | _ => False

/-- Renderings that begin with `-`: negative real constants and unary calls
named `-` (`src/Strings.jl:87-133`). `combine_op_with_inputs` brackets exactly
these as `^` bases (`src/Strings.jl:110-114`). -/
def MinusLed (ops : Operators) : Tree Scalar → Bool
  | .const (.real (.fin q)) => decide (q.num < 0)
  | .branch idx [_] => opName ops 1 idx == "-"
  | _ => false

/-- Renderings that begin with `+`: unary calls named `+`
(`src/Strings.jl:119-131`). Printed constants never start with `+`. -/
def PlusLed (ops : Operators) : Tree Scalar → Bool
  | .branch idx [_] => opName ops 1 idx == "+"
  | _ => false

/-- Input-only exclusions of the known serialization triggers: nonfinite,
Float32, and nonterminating constants, and complex constants when `im` is a
variable name. -/
def Admissible (ops : Operators) (names : List String) : Tree Scalar → Prop
  | .const v => CleanConst (!names.contains "im") v
  | .feature _ => True
  | .branch _ cs => ∀ c ∈ cs, Admissible ops names c

/-- No `^` base is a unary `+` call, which `Meta.parse` reads as
`+(base ^ exponent)` (Q40). -/
def NoPlusBase (ops : Operators) : Tree Scalar → Prop
  | .branch idx cs =>
      (∀ a b, cs = [a, b] → opName ops 2 idx = "^" → PlusLed ops a = false) ∧
      ∀ c ∈ cs, NoPlusBase ops c
  | _ => True

/-- A `^` call with original base `a` and rebuilt operands `a'`, `b'`. When `a`
is a unary `+` call `+(c)`, Julia parses the printed `+(c) ^ b` as
`+(c ^ b)` (Q40), so the rebuilt `+(c')` moves above the power. -/
def rotPow (ops : Operators) (idx : Nat) (a a' b' : Tree Scalar) : Tree Scalar :=
  if opName ops 2 idx = "^" ∧ PlusLed ops a = true then
    match a' with
    | .branch pidx [c'] => .branch pidx [.branch idx [c', b']]
    | _ => .branch idx [a', b']
  else .branch idx [a', b']

/-- The tree that `Meta.parse` reads back before literal folds. -/
def rotT (ops : Operators) : Tree Scalar → Tree Scalar
  | .const v => .const v
  | .feature k => .feature k
  | .branch idx [c] => .branch idx [rotT ops c]
  | .branch idx [a, b] => rotPow ops idx a (rotT ops a) (rotT ops b)
  | .branch idx cs => .branch idx cs

def rcfg (ops : Operators) (names : List String) : RenderConfig :=
  {operators := some ops, names := some names}
def pcfg (ops : Operators) (names : List String) : ParseConfig :=
  {operators := ops, names := some names}

/-! ## Expected parse result: Julia's literal folding -/

/-- `Meta.parse` folds a unary `-`/`+` call on a numeric literal
(`src/Parse.jl:297`). -/
def unaryFold (n : String) (idx : Nat) : Tree Scalar → Tree Scalar
  | .const (.real v) =>
      if n == "-" then .const (.real (-v)) else if n == "+" then .const (.real v)
      else .branch idx [.const (.real v)]
  | c => .branch idx [c]

/-- Imaginary-unit folding of `src/Parse.jl:236-247`. -/
def binaryFold (n : String) (idx : Nat) : Tree Scalar → Tree Scalar → Tree Scalar
  | .const (.real x), .const (.complex (.fin 0) y) =>
      if n == "+" then .const (.complex x y)
      else if n == "-" then .const (.complex x (-y))
      else if n == "*" then .const (.complex (.fin 0) (x * y))
      else .branch idx [.const (.real x), .const (.complex (.fin 0) y)]
  | .const (.complex (.fin 0) x), .const (.real y) =>
      if n == "+" then .const (.complex y x)
      else if n == "*" then .const (.complex (.fin 0) (x * y))
      else .branch idx [.const (.complex (.fin 0) x), .const (.real y)]
  | a, b => .branch idx [a, b]

/-- The tree produced by reparsing the serialization: identical up to Julia's
literal folding. -/
def expect (ops : Operators) : Tree Scalar → Tree Scalar
  | .const v => .const v
  | .feature k => .feature k
  | .branch idx [c] => unaryFold (opName ops 1 idx) idx (expect ops c)
  | .branch idx [a, b] => binaryFold (opName ops 2 idx) idx (expect ops a) (expect ops b)
  | .branch idx cs => .branch idx cs

/-- Trees without fold sites: no complex constants and no unary `-`/`+` on a
constant. -/
def FoldFree (ops : Operators) : Tree Scalar → Prop
  | .const (.complex _ _) => False
  | .const _ => True
  | .feature _ => True
  | .branch idx cs =>
      (∀ c, cs = [c] → ["-", "+"].contains (opName ops 1 idx) = true → ∀ v, c ≠ .const v) ∧
      ∀ c ∈ cs, FoldFree ops c

/-- Standard Julia meaning of the folded operators on finite arguments. -/
def StdFold (ops : Operators) : Prop :=
  (∀ op ∈ ops[0]?.getD [], op.name = "-" → ∀ q, op.apply [.real (.fin q)] = .real (.fin (-q))) ∧
  (∀ op ∈ ops[0]?.getD [], op.name = "+" → ∀ q, op.apply [.real (.fin q)] = .real (.fin q)) ∧
  (∀ op ∈ ops[1]?.getD [], op.name = "+" → ∀ x y,
    op.apply [.real (.fin x), .complex (.fin 0) (.fin y)] = .complex (.fin x) (.fin y) ∧
    op.apply [.complex (.fin 0) (.fin x), .real (.fin y)] = .complex (.fin y) (.fin x)) ∧
  (∀ op ∈ ops[1]?.getD [], op.name = "-" → ∀ x y,
    op.apply [.real (.fin x), .complex (.fin 0) (.fin y)] = .complex (.fin x) (.fin (-y))) ∧
  (∀ op ∈ ops[1]?.getD [], op.name = "*" → ∀ x y,
    op.apply [.real (.fin x), .complex (.fin 0) (.fin y)] = .complex (.fin 0) (.fin (x * y)) ∧
    op.apply [.complex (.fin 0) (.fin x), .real (.fin y)] = .complex (.fin 0) (.fin (x * y)))

/-- Unary `+` operators are the identity on every argument. -/
def PlusIdentity (ops : Operators) : Prop :=
  ∀ op ∈ ops[0]?.getD [], op.name = "+" → ∀ v, op.apply [v] = v

/-! ## Token and syntax specifications -/

def dec (q : Rat) : String := finiteText q false

/-- Tokens of a real constant: a sign token then digits for negatives. -/
def realToks (q : Rat) : List String :=
  if q.num < 0 then ["-", dec (-q)] else [dec q]

def imagSign (i : Rat) : String := if i.num < 0 then "-" else "+"
def imagMag (i : Rat) : Rat := if i.num < 0 then -i else i

/-- Renderings wrapped in one parenthesis pair: complex constants and infix
calls (`src/Strings.jl:81-120`). -/
def wrapped (ops : Operators) : Tree Scalar → Bool
  | .const (.complex _ _) => true
  | .branch idx [_, _] => infixName (opName ops 2 idx)
  | _ => false

/-- Left operands of an infix spelling rendered inside one more parenthesis
pair: wrapped renderings and `-`-led `^` bases (`src/Strings.jl:110-114`). -/
def lhsWrap (ops : Operators) (n : String) (a : Tree Scalar) : Bool :=
  wrapped ops a || (n == "^" && MinusLed ops a)

/-- Tokens of the rendering with its outer pair stripped. -/
def bare (ops : Operators) (names : List String) : Tree Scalar → List String
  | .const (.real (.fin q)) => realToks q
  | .const (.complex (.fin r) (.fin i)) => realToks r ++ [imagSign i, dec (imagMag i), "im"]
  | .const _ => []
  | .feature k => [names[k - 1]?.getD ""]
  | .branch idx [c] => [opName ops 1 idx, "("] ++ bare ops names c ++ [")"]
  | .branch idx [a, b] =>
      if infixName (opName ops 2 idx) then
        (if lhsWrap ops (opName ops 2 idx) a then "(" :: bare ops names a ++ [")"]
          else bare ops names a) ++
          [opName ops 2 idx] ++
          (if wrapped ops b then "(" :: bare ops names b ++ [")"] else bare ops names b)
      else [opName ops 2 idx, "("] ++ bare ops names a ++ [","] ++ bare ops names b ++ [")"]
  | .branch _ _ => []

/-- Tokens of the full rendering. -/
def full (ops : Operators) (names : List String) (t : Tree Scalar) : List String :=
  if wrapped ops t then "(" :: bare ops names t ++ [")"] else bare ops names t

/-- Tokens of the left operand of the infix spelling `n`. -/
def lhs (ops : Operators) (names : List String) (n : String) (a : Tree Scalar) : List String :=
  if lhsWrap ops n a then "(" :: bare ops names a ++ [")"] else bare ops names a

/-- Syntax tree produced by `Meta.parse` (`src/Parse.jl:297`). -/
def surf (ops : Operators) (names : List String) : Tree Scalar → Surface
  | .const (.complex (.fin r) (.fin i)) =>
      .call (imagSign i) [.literal (.real (.fin r)),
        .call "*" [.literal (.real (.fin (imagMag i))), .symbol "im"]]
  | .const v => .literal v
  | .feature k => .symbol (names[k - 1]?.getD "")
  | .branch idx [c] =>
      let n := opName ops 1 idx
      if n == "-" || n == "+" then
        match surf ops names c with
        | .literal v => .literal (if n == "-" then v.neg else v)
        | s => .call n [s]
      else .call n [surf ops names c]
  | .branch idx [a, b] => .call (opName ops 2 idx) [surf ops names a, surf ops names b]
  | .branch _ _ => .unsupported ""

/-- Syntax tree of an expected tree after imaginary-unit normalization. -/
def toSurf (ops : Operators) (names : List String) : Tree Scalar → Surface
  | .const v => .literal v
  | .feature k => .symbol (names[k - 1]?.getD "")
  | .branch idx [c] => .call (opName ops 1 idx) [toSurf ops names c]
  | .branch idx [a, b] => .call (opName ops 2 idx) [toSurf ops names a, toSurf ops names b]
  | .branch _ _ => .unsupported ""

end DynExpr.StringsParse.Roundtrip
