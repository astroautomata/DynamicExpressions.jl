import DynExpr.Runtime.Value
import DynExpr.Runtime.Errors
import DynExpr.Model.Tree
import Std

namespace DynExpr.StringsParse

/-- Real/Float32/complex scalar cases of `src/Strings.jl:81-93` and
`src/Parse.jl:219-249`. Finite arithmetic inherits JF's exact-rational scope. -/
inductive Scalar where
  | real (v : JF)
  | float32 (v : JF)
  | complex (re im : JF)
  deriving DecidableEq, Repr

def Scalar.parts : Scalar → JF × JF
  | .real v | .float32 v => (v, .fin 0)
  | .complex r i => (r, i)

def Scalar.add (a b : Scalar) : Scalar :=
  match a, b with
  | .real x, .real y => .real (x + y)
  | .float32 x, .float32 y => .float32 (x + y)
  | .real x, .float32 y | .float32 x, .real y => .real (x + y)
  | _, _ => .complex (a.parts.1 + b.parts.1) (a.parts.2 + b.parts.2)

def Scalar.neg : Scalar → Scalar
  | .real x => .real (-x)
  | .float32 x => .float32 (-x)
  | .complex r i => .complex (-r) (-i)

def Scalar.sub (a b : Scalar) : Scalar := a.add b.neg

def Scalar.mul (a b : Scalar) : Scalar :=
  match a, b with
  | .real x, .real y => .real (x * y)
  | .float32 x, .float32 y => .float32 (x * y)
  | .real x, .float32 y | .float32 x, .real y => .real (x * y)
  | _, _ => .complex (a.parts.1 * b.parts.1 - a.parts.2 * b.parts.2)
      (a.parts.1 * b.parts.2 + a.parts.2 * b.parts.1)

/-- Exact decimal value `mant / 10 ^ scale`. -/
structure Decimal where
  mant : Int
  scale : Nat
  deriving DecidableEq, Repr

/-- Removes factors 2 and 5 from `d`, returning their count and the residue.
Fuel `d` suffices for `0 < d`, since each step halves or fifths `d`. -/
def decimalScale : Nat → Nat → Nat × Nat
  | 0, d => (0, d)
  | fuel + 1, d =>
      if d % 2 = 0 ∧ 0 < d then
        let r := decimalScale fuel (d / 2)
        (r.1 + 1, r.2)
      else if d % 5 = 0 ∧ 0 < d then
        let r := decimalScale fuel (d / 5)
        (r.1 + 1, r.2)
      else (0, d)

/-- Decimal representation of a rational whose denominator divides a power of
ten, which covers every finite binary floating-point value. -/
def toDecimal (q : Rat) : Decimal :=
  let s := (decimalScale q.den q.den).1
  ⟨q.num * ((10 ^ s / q.den : Nat) : Int), s⟩

/-- Drops trailing `'0'` characters. -/
def stripTrailingZeros : List Char → List Char
  | [] => []
  | c :: cs =>
      let r := stripTrailingZeros cs
      if r.isEmpty && c == '0' then [] else c :: r

/-- Characters of Julia's decimal and scientific forms used by `string(val)` at
`src/Strings.jl:87-93`: scientific when the magnitude is at least `1e6` or
below `1e-4`, with trailing fractional zeros removed. -/
def decimalChars (x : Decimal) (single : Bool) : List Char :=
  let m := x.mant.natAbs
  let s := x.scale
  let sign := if x.mant < 0 then ['-'] else []
  let ds := Nat.toDigits 10 m
  let whole := m / 10 ^ s
  if 1000000 ≤ whole ∨ (whole = 0 ∧ 0 < m ∧ m * 10000 < 10 ^ s) then
    let sig := stripTrailingZeros ds
    let tail := sig.drop 1
    sign ++ sig.take 1 ++ '.' :: (if tail.isEmpty then ['0'] else tail) ++
      (if single then 'f' else 'e') :: (toString ((ds.length : Int) - 1 - s)).toList
  else
    let padded := List.replicate (s + 1 - ds.length) '0' ++ ds
    let fraction := stripTrailingZeros (padded.drop (padded.length - s))
    sign ++ padded.take (padded.length - s) ++
      '.' :: (if fraction.isEmpty then ['0'] else fraction) ++
      (if single then ['f', '0'] else [])

/-- Decimal rendering of exact terminating decimals, following Julia's decimal
and scientific forms used by `string(val)` at `src/Strings.jl:87-93`. Julia's
shortest-roundtrip digit choice is modelled as exact decimal printing; signed
zero is not modelled. -/
def finiteText (q : Rat) (single : Bool) : String :=
  String.ofList (decimalChars (toDecimal q) single)

/-- Scalar `string` cases used by `src/Strings.jl:87-93`. `print` of a
`Float32` omits the `f0`/`32` suffix, so Float32 values print like Float64. -/
def realText (v : JF) (single : Bool := false) : String :=
  match v with
  | .fin q => finiteText q single
  | .nan => if single then "NaN32" else "NaN"
  | .posInf => if single then "Inf32" else "Inf"
  | .negInf => if single then "-Inf32" else "-Inf"

/-- `string` of a complex value is Julia's `show(io, ::Complex)`: the real part,
` - ` for a negative non-NaN imaginary part (then its negation) and ` + `
otherwise, the imaginary part, `*` before `im` when that part is not finite,
then `im` (`src/Strings.jl:87-93`). -/
def scalarText : Scalar → String
  | .real v => realText v
  | .float32 v => realText v
  | .complex r i =>
      let neg : Bool := match i with | .fin q => decide (q.num < 0) | .negInf => true | _ => false
      realText r ++ (if neg then " - " else " + ") ++ realText (if neg then -i else i) ++
        (match i with | .fin _ => "im" | _ => "*im")

/-- Julia syntax accepted by the slice's defined Meta.parse subset
(`src/Parse.jl:298`). Calls retain argument order and operator symbols.
`dotCall f args` is the dot-call AST `Expr(:., f, Expr(:tuple, args...))` that
`Meta.parse` returns for `f.(args...)`. -/
inductive Surface where
  | literal (v : Scalar)
  | symbol (s : String)
  | call (name : String) (args : List Surface)
  | dotCall (f : String) (args : List Surface)
  | node (tag : String) (value : DynExpr.Tree Scalar)
  | expression
  | unsupported (head : String)
  deriving Repr

def decimalNat (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all Char.isDigit then none
  else some (cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

def decimalInt (cs : List Char) : Option Int := do
  if cs.head? == some '-' then return -(← decimalNat cs.tail! : Nat)
  if cs.head? == some '+' then return (← decimalNat cs.tail! : Nat)
  return (← decimalNat cs : Nat)

/-- Parse signed decimal/scientific/Float32 numeric tokens, modelling the literal
part of `Meta.parse` at `src/Parse.jl:297`. Nonfinite names are symbols. -/
def numericToken (s : String) : Option Scalar := do
  let cs := s.toList
  let single := cs.contains 'f'
  let (mant, expPart) := cs.span (fun c => c != 'e' && c != 'E' && c != 'f')
  let exp : Int ← if expPart.isEmpty then some 0
    else decimalInt expPart.tail!
  let negative := mant.head? == some '-'
  let mant := if mant.head? == some '-' || mant.head? == some '+' then mant.tail! else mant
  let (whole, fract) := mant.span (· != '.')
  let fract := if fract.isEmpty then [] else fract.tail!
  if whole.isEmpty || !(whole ++ fract).all Char.isDigit then none else do
    let n ← decimalNat (whole ++ fract)
    let q : Rat := (if negative then -(n : Rat) else (n : Rat)) / (10 ^ fract.length : Nat)
    let q := if exp ≥ 0 then q * (10 ^ exp.toNat : Nat)
      else q / (10 ^ (-exp).toNat : Nat)
    return if single then .float32 (.fin q) else .real (.fin q)

/-- Tokenizer for parentheses, calls, infix arithmetic, identifiers, and decimal
literals emitted by `src/Strings.jl:106-133`. -/
def lex : Nat → List Char → List String
  | 0, _ => []
  | fuel + 1, cs =>
      match cs with
      | [] => []
      | c :: rest =>
          if c.isWhitespace then lex fuel rest
          else if c.isDigit then
            let (body, rest) := rest.span (fun x => x.isDigit || x == '.')
            let (suffix, rest) := match rest with
              | e :: tail => if e == 'e' || e == 'E' || e == 'f' then
                  let (sign, tail) := match tail with
                    | s :: t => if s == '+' || s == '-' then ([s], t) else ([], tail)
                    | [] => ([], [])
                  let (ns, rs) := tail.span Char.isDigit
                  (e :: sign ++ ns, rs)
                else ([], rest)
              | [] => ([], [])
            String.ofList (c :: body ++ suffix) :: lex fuel rest
          else if c.isAlpha || c == '_' || c.toNat > 127 then
            let (body, rest) := rest.span (fun x => x.isAlphanum || x == '_' || x.toNat > 127)
            String.ofList (c :: body) :: lex fuel rest
          else String.singleton c :: lex fuel rest

private def topPositions (ts : List String) : List (Nat × String) := Id.run do
  let mut depth := 0
  let mut out := []
  for (t, i) in ts.zipIdx do
    if t == "(" then depth := depth + 1
    else if t == ")" then depth := depth - 1
    else if depth == 0 then out := out ++ [(i, t)]
  return out

private def outerParens (ts : List String) : Bool := Id.run do
  if ts.head? != some "(" || ts.getLast? != some ")" then return false
  let mut depth := 0
  for (t, i) in ts.zipIdx do
    if t == "(" then depth := depth + 1
    if t == ")" then depth := depth - 1
    if depth == 0 && i + 1 < ts.length then return false
  return true

private def splitCommas (ts : List String) : List (List String) := Id.run do
  if ts.isEmpty then return []
  let mut start := 0
  let mut result := []
  for (i, t) in topPositions ts do
    if t == "," then
      result := result ++ [(ts.drop start).take (i - start)]
      start := i + 1
  return result ++ [ts.drop start]

private def splitPositions (ts : List String) (positions : List Nat) : List (List String) := Id.run do
  let mut start := 0
  let mut out := []
  for i in positions do
    out := out ++ [(ts.drop start).take (i - start)]
    start := i + 1
  return out ++ [ts.drop start]

/-- Defined parser for emitted Julia syntax. Depth-aware operator splitting uses
Julia arithmetic precedence and right-associative exponentiation. Unary signed
numeric literals become values, as Julia Meta.parse does (`src/Parse.jl:298`).
A token `f` followed by `.(args)` is a dot call; `string_tree` emits this for
identifier-named broadcast callables (`src/Strings.jl:53-66`). -/
def metaParseTokens : Nat → List String → Jl Surface
  | 0, _ => .error (.argumentError "parse depth exhausted")
  | fuel + 1, ts => do
      if ts.isEmpty then throw (.argumentError "empty expression")
      if outerParens ts then return ← metaParseTokens fuel (ts.drop 1 |>.take (ts.length - 2))
      let tops := (topPositions ts).filter (fun p => p.1 > 0 &&
        !( ["+", "-", "*", "/", "^", "(", ","].contains (ts[p.1 - 1]?.getD "")))
      let low := tops.filter (fun p => p.2 == "+" || p.2 == "-")
      let mid := tops.filter (fun p => p.2 == "*" || p.2 == "/")
      let high := tops.filter (fun p => p.2 == "^")
      if low.isEmpty && mid.isEmpty && !high.isEmpty &&
          (ts.head? == some "-" || ts.head? == some "+") then
        return .call (ts.head?.getD "") [← metaParseTokens fuel (ts.drop 1)]
      let split := if !low.isEmpty then low.getLast? else if !mid.isEmpty then mid.getLast? else high.head?
      if let some (i, op) := split then
        if op == "+" || op == "*" then
          let level := if op == "+" then low else mid
          let suffix := level.reverse.takeWhile (fun p => p.2 == op) |>.reverse
          if suffix.length > 1 then
            return .call op (← (splitPositions ts (suffix.map Prod.fst)).mapM (metaParseTokens fuel))
        return .call op [← metaParseTokens fuel (ts.take i), ← metaParseTokens fuel (ts.drop (i + 1))]
      if ts[1]? == some "(" && ts.getLast? == some ")" then
        let args ← (splitCommas (ts.drop 2 |>.take (ts.length - 3))).mapM (metaParseTokens fuel)
        let name := ts.head?.getD ""
        if name == "-" || name == "+" then
          if let [.literal v] := args then
            return .literal (if name == "-" then v.neg else v)
        return .call name args
      if ts.head? == some "-" || ts.head? == some "+" then
        let arg ← metaParseTokens fuel (ts.drop 1)
        return match arg with
          | .literal v => .literal (if ts.head? == some "-" then v.neg else v)
          | _ => .call (ts.head?.getD "") [arg]
      if ts.length == 2 && ts[1]? == some "im" then
        return .call "*" [← metaParseTokens fuel (ts.take 1), .symbol "im"]
      if ts.length == 1 then
        let t := ts.head?.getD ""
        return match numericToken t with
          | some v => .literal v
          | none => .symbol t
      if ts[1]? == some "." && ts[2]? == some "(" && ts.getLast? == some ")" then
        let args ← (splitCommas (ts.drop 3 |>.take (ts.length - 4))).mapM (metaParseTokens fuel)
        return .dotCall (ts.head?.getD "") args
      if ts.head? == some "{" && ts.getLast? == some "}" then return .unsupported "braces"
      if ts.head? == some "[" && ts.getLast? == some "]" then return .unsupported "vect"
      return .unsupported (if ts.contains "." then "." else "syntax")

def metaParse (s : String) : Jl Surface :=
  metaParseTokens (s.length + 1) (lex (s.length + 1) s.toList)

end DynExpr.StringsParse
