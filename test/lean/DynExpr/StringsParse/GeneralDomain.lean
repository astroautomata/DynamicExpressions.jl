import DynExpr.StringsParse.Properties

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 200000

/-- Parseable identifiers emitted by src/Strings.jl:95-103. -/
def identifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_' || c.toNat > 127) &&
    cs.all (fun c => c.isAlphanum || c == '_' || c.toNat > 127)
def goodNames (names : List String) : Bool :=
  names.length ≤ 65535 && decide names.Nodup && names.all identifier
def renderer (ops : Operators) (names : List String) : RenderConfig :=
  {operators := some ops, names := some names}
def parser (ops : Operators) (names : List String) : ParseConfig :=
  {operators := ops, names := some names}
def renderParse (ops : Operators) (names : List String) (t : Tree Scalar) : Option ParsedNode := do
  let text ← (stringTree (renderer ops names) t).toOption
  (parseString (parser ops names) text).toOption

theorem testNames : goodNames ["x1", "x2"] = true := by decide +kernel

end DynExpr.StringsParse.General
