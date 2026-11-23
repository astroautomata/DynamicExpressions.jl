import Lean

/-!
Property registry types.

Every correctness property of DynamicExpressions.jl is a closed `Prop` constant
(`prop`). A `proven` entry names a theorem whose type is exactly `prop`; a
`refuted` entry names a theorem whose type is exactly `¬ prop` and a Julia
reproducer script. `Audit.lean` checks these types, the axioms each theorem
depends on, and coverage of the Julia sources.
-/

namespace DynExpr.Registry

inductive Status where
  /-- Not yet settled. The audit fails while any entry is open. -/
  | todo
  /-- Hit the per-property attempt cap without being settled. -/
  | stuck
  | proven
  | refuted
  deriving Repr, BEq, DecidableEq


structure Entry where
  /-- Unique identifier, also used to name the reproducer `test/lean/repro/<id>.jl`. -/
  id : String
  /-- Julia source file this property is about, e.g. `src/Evaluate.jl`. -/
  juliaFile : String
  /-- Julia functions (exported or internal) the property covers. -/
  juliaFns : List String
  /-- Informal statement of the property. -/
  statement : String
  /-- Reasonable-input preconditions, stated informally; the Lean `prop` encodes them. -/
  preconditions : String
  status : Status
  /-- Closed `Prop` constant stating the property. -/
  prop : Lean.Name
  /-- Theorem proving `prop` (proven) or `¬ prop` (refuted). -/
  thm : Option Lean.Name := none
  /-- Notes, e.g. attempt log for stuck entries or the bug description. -/
  notes : String := ""

end DynExpr.Registry
