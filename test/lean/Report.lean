import DynExpr
import DynExpr.Registry.Generality

/-! Print the registry as tab-separated rows: id, status, kind, number of
universally quantified data variables, Julia file, statement, preconditions.

The count unfolds `Prop`-valued definitions from the `DynExpr` namespace (up to
a fixed depth) and counts `∀ x : A` binders anywhere in the statement whose
type `A` is not a proposition. A count of 0 means the property only talks about
fixed concrete inputs. Run with `lake env lean -M8000 Report.lean`. -/

open Lean Meta DynExpr.Registry

#eval show MetaM Unit from do
  for e in DynExpr.Registry.all do
    let status := match e.status with
      | .todo => "todo" | .stuck => "stuck" | .proven => "proven" | .refuted => "refuted"
    let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
    let n ← countForallData 6 (mkConst e.prop)
    let kind := if DynExpr.Registry.staticFacts.contains e.id then "static" else "general"
    IO.println s!"{e.id}\t{status}\t{kind}\t{n}\t{e.juliaFile}\t{clean e.statement}\t{clean e.preconditions}"
