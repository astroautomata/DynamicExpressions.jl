import DynExpr.ParamStruct
import DynExpr.Registry.Generality

open Lean Meta DynExpr.Registry

/- Report this slice using the same measurement and columns as test/lean/Report.lean. -/
#eval show MetaM Unit from do
  for e in DynExpr.ParamStruct.entries do
    let status := match e.status with
      | .todo => "todo" | .stuck => "stuck" | .proven => "proven" | .refuted => "refuted"
    let clean (s : String) := (s.replace "\t" " ").replace "\n" " "
    let count ← countForallData 6 (mkConst e.prop)
    if count = 0 then throwError "worked-example property {e.id}"
    IO.println s!"{e.id}\t{status}\tgeneral\t{count}\t{e.juliaFile}\t{clean e.statement}"
