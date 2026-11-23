import DynExpr.Plumbing
import DynExpr.Registry.Generality

open Lean Meta DynExpr.Registry

-- Same six-level quantifier counter as Report.lean, scoped to this slice.
#eval show MetaM Unit from do
  for e in DynExpr.Plumbing.entries do
    let n ← countForallData 6 (mkConst e.prop)
    IO.println s!"{e.id}\t{repr e.status}\t{n}"
