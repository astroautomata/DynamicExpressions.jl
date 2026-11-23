import DynExpr.NodeUtils
import DynExpr.Registry.Generality

open Lean Meta DynExpr.Registry

#eval show MetaM Unit from do
  let env ← getEnv
  let mut seen : List String := []
  let mut proven := 0
  let mut refuted := 0
  for e in DynExpr.NodeUtils.entries do
    if seen.contains e.id then throwError m!"{e.id}: duplicate identifier"
    seen := e.id :: seen
    let propExpr := mkConst e.prop
    let n ← countForallData 6 propExpr
    if n == 0 then throwError m!"{e.id}: no universally quantified data input"
    let some p := env.find? e.prop | throwError m!"{e.id}: missing property"
    unless p.levelParams.isEmpty do throwError m!"{e.id}: property universe parameters"
    unless ← isProp propExpr do throwError m!"{e.id}: expected Prop"
    let some thm := e.thm | throwError m!"{e.id}: missing theorem"
    let some (.thmInfo ti) := env.find? thm | throwError m!"{e.id}: expected theorem"
    unless ti.levelParams.isEmpty do throwError m!"{e.id}: theorem universe parameters"
    let expected ← match e.status with
      | .proven => proven := proven + 1; pure propExpr
      | .refuted => refuted := refuted + 1; pure (mkNot propExpr)
      | _ => throwError m!"{e.id}: unsettled property"
    unless ← isDefEq ti.type expected do throwError m!"{e.id}: theorem type mismatch"
    for ax in ← collectAxioms thm do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError m!"{e.id}: disallowed dependency {ax}"
    IO.println s!"{e.id}\t{repr e.status}\tgeneral\t{n}\t{e.juliaFile}"
  IO.println s!"SLICE AUDIT OK: {proven} proven, {refuted} refuted, {seen.length} entries"
