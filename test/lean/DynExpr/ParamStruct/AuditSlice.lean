import DynExpr.ParamStruct
import DynExpr.Registry.Generality

open Lean Meta

/- Check this slice without requiring unfinished sibling modules. The checks
match the registry contract in test/lean/ARCHITECTURE.md and test/lean/Audit.lean. -/
#eval show MetaM Unit from do
  let env ← getEnv
  let entries := DynExpr.ParamStruct.entries
  let mut seen : Std.HashSet String := {}
  let mut proven := 0
  let mut refuted := 0
  for e in entries do
    if seen.contains e.id then throwError "duplicate id {e.id}"
    seen := seen.insert e.id
    unless e.status == .proven || e.status == .refuted do
      throwError "unsettled property {e.id}"
    let some propInfo := env.find? e.prop
      | throwError "missing property {e.prop}"
    unless propInfo.levelParams.isEmpty do throwError "polymorphic property {e.prop}"
    let propExpr := mkConst e.prop
    unless ← isProp propExpr do throwError "property is not Prop: {e.prop}"
    let quantifiers ← DynExpr.Registry.countForallData 6 propExpr
    if quantifiers = 0 then throwError "worked-example property {e.id}"
    IO.println s!"GENERAL {e.id} {quantifiers}"
    let some thm := e.thm | throwError "missing proof for {e.id}"
    let some (.thmInfo thmInfo) := env.find? thm
      | throwError "missing theorem {thm}"
    unless thmInfo.levelParams.isEmpty do throwError "polymorphic theorem {thm}"
    let expected := if e.status == .proven then propExpr else mkNot propExpr
    unless ← isDefEq thmInfo.type expected do throwError "wrong theorem type for {e.id}"
    for ax in ← collectAxioms thm do
      unless ([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains ax do
        throwError "unexpected proof assumption {ax} for {e.id}"
    if e.status == .proven then proven := proven + 1
    else
      refuted := refuted + 1
      IO.println s!"REFUTED {e.id}"
  IO.println s!"PARAMSTRUCT AUDIT OK: {proven} proven, {refuted} refuted, {entries.length} entries"
