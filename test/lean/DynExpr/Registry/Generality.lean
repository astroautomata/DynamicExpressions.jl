import Lean

/-! Generality measure used by `Audit.lean` and `Report.lean`. -/

namespace DynExpr.Registry

open Lean Meta

/-- Number of `∀ x : A` binders with non-`Prop` type `A` anywhere in a
statement, unfolding `Prop`-valued definitions from the `DynExpr` namespace up
to `depth` levels. Zero means the statement only concerns fixed concrete
inputs. -/
partial def countForallData (depth : Nat) (e : Expr) : MetaM Nat := do
  match e with
  | .forallE n ty body bi =>
    let here := if (← isProp ty) then 0 else 1
    let tyCount ← countForallData depth ty
    withLocalDecl n bi ty fun x => do
      return here + tyCount + (← countForallData depth (body.instantiate1 x))
  | .lam n ty body bi =>
    withLocalDecl n bi ty fun x => countForallData depth (body.instantiate1 x)
  | .mdata _ b => countForallData depth b
  | .letE n ty v b _ =>
    withLetDecl n ty v fun x => countForallData depth (b.instantiate1 x)
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut total := 0
    for a in args do total := total + (← countForallData depth a)
    if let .const c _ := fn then
      if depth > 0 && (`DynExpr).isPrefixOf c then
        if let some (.defnInfo _) := (← getEnv).find? c then
          if (← isProp e) then
            if let some e' ← unfoldDefinition? e then
              total := total + (← countForallData (depth - 1) e')
    return total
  | .const c _ =>
    if depth > 0 && (`DynExpr).isPrefixOf c then
      if let some (.defnInfo info) := (← getEnv).find? c then
        if (← isProp e) then return ← countForallData (depth - 1) info.value
    return 0
  | _ => return 0

end DynExpr.Registry
