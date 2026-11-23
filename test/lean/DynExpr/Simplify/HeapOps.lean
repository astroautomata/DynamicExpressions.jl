import DynExpr.Model.NodeHeap
import DynExpr.Model.Denote
import DynExpr.Runtime.Value

/-!
Node field accessors used by `src/Simplify.jl`, on the heap model of
`src/Node.jl:75-91`. Only active children are stored in a `Cell`; writing a
leaf therefore stores an empty child list, which represents Julia keeping
stale, inactive child slots.
-/

namespace DynExpr.Simplify

/-- `is_node_constant(tree) = tree.degree == 0 && tree.constant`
(src/NodeUtils.jl:36). -/
def cellConst (c : Cell T) : Bool := c.degree == 0 && c.constant

/-- `get_child(n, i)` (src/Node.jl:214-216): one-based access to an active
child. Inactive slots hold poison, whose dereference raises `UndefRefError`
(src/Utils.jl:92). -/
def childAt (c : Cell T) (i : Nat) : Jl Addr :=
  if i = 0 then throw .boundsError
  else match c.children[i - 1]? with
    | some a => pure a
    | none => throw .undefRefError

/-- `get_child(get_child(...))` chains re-read the current object state
(src/Node.jl:214-216). -/
def childOf (g : Graph T) (a : Addr) (i : Nat) : Jl Addr := do
  childAt (← g.read a) i

/-- Reading the `val` field of a node (src/Node.jl:78). An unset field is an
undefined reference. -/
def valOf (g : Graph T) (a : Addr) : Jl T := do
  match (← g.read a).val with
  | some v => pure v
  | none => throw .undefRefError

/-- `is_node_constant` applied to a referenced node (src/NodeUtils.jl:36). -/
def isConstAt (g : Graph T) (a : Addr) : Jl Bool := do
  return cellConst (← g.read a)

/-- `set_child!(n, child, i)` (src/Node.jl:224-227). The tuple has `D = 2`
slots; writing an active slot replaces it, writing an inactive slot
(`i ≤ 2` but beyond the degree) changes nothing observable. -/
def setChild (g : Graph T) (a : Addr) (i : Nat) (b : Addr) : Jl (Graph T) := do
  let c ← g.read a
  if i = 0 ∨ 2 < i then throw .boundsError
  else if i - 1 < c.children.length then
    g.write a { c with children := c.children.set (i - 1) b }
  else pure g

/-- Field assignment `node.val = v` (src/Simplify.jl:69,74,94,101,113,120). -/
def setVal (g : Graph T) (a : Addr) (v : T) : Jl (Graph T) := do
  let c ← g.read a
  g.write a { c with val := some v }

end DynExpr.Simplify
