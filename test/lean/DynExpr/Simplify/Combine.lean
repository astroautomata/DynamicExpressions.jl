import DynExpr.Simplify.HeapOps

/-!
Mirror of `combine_operators!(tree::AbstractExpressionNode{T,2}, operators)` (src/Simplify.jl:32-126).
Binary operators are tagged so that `is_commutative` (`+`, `*`) and
`is_subtraction` (`-`) can recognise the concrete Julia functions
(src/Simplify.jl:21-26); any other operator is an arbitrary function.
-/

namespace DynExpr.Simplify

open DynExpr

/-- A binary operator: Julia's `+`, `*`, `-`, or any other function. -/
inductive BinOp (T : Type) where
  | plus
  | times
  | minus
  | other (f : T → T → T)

/-- Calling the binary operator (`_op_kernel`, src/Simplify.jl:18). -/
def BinOp.eval [Add T] [Mul T] [Sub T] : BinOp T → T → T → T
  | .plus, a, b => a + b
  | .times, a, b => a * b
  | .minus, a, b => a - b
  | .other f, a, b => f a b

/-- `is_commutative` (src/Simplify.jl:21-23). -/
def BinOp.isComm : BinOp T → Bool
  | .plus | .times => true
  | _ => false

/-- `is_subtraction` (src/Simplify.jl:25-26). -/
def BinOp.isSub : BinOp T → Bool
  | .minus => true
  | _ => false

/-- Operator enum with unary and binary tuples (`OperatorEnum`, src/OperatorEnum.jl:14-16). -/
structure CEnum (T : Type) where
  una : List (T → T)
  bin : List (BinOp T)

/-- The enum as a denotational `OpEnum` (degree 1 then degree 2). -/
def CEnum.toOpEnum [Add T] [Mul T] [Sub T] [Inhabited T] (o : CEnum T) : OpEnum T :=
  ⟨[o.una.map (fun f xs => f xs[0]!), o.bin.map (fun b xs => b.eval xs[0]! xs[1]!)]⟩

/-- `operators.binops[op]` (src/OperatorEnum.jl:44-46): out of range is a `BoundsError`. -/
def CEnum.binop (o : CEnum T) (op : Nat) : Jl (BinOp T) :=
  if op = 0 then throw .boundsError
  else match o.bin[op - 1]? with
    | some b => pure b
    | none => throw .boundsError

variable [Add T] [Mul T] [Sub T]

/-- Commutative block (src/Simplify.jl:54-79). Returns the possibly replaced
subtree root (`tree = below`, lines 68 and 73). -/
def commBlock (o : CEnum T) (g : Graph T) (tree : Addr) : Jl (Addr × Graph T) := do
  let c ← g.read tree
  let op := c.op
  -- Lines 58-62: put the constant on the right.
  let g ← if ← isConstAt g (← childAt c 1) then do
      let tmp ← childOf g tree 2
      let g ← setChild g tree 2 (← childOf g tree 1)
      setChild g tree 1 tmp
    else pure g
  let topconstant ← valOf g (← childOf g tree 2)
  let below ← childOf g tree 1
  let bc ← g.read below
  if bc.degree = 2 ∧ bc.op = op then
    let b1 ← childAt bc 1
    if ← isConstAt g b1 then
      -- Lines 68-71.
      let f ← o.binop op
      let g ← setVal g b1 (f.eval (← valOf g b1) topconstant)
      return (below, g)
    else
      let b2 ← childAt bc 2
      if ← isConstAt g b2 then
        -- Lines 73-76.
        let f ← o.binop op
        let g ← setVal g b2 (f.eval (← valOf g b2) topconstant)
        return (below, g)
      else return (tree, g)
  else return (tree, g)

/-- Subtraction block (src/Simplify.jl:85-123), using Julia's `-` and `+` on values. -/
def subBlock (g : Graph T) (tree : Addr) : Jl (Addr × Graph T) := do
  let c ← g.read tree
  let l ← childAt c 1
  if ← isConstAt g l then
    let r ← childAt c 2
    let rc ← g.read r
    if rc.degree = 2 ∧ c.op = rc.op then
      if ← isConstAt g (← childAt rc 1) then
        -- Lines 88-94: (const - (const - var)) => (var - const)
        let simplified := (← valOf g (← childAt rc 1)) - (← valOf g l)
        let g ← setChild g tree 1 (← childOf g (← childOf g tree 2) 2)
        let g ← setChild g tree 2 l
        let g ← setVal g (← childOf g tree 2) simplified
        return (tree, g)
      else if ← isConstAt g (← childAt rc 2) then
        -- Lines 96-101: (const - (var - const)) => (const - var)
        let simplified := (← valOf g l) + (← valOf g (← childAt rc 2))
        let g ← setChild g tree 2 (← childOf g (← childOf g tree 2) 1)
        let g ← setVal g (← childOf g tree 1) simplified
        return (tree, g)
      else return (tree, g)
    else return (tree, g)
  else
    let r ← childAt c 2
    let lc ← g.read l
    if lc.degree = 2 ∧ c.op = lc.op then
      if ← isConstAt g (← childAt lc 1) then
        -- Lines 107-113: ((const - var) - const) => (const - var)
        let simplified := (← valOf g (← childAt lc 1)) - (← valOf g r)
        let g ← setChild g tree 2 (← childOf g (← childOf g tree 1) 2)
        let g ← setChild g tree 1 r
        let g ← setVal g (← childOf g tree 1) simplified
        return (tree, g)
      else if ← isConstAt g (← childAt lc 2) then
        -- Lines 115-120: ((var - const) - const) => (var - const)
        let simplified := (← valOf g r) + (← valOf g (← childAt lc 2))
        let g ← setChild g tree 1 (← childOf g (← childOf g tree 1) 1)
        let g ← setVal g (← childOf g tree 2) simplified
        return (tree, g)
      else return (tree, g)
    else return (tree, g)

/-- Local rewrites after the children were combined (src/Simplify.jl:51-125). -/
def rewrite (o : CEnum T) (g : Graph T) (tree0 : Addr) : Jl (Addr × Graph T) := do
  let c ← g.read tree0
  -- Lines 51-53 (short-circuit `&&`/`||`).
  let tlc ← if c.degree = 2 then do
      if ← isConstAt g (← childAt c 1) then pure true
      else isConstAt g (← childAt c 2)
    else pure false
  -- Line 54: `tree.degree == 2 && is_commutative(binops[tree.op]) && top_level_constant`.
  let (tree, g) ← if c.degree = 2 then do
      let b ← o.binop c.op
      if b.isComm && tlc then commBlock o g tree0 else pure (tree0, g)
    else pure (tree0, g)
  -- Line 81, evaluated on the possibly replaced `tree`.
  let c ← g.read tree
  if c.degree = 2 then
    let b ← o.binop c.op
    if b.isSub && tlc then subBlock g tree else pure (tree, g)
  else pure (tree, g)

/-- `combine_operators!(tree::AbstractExpressionNode{T,2}, operators)`
(src/Simplify.jl:32-126) for node types that do not preserve sharing (`Node`,
`ParametricNode`; `GraphNode` returns at line 35 and is not modelled here):
recursively combine children (lines 42-49), storing each returned subtree root
with `set_child!`, then apply the local rewrites. Returns the possibly
different root. A `ParametricNode` parameter leaf is a non-constant leaf that
the rewrites never read or write, so it is modelled as a feature leaf. `fuel`
bounds recursion depth (a model artifact). -/
def combineOps (o : CEnum T) : Nat → Graph T → Addr → Jl (Addr × Graph T)
  | 0, _, _ => throw (.errorException "model recursion fuel exhausted")
  | fuel + 1, g, tree => do
    let c ← g.read tree
    if c.degree = 0 then return (tree, g)
    let g ← if c.degree = 1 then do
        let (r, g) ← combineOps o fuel g (← childAt c 1)
        setChild g tree 1 r
      else if c.degree = 2 then do
        let (r1, g) ← combineOps o fuel g (← childAt c 1)
        let g ← setChild g tree 1 r1
        let (r2, g) ← combineOps o fuel g (← childOf g tree 2)
        setChild g tree 2 r2
      else pure g
    rewrite o g tree

/-- The deprecated `combine_operators(tree, operators)` (src/Simplify.jl:128):
`Base.@deprecate` defines it as a call of `combine_operators!(tree, operators)`.
The deprecation warning it emits under `--depwarn=yes` is not modelled (under
`--depwarn=error` the call throws instead). -/
def combineOperatorsDeprecated (o : CEnum T) (fuel : Nat) (g : Graph T) (tree : Addr) :
    Jl (Addr × Graph T) :=
  combineOps o fuel g tree

end DynExpr.Simplify
