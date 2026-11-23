import DynExpr.Model.Denote
import DynExpr.Runtime.Heap

/-!
Model of `src/OperatorEnumConstruction.jl`: building operator tuples from
degree pairs, the global convenience state (`LATEST_OPERATORS`,
`LATEST_OPERATOR_MAPPING`, `ALREADY_DEFINED_OPERATORS`,
`LATEST_VARIABLE_NAMES`), `lookup_op`, and the node-building methods generated
by `@extend_operators`.

Operator functions are identities `Fn`: a plain function or
`Broadcast.BroadcastFunction` of a plain function; their numeric behaviour is
an arbitrary interpretation `I : Fn → List T → T`.
-/

namespace DynExpr.Simplify

open DynExpr

/-- A Julia operator function: `plain n`, or `bcast n` for
`Broadcast.BroadcastFunction(plain n)`. Equality is Julia function identity. -/
inductive Fn where
  | plain (id : Nat)
  | bcast (id : Nat)
  deriving DecidableEq, Repr

/-- `_pairs_to_ops_tuple(pair, pairs...)` (src/OperatorEnumConstruction.jl:409-427).
`ops_array` has `maximum(first, all_pairs)` empty slots; pairs are written in
order, so a repeated degree overwrites the earlier tuple. -/
def pairsToOpsTuple (p : Int × List Fn) (ps : List (Int × List Fn)) : Jl (List (List Fn)) :=
  let maxDeg := ps.foldl (fun m q => max m q.1) p.1
  (p :: ps).foldlM (fun arr q =>
    if q.1 < 1 then throw (.argumentError s!"Degree must be ≥ 1, got {q.1}")
    else pure (arr.set (q.1.toNat - 1) q.2)) (List.replicate maxDeg.toNat [])

/-- Enumeration from a starting index (`enumerate`). -/
def enumFrom : Nat → List α → List (α × Nat)
  | _, [] => []
  | n, a :: as => (a, n) :: enumFrom (n + 1) as

/-- Kind of the latest default enum (`AvailableOperatorTypes`, lines 13-17). -/
inductive EnumKind where
  | operatorEnum
  | genericOperatorEnum
  deriving DecidableEq, Repr

/-- Global convenience state (src/OperatorEnumConstruction.jl:23-32).
`mapping d f` is `LATEST_OPERATOR_MAPPING[d][f]` (missing keys are `none`);
`defined d f` records that a generated node method for `f` with `d`
arguments exists (`ALREADY_DEFINED_OPERATORS`, and Julia method tables);
`varNames` is the vector object referenced by `LATEST_VARIABLE_NAMES`. -/
structure Globals where
  latest : Option (EnumKind × List (List Fn))
  mapping : Nat → Fn → Option Nat
  defined : Nat → Fn → Bool
  varNames : Addr

/-- `_validate_no_ambiguous_broadcasts` (lines 122-134). -/
def validateBroadcasts (ops : List (List Fn)) : Jl Unit :=
  ops.forM fun tup => tup.forM fun op =>
    match op with
    | .bcast n =>
      if ops.any (fun other => other.contains (.plain n)) then
        throw (.argumentError s!"Usage of both broadcasted and unbroadcasted operator is ambiguous")
      else pure ()
    | .plain _ => pure ()

/-- One `(op, func)` step of the registration loop (lines 337-357): record
`func => op` (stored as `UInt8`, so indices above 255 raise `InexactError`),
then define the node methods unless `func` is skipped as a non-`Base` function. -/
def registerOp (inBase : Fn → Bool) (skipUser : Bool) (degree : Nat) (st : Globals)
    (q : Fn × Nat) : Jl Globals :=
  if 255 < q.2 then throw (.errorException "InexactError: UInt8")
  else
    let st := { st with mapping := fun d f =>
      if d = degree ∧ f = q.1 then some q.2 else st.mapping d f }
    if !inBase q.1 && skipUser then pure st
    else pure { st with defined := fun d f => decide (d = degree ∧ f = q.1) || st.defined d f }

/-- Code produced by `_extend_operators` (lines 276-363): validate broadcasts,
optionally empty every degree's mapping, then register every operator.
`skipUser` is true for `@extend_operators_base`. -/
def extendOperators (inBase : Fn → Bool) (skipUser : Bool) (ops : List (List Fn))
    (emptyOld : Bool) (st : Globals) : Jl Globals := do
  validateBroadcasts ops
  let st := if emptyOld then { st with mapping := fun _ _ => none } else st
  (enumFrom 1 ops).foldlM (fun st dq =>
    (enumFrom 1 dq.1).foldlM (registerOp inBase skipUser dq.2) st) st

/-- `OperatorEnum(pairs...; define_helper_functions, empty_old_operators)`
(lines 476-516) and `GenericOperatorEnum(...)` (lines 553-565). Warnings have
no effect on state. Helpers run `@extend_operators_base` and
`set_default_operators!` (lines 88-95). -/
def makeEnum (inBase : Fn → Bool) (kind : EnumKind) (p : Int × List Fn)
    (ps : List (Int × List Fn)) (defineHelpers emptyOld : Bool) (st : Globals) :
    Jl (List (List Fn) × Globals) := do
  let ops ← pairsToOpsTuple p ps
  if defineHelpers then
    let st ← extendOperators inBase true ops emptyOld st
    pure (ops, { st with latest := some (kind, ops) })
  else pure (ops, st)

/-- Deprecated keyword constructors (src/deprecated.jl:95-118):
`OperatorEnum(; binary_operators, unary_operators, kws...)` is
`OperatorEnum(1 => Tuple(something(unary, ())), 2 => Tuple(something(binary, ())); kws...)`. -/
def makeEnumKw (inBase : Fn → Bool) (kind : EnumKind) (binary unary : Option (List Fn))
    (defineHelpers emptyOld : Bool) (st : Globals) : Jl (List (List Fn) × Globals) :=
  makeEnum inBase kind (1, unary.getD []) [(2, binary.getD [])] defineHelpers emptyOld st

/-- `lookup_op(f, Val(degree); allow_failure)` (lines 97-112). -/
def lookupOp (st : Globals) (f : Fn) (degree : Nat) (allowFailure : Bool) : Jl Nat :=
  match st.mapping degree f with
  | some i => pure i
  | none =>
    if allowFailure then pure 0
    else throw (.errorException "Convenience constructor for operator is out-of-date")

/-- `set_default_variable_names!(v)` (lines 82-84): stores and returns a copy
of the vector object `v` (vectors live in a heap of string lists). -/
def setDefaultVariableNames (h : Heap (List String)) (v : Addr) (st : Globals) :
    Jl (Addr × Heap (List String) × Globals) := do
  let names ← h.read v
  let (a, h) := h.alloc names
  pure (a, h, { st with varNames := a })

/-! ### Generated node methods (lines 148-274) on pure trees -/

variable {T : Type}

/-- Generated unary method `f(l::N)` (lines 151-164). -/
def callUnary (I : Fn → List T → T) (st : Globals) (f : Fn) (l : Tree T) : Jl (Tree T) :=
  if !st.defined 1 f then throw (.methodError "no method")
  else match l with
    | .const v => pure (.const (I f [v]))
    | _ => do
      let idx ← lookupOp st f 1 false
      pure (.branch idx [l])

/-- Generated binary method `f(l::N, r::N)` (lines 174-183). -/
def callBinary (I : Fn → List T → T) (st : Globals) (f : Fn) (l r : Tree T) : Jl (Tree T) :=
  if !st.defined 2 f then throw (.methodError "no method")
  else match l, r with
    | .const a, .const b => pure (.const (I f [a, b]))
    | _, _ => do
      let idx ← lookupOp st f 2 false
      pure (.branch idx [l, r])

/-- Generated binary method `f(l::N, r::T)` (lines 184-196). -/
def callBinaryNS (I : Fn → List T → T) (st : Globals) (f : Fn) (l : Tree T) (r : T) :
    Jl (Tree T) :=
  if !st.defined 2 f then throw (.methodError "no method")
  else match l with
    | .const a => pure (.const (I f [a, r]))
    | _ => do
      let idx ← lookupOp st f 2 false
      pure (.branch idx [l, .const r])

/-- Generated binary method `f(l::T, r::N)` (lines 197-209). -/
def callBinarySN (I : Fn → List T → T) (st : Globals) (f : Fn) (l : T) (r : Tree T) :
    Jl (Tree T) :=
  if !st.defined 2 f then throw (.methodError "no method")
  else match r with
    | .const b => pure (.const (I f [l, b]))
    | _ => do
      let idx ← lookupOp st f 2 false
      pure (.branch idx [.const l, r])

/-- Constant value of a constant leaf. -/
def leafConst? : Tree T → Option T
  | .const v => some v
  | _ => none

/-- Generated n-ary method `f(arg1, ..., argn)` for `n = args.length > 2`
(lines 247-271). `chainable` is `f ∈ (+, *)`; when such an `f` has no
`n`-ary mapping, the call is folded through the binary method. -/
def callNary (I : Fn → List T → T) (chainable : Fn → Bool) (st : Globals) (f : Fn)
    (args : List (Tree T)) : Jl (Tree T) :=
  if !st.defined args.length f then throw (.methodError "no method")
  else match args.mapM leafConst? with
    | some vals => pure (.const (I f vals))
    | none => do
      let idx ← lookupOp st f args.length (chainable f)
      if chainable f && idx == 0 then
        match args with
        | a :: rest => rest.foldlM (callBinary I st f) a
        | [] => throw (.methodError "no method")
      else pure (.branch idx args)

/-- Denotational operator enum of an operator tuple list under `I`. -/
def opEnumOf (I : Fn → List T → T) (ops : List (List Fn)) : OpEnum T :=
  ⟨ops.map (·.map I)⟩

end DynExpr.Simplify
