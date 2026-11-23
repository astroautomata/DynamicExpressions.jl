import DynExpr.Model.OperatorEnum
import DynExpr.Runtime.Errors

namespace DynExpr.NodeUtils

/-- src/OperatorEnum.jl:5,14-29: the two concrete kinds share their tuple API. -/
inductive AbstractOperatorEnum (T : Type) where
  | typed (ops : OpEnum T)
  | generic (ops : OpEnum T)

def enumOps : AbstractOperatorEnum T → OpEnum T
  | .typed o | .generic o => o

/-- src/OperatorEnum.jl:31 copies the immutable wrapper without cloning closures. -/
def copyEnum (o : AbstractOperatorEnum T) := o

/-- src/OperatorEnum.jl:34-36 is checked one-based tuple indexing. -/
def enumGet (o : AbstractOperatorEnum T) (i : Nat) : Jl (List (List T → T)) :=
  if i = 0 then .error .boundsError
  else match (enumOps o).ops[i - 1]? with
    | some ops => .ok ops
    | none => .error .boundsError

/-- src/OperatorEnum.jl:37-39 counts degree tuples, including empty tuples. -/
def enumLength (o : AbstractOperatorEnum T) := (enumOps o).ops.length

/-- src/OperatorEnum.jl:40-45: unary indexing throws on an empty enum;
binary access returns an empty tuple when the second degree is absent. -/
def unaops (o : AbstractOperatorEnum T) := enumGet o 1

def binops (o : AbstractOperatorEnum T) : List (List T → T) :=
  if enumLength o > 1 then (enumOps o).ops[1]?.getD [] else []

def EnumIndex : Prop := ∀ (o : AbstractOperatorEnum Nat) i fs,
  (enumOps o).ops[i]? = some fs → enumGet o (i + 1) = .ok fs

theorem enumIndex_proven : EnumIndex := by
  intro o i fs h; simp [enumGet, h]

example : (enumOps (AbstractOperatorEnum.typed (OpEnum.mk [[]] : OpEnum Nat))).ops[0]? = some [] := rfl

def EnumLength : Prop := ∀ o : AbstractOperatorEnum Nat,
  enumLength o = (enumOps o).ops.length

theorem enumLength_proven : EnumLength := by intro o; rfl

def EnumCopy : Prop := ∀ o : AbstractOperatorEnum Nat, copyEnum o = o

theorem enumCopy_proven : EnumCopy := by intro o; rfl

def EnumDegreeProperties : Prop := ∀ o : AbstractOperatorEnum Nat,
  unaops o = (match (enumOps o).ops with | [] => .error .boundsError | fs :: _ => .ok fs) ∧
  binops o = (enumOps o).ops[1]?.getD []

theorem enumDegreeProperties_proven : EnumDegreeProperties := by
  intro o
  cases h : (enumOps o).ops with
  | nil => simp [unaops,enumGet,binops,enumLength,h]
  | cons fs rest =>
      cases rest with
      | nil => simp [unaops,enumGet,binops,enumLength,h]
      | cons bs tail => simp [unaops,enumGet,binops,enumLength,h]

end DynExpr.NodeUtils
