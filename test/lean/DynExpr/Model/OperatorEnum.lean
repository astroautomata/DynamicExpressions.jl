import Std

namespace DynExpr

/-- Per-degree operator tuples (`src/OperatorEnum.jl:14-29`). Functions are total;
callers supply the degree's argument count. -/
structure OpEnum (T : Type) where
  ops : List (List (List T → T))

/-- Operator count for a one-based degree (`src/Evaluate.jl:330-336`). -/
def OpEnum.nops (o : OpEnum T) (d : Nat) : Nat :=
  if d = 0 then 0 else (o.ops[d - 1]?.getD []).length

/-- One-based degree and operator lookup (`src/OperatorEnum.jl:32`). -/
def OpEnum.lookup (o : OpEnum T) (d op : Nat) : Option (List T → T) :=
  if d = 0 ∨ op = 0 then none else (o.ops[d - 1]?.getD [])[op - 1]?

/-- An operator is present exactly inside the one-based bounds (`src/Node.jl:48-53`). -/
theorem OpEnum.lookup_some_iff (o : OpEnum T) (d op : Nat) :
    (∃ f, o.lookup d op = some f) ↔ 1 ≤ op ∧ op ≤ o.nops d := by
  by_cases hd : d = 0
  · simp [lookup, nops, hd] <;> omega
  by_cases ho : op = 0
  · simp [lookup, nops, ho]
  simp only [lookup, nops, hd, ho, or_self, ↓reduceIte, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨f, h, _⟩
    omega
  · intro h
    exact ⟨_, by omega, rfl⟩
end DynExpr
