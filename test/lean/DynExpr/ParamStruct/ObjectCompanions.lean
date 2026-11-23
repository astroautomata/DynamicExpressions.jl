import DynExpr.ParamStruct.ObjectAliases

namespace DynExpr.ParamStruct

/-- Constant leaf copying of an isbits value keeps the exact value, leaves the
value memory unchanged, and allocates a fresh node identity,
src/ParametricExpression.jl:127-129 and src/ValueInterface.jl:82. -/
def CompositeCopySafe : Prop := ∀ g : Graph Addr, ∀ vm : ValueMemory, ∀ valueObject : Addr,
  ∃ copied, copyCompositeConstant g vm true valueObject = .ok (copied, vm) ∧
    (copied.2.read copied.1).map (fun cell => cell.val) = .ok (some valueObject) ∧
    g.next ≤ copied.1

theorem compositeCopySafe_proven : CompositeCopySafe := by
  intro g vm valueObject
  refine ⟨g.ofTree (.const valueObject), rfl, ?_, Graph.root_ofTree_fresh g (.const valueObject)⟩
  simp [Graph.ofTree, Heap.read, Heap.alloc] <;> rfl

example : (Heap.empty : ValueMemory).alloc [.fin 1] = (0, ((Heap.empty : ValueMemory).alloc [.fin 1]).2) := rfl

end DynExpr.ParamStruct
