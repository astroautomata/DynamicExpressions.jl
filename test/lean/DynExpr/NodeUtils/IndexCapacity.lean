import DynExpr.NodeUtils.GraphIndex
import DynExpr.NodeUtils.CounterAccounting

namespace DynExpr.NodeUtils

/-- src/NodeUtils.jl:186-202: the final constant index is nonzero when the
finite tree has at least one and at most 65535 constant leaves. -/
def PublicIndexCapacity : Prop := ∀ t : Tree Nat,
  t.Representable → 0 < countConstantNodes t → countConstantNodes t ≤ 65535 →
    (indexConstants t 0).2 ≠ 0

theorem publicIndexCapacity_proven : PublicIndexCapacity := by
  intro t _hr hpos hcap
  have h := (indexCounterAccounting t 0 (by decide)).2
  have hc : countConstantNodes t < 65536 := by omega
  simp [Nat.mod_eq_of_lt hc] at h
  rw [h]
  omega

example : (Tree.const (1 : Nat)).Representable ∧
    0 < countConstantNodes (Tree.const (1 : Nat)) ∧
    countConstantNodes (Tree.const (1 : Nat)) ≤ 65535 := by
  simp [Tree.Representable, countConstantNodes]

end DynExpr.NodeUtils
