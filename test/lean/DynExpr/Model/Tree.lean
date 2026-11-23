import Std

namespace DynExpr

/-- Unshared expression nodes, modelling `src/Node.jl:74-83`. Indices are one-based. -/
inductive Tree (T : Type) where
  | const (val : T)
  | feature (idx : Nat)
  | branch (op : Nat) (children : List (Tree T))
  deriving Repr

/-- Active child count (`src/Node.jl:76`). -/
def Tree.degree : Tree T → Nat
  | .const _ | .feature _ => 0
  | .branch _ cs => cs.length

/-- Induction over all active children (`src/base.jl:77-158`). -/
theorem Tree.induction {P : Tree T → Prop}
    (hc : ∀ v, P (.const v)) (hf : ∀ i, P (.feature i))
    (hb : ∀ op cs, (∀ c ∈ cs, P c) → P (.branch op cs)) : ∀ t, P t := by
  intro t
  cases t with
  | const v => exact hc v
  | feature i => exact hf i
  | branch op cs =>
    apply hb op cs
    intro c h
    exact Tree.induction hc hf hb c
termination_by t => sizeOf t

/-- Unfolded node count, corresponding to `count_nodes` (`src/base.jl:271-279`). -/
def Tree.size : Tree T → Nat
  | .const _ | .feature _ => 1
  | .branch _ cs => 1 + (cs.map Tree.size).sum

/-- Leaf depth one, corresponding to `count_depth` (`src/NodeUtils.jl:25-29`). -/
def Tree.depth : Tree T → Nat
  | .const _ | .feature _ => 1
  | .branch _ cs => 1 + (cs.map Tree.depth).foldr max 0

/-- Structural and UInt8/UInt16 field constraints (`src/Node.jl:74-83,392-414`). -/
def Tree.WF (D : Nat) (nops : Nat → Nat) (nfeat : Nat) : Tree T → Prop
  | .const _ => True
  | .feature i => 1 ≤ i ∧ i ≤ nfeat ∧ i ≤ 65535
  | .branch op cs =>
    (1 ≤ cs.length ∧ cs.length ≤ D ∧ cs.length ≤ 255) ∧
    (1 ≤ op ∧ op ≤ nops cs.length ∧ op ≤ 255) ∧
    ∀ c ∈ cs, c.WF D nops nfeat

/-- Trees representable by Julia's degree-zero leaf tag (`src/Node.jl:74-83`).
Every branch has at least one child; `Tree.WF` implies this condition. -/
def Tree.Representable : Tree T → Prop
  | .const _ | .feature _ => True
  | .branch _ cs => 0 < cs.length ∧ ∀ c ∈ cs, c.Representable

/-- Well-formed nodes satisfy the Julia leaf/branch representation (`src/Node.jl:392-414`). -/
theorem Tree.WF.representable (t : Tree T) (h : t.WF D nops nf) : t.Representable := by
  induction t using Tree.induction with
  | hc v => simp [Tree.Representable]
  | hf i => simp [Tree.Representable]
  | hb op cs ih =>
    simp only [Tree.WF, Tree.Representable] at *
    exact ⟨by omega, fun c hc => ih c hc (h.2.2 c hc)⟩

/-- Node counts are positive (`src/base.jl:271-279`). -/
theorem Tree.size_pos (t : Tree T) : 0 < t.size := by
  cases t <;> simp [Tree.size] <;> omega

/-- Depth is positive (`src/NodeUtils.jl:25-29`). -/
theorem Tree.depth_pos (t : Tree T) : 0 < t.depth := by
  cases t <;> simp [Tree.depth] <;> omega

/-- Branch node count sums unfolded children (`src/base.jl:77-158`). -/
@[simp] theorem Tree.size_branch (op : Nat) (cs : List (Tree T)) :
    (Tree.branch op cs).size = 1 + (cs.map Tree.size).sum := by simp [Tree.size]

end DynExpr
