import DynExpr.Model.Tree
import DynExpr.Model.OperatorEnum
import DynExpr.Runtime.Array

namespace DynExpr

/-- Scalar expression evaluation with left-to-right child traversal (`src/Evaluate.jl:338-439`). -/
def Tree.denote (o : OpEnum T) (x : Nat → Option T) : Tree T → Option T
  | .const v => some v
  | .feature i => x i
  | .branch op cs => do
    let f ← o.lookup cs.length op
    let vs ← cs.mapM (Tree.denote o x)
    pure (f vs)

/-- Evaluate sample column `j` of a features-by-samples matrix (`src/Evaluate.jl:280-310`). -/
def Tree.denoteRow (o : OpEnum T) (X : JMat T) (j : Nat) : Tree T → Option T :=
  Tree.denote o (fun f => (X.get? f j).toOption)

/-- Total option traversal when every child is defined (`src/base.jl:123-158`). -/
theorem Tree.mapM_some {f : α → Option β} (xs : List α)
    (h : ∀ a ∈ xs, ∃ b, f a = some b) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨bs, hbs⟩ := ih (by intro a ha; exact h a (by simp [ha]))
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs]⟩

/-- Well-formed trees evaluate whenever all feature bindings exist (`src/Node.jl:392-414`). -/
theorem Tree.denote_some (o : OpEnum T) (x : Nat → Option T)
    (hx : ∀ i, 1 ≤ i → i ≤ nf → ∃ v, x i = some v)
    (t : Tree T) (hw : t.WF D o.nops nf) : ∃ v, t.denote o x = some v := by
  induction t using Tree.induction with
  | hc v => exact ⟨v, by simp [Tree.denote]⟩
  | hf i =>
    simp only [Tree.WF] at hw
    simpa [Tree.denote] using hx i hw.1 hw.2.1
  | hb op cs ih =>
    simp only [Tree.WF] at hw
    obtain ⟨f, hf⟩ := (o.lookup_some_iff cs.length op).2 ⟨hw.2.1.1, hw.2.1.2.1⟩
    obtain ⟨vs, hvs⟩ := Tree.mapM_some cs (by intro c hc; exact ih c hc (hw.2.2 c hc))
    exact ⟨f vs, by simp [Tree.denote, hf, hvs]⟩

/-- Each valid sample column defines the denotation (`src/Evaluate.jl:280-310`). -/
theorem Tree.denoteRow_some (o : OpEnum T) (X : JMat T) (j : Nat)
    (hj : 1 ≤ j ∧ j ≤ X.ncols) (t : Tree T) (hw : t.WF D o.nops X.nrows) :
    ∃ v, t.denoteRow o X j = some v := by
  apply Tree.denote_some o _ _ t hw
  intro i hi hir
  obtain ⟨v, hv⟩ := X.get?_exists i j hi hir hj.1 hj.2
  exact ⟨v, by rw [hv]; rfl⟩

end DynExpr
