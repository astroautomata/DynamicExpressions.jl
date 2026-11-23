import DynExpr.Model.Denote

/-!
A structurally recursive copy of `Tree.denote` (src/Evaluate.jl:307-411) that
the kernel can evaluate, used to check concrete counterexamples with `decide`.
-/

namespace DynExpr.Simplify

open DynExpr

mutual
  /-- Structural form of `Tree.denote`. -/
  def denS (o : OpEnum T) (x : Nat → Option T) : Tree T → Option T
    | .const v => some v
    | .feature i => x i
    | .branch op cs => do
      let f ← o.lookup cs.length op
      let vs ← denSF o x cs
      pure (f vs)
  /-- Structural form of `cs.mapM (Tree.denote o x)`. -/
  def denSF (o : OpEnum T) (x : Nat → Option T) : List (Tree T) → Option (List T)
    | [] => some []
    | c :: cs => do
      let v ← denS o x c
      let vs ← denSF o x cs
      pure (v :: vs)
end

theorem denSF_eq_mapM (o : OpEnum T) (x : Nat → Option T) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, denS o x c = c.denote o x) :
    denSF o x cs = cs.mapM (Tree.denote o x) := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [denSF, List.mapM_cons]
    rw [ih c (by simp), ihc (fun d hd => ih d (by simp [hd]))]

/-- The structural evaluator agrees with `Tree.denote`. -/
theorem denS_eq (o : OpEnum T) (x : Nat → Option T) (t : Tree T) :
    denS o x t = t.denote o x := by
  induction t using Tree.induction with
  | hc v => simp [denS, Tree.denote]
  | hf i => simp [denS, Tree.denote]
  | hb op cs ih =>
    simp only [denS, Tree.denote]
    rw [denSF_eq_mapM o x cs ih]

end DynExpr.Simplify
