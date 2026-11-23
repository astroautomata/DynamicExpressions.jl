import DynExpr.Deriv.Properties

namespace DynExpr.Deriv

@[simp] private theorem jlBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem jlPure (a : α) : (pure a : Jl α) = .ok a := rfl
@[simp] private theorem jlMap (a : α) (f : α → β) :
    (Except.ok a : Jl α).map f = .ok (f a) := rfl

/-- Leaf equations of the gradient traversal. -/
theorem gradTree_const (s m o X ng start v) :
    gradTree s m o X ng start (.const v) =
      (grad_deg0_eval s m X.nrows ng (List.replicate X.ncols v) true (start % 65536)).map
        checkResult := by
  simp only [gradTree]

theorem gradTree_feature (s m o X ng start k) :
    gradTree s m o X ng start (.feature k) = (do
      let vals ← X.row k
      (grad_deg0_eval s m X.nrows ng vals.toList false k).map checkResult) := by
  simp only [gradTree]

/-- Branch equation of the gradient traversal. -/
theorem gradTree_branch (s m o X ng start idx cs) :
    gradTree s m o X ng start (.branch idx cs) = (do
      let rs ← collectChildren (gradTreeList s m o X ng start cs)
      match firstIncomplete rs with
      | some r => pure r
      | none =>
          match o.lookup cs.length idx with
          | none => .error (.undefinedBehavior "generated operator dispatch has no matching arm")
          | some op => (gradKernel op X.ncols rs).map checkResult) := by
  simp only [gradTree]
  rfl

/-- One feature, two samples, as `view(ones(1, 2), :, :)`. -/
def twoSampleOnes : JMat JF := ⟨1, 2, #[one, one], by decide⟩

end DynExpr.Deriv
