import DynExpr.Deriv.HeapDiff
import DynExpr.Eval.Final
import DynExpr.Eval.Scalars

/-! The forward rule `rrule(::typeof(eval_tree_array), tree, X, operators; kws...)`,
src/ChainRules.jl:33-47, built on the Eval slice's mirror of `eval_tree_array`
(`Eval.evalT`, which tracks whether the output array is freshly allocated or an
`ArrayBuffer` slot). -/

namespace DynExpr.Deriv

@[simp] private theorem rBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem rPure (a : α) : (pure a : Jl α) = .ok a := rfl

/-- The rule on the plain evaluation path: it returns the evaluator's output
array itself (its identity included) and, when the evaluation is incomplete,
`set_invalid!` fills that same array with NaN, src/ChainRules.jl:40-46,
src/Evaluate.jl:275-279, src/Utils.jl:99-102. -/
def rrulePrimal (cx : Eval.Ctx) (o : OpEnum JF) (X : JMat JF) (t : Tree JF) (b : Eval.Buf JF) :
    Jl ((JVec JF × Eval.Ident × Bool) × Eval.Buf JF) := do
  let (r, b') ← Eval.evalT cx o X t b
  let complete := r.ok && (!cx.earlyExit || Eval.isValidArray r.x)
  if complete then pure ((r.x, r.id, true), b')
  else do
    let x ← Eval.setInvalid r.x
    pure ((x, r.id, false), b')

private theorem evalArr_of (cx : Eval.Ctx) (o : OpEnum JF) (X : JMat JF) (t : Tree JF)
    (b : Eval.Buf JF) (r : Eval.ResultOk JF) (b' : Eval.Buf JF)
    (h : Eval.evalT cx o X t b = .ok (r, b')) :
    Eval.evalArr cx o X t b = .ok (r.x, r.ok && (!cx.earlyExit || Eval.isValidArray r.x)) := by
  simp [Eval.evalArr, h]

private theorem rrule_of (cx : Eval.Ctx) (o : OpEnum JF) (X : JMat JF) (t : Tree JF)
    (b : Eval.Buf JF) (r : Eval.ResultOk JF) (b' : Eval.Buf JF)
    (h : Eval.evalT cx o X t b = .ok (r, b')) :
    rrulePrimal cx o X t b = .ok ((if r.ok && (!cx.earlyExit || Eval.isValidArray r.x) then r.x
      else JVec.fill r.x.size .nan, r.id, r.ok && (!cx.earlyExit || Eval.isValidArray r.x)), b') := by
  unfold rrulePrimal
  rw [h]
  simp only [rBind]
  cases hc : (r.ok && (!cx.earlyExit || Eval.isValidArray r.x))
  · simp only [Bool.false_eq_true, ite_false]
    rfl
  · simp only [ite_true, rPure]

/-- For every well-formed tree, operator enum, input matrix, evaluation policy
and fitting buffer (none, a vector-of-slots or a matrix `ArrayBuffer`), the rule
succeeds and returns exactly `eval_tree_array`'s array and completion flag when
complete; when incomplete it returns the same array filled with NaN and
`complete = false`. -/
def failedRuleInvalidates : Prop :=
  ∀ (cx : Eval.Ctx) (o : OpEnum JF) (X : JMat JF) (t : Tree JF) (b : Eval.Buf JF),
    t.WF cx.D o.nops X.nrows → Eval.BufferFits X t b →
    ∃ x0 c x id b', Eval.evalArr cx o X t b = .ok (x0, c) ∧
      rrulePrimal cx o X t b = .ok ((x, id, c), b') ∧
      (c = true → x = x0) ∧ (c = false → x = JVec.fill x0.size .nan)
theorem failedRuleInvalidates_proof : failedRuleInvalidates := by
  intro cx o X t b hw hfit
  obtain ⟨r, b', hr⟩ := Eval.evalT_total cx o X t b hw (Eval.bufOK_of_fits hfit)
  refine ⟨_, _, _, _, _, evalArr_of cx o X t b r b' hr, rrule_of cx o X t b r b' hr, ?_, ?_⟩
  · intro hc; simp [hc]
  · intro hc; simp [hc]

/-- For every well-formed tree, operator enum, input matrix, evaluation policy
and fitting buffer, the rule's primal is the evaluator's output array object
itself, not a copy: without a buffer it is freshly allocated (never `X`), and
with an `ArrayBuffer` it is a slot handed out during this call, which a later
evaluation after `reset_index!` reuses (ArrayBuffer's documented lifetime,
src/Evaluate.jl:34-38). -/
def ruleBorrowedPrimal : Prop :=
  ∀ (cx : Eval.Ctx) (o : OpEnum JF) (X : JMat JF) (t : Tree JF) (b : Eval.Buf JF),
    t.WF cx.D o.nops X.nrows → Eval.BufferFits X t b →
    ∃ r x c b', Eval.evalT cx o X t b = .ok (r, b') ∧
      rrulePrimal cx o X t b = .ok ((x, r.id, c), b') ∧
      (b.isNone = true → r.id = .fresh) ∧
      (b.isNone = false → ∃ k, r.id = .slot k ∧ Eval.Buf.idx b < k ∧ k ≤ Eval.Buf.idx b')
theorem ruleBorrowedPrimal_proof : ruleBorrowedPrimal := by
  intro cx o X t b hw hfit
  obtain ⟨r, b', hr⟩ := Eval.evalT_total cx o X t b hw (Eval.bufOK_of_fits hfit)
  refine ⟨r, _, _, b', hr, rrule_of cx o X t b r b' hr, ?_, ?_⟩
  · intro hn
    cases b with
    | none => exact (Eval.aliasFresh_of_ok cx o X t r b' hr).1
    | mat _ _ => simp [Eval.Buf.isNone] at hn
    | vec _ _ => simp [Eval.Buf.isNone] at hn
  · intro hn
    exact (Eval.aliasSlots_of_ok cx o X t b r b' hn hr).2

end DynExpr.Deriv
