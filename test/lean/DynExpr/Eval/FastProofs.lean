import DynExpr.Eval.Top

/-!
Correctness of the positional fast evaluation helpers `_eval_tree_array_fast`
and `apply_op_array` (`src/Evaluate.jl:260-271, 381-400`).
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- `_eval_tree_array_fast` agrees identically with `eval_tree_array` whenever
`turbo = false`, unconditionally (including errors, early exit, buffers, and
non-finite values). -/
def evalFastAgree : Prop :=
  ∀ (T : Type) [JlScalar T] (ext : Ext) (impl : ExtImpl T) (D : Nat) (t : Tree T)
    (X : JMat T) (o : OpEnum T) (ec : EvalContext T),
    ec.turbo = false →
    evalTreeArrayFast D t X o ec = evalTreeArray ext impl D t X o ec

theorem evalFastAgree_proof : evalFastAgree := by
  intro T _ ext impl D t X o ec ht
  simp [evalTreeArrayFast, evalTreeArray, ht]

example : (plainCtx true true (.none : Buf JF)).turbo = false := rfl

/-- `degnEval` on equal-length cumulators computes the operator elementwise. -/
private theorem degnEval_eq_len (f : List T → T) (n : Nat) (cums : List (JVec T))
    (hne : cums ≠ []) (hsz : ∀ c ∈ cums, c.size = n) :
    degnEval f cums =
      .ok ((List.range n).map (fun j => f (cums.map (fun c => c.getD j JlScalar.undef)))).toArray := by
  cases cums with
  | nil => exact absurd rfl hne
  | cons c1 cs =>
    have hc1 : c1.size = n := hsz c1 (by simp)
    have hinner : ∀ j, j < n →
        (c1 :: cs).mapM (fun a => getInb a j) =
          .ok ((c1 :: cs).map (fun a => a.getD j JlScalar.undef)) := by
      intro j hj
      exact mapM_jl_eq (fun a => getInb a j) (fun a => a.getD j JlScalar.undef) (c1 :: cs) (by
        intro a ha
        have hasz : j < a.size := by rw [hsz a ha]; exact hj
        simp [getInb, hasz, Array.getD])
    have hm := mapM_jl_eq
      (fun j => do
        let args ← (c1 :: cs).mapM (fun a => getInb a j)
        pure (f args))
      (fun j => f ((c1 :: cs).map (fun a => a.getD j JlScalar.undef))) (List.range n) (by
        intro j hj
        have hj' : j < n := by simpa using hj
        show ((c1 :: cs).mapM (fun a => getInb a j) >>= fun args => pure (f args)) = _
        rw [hinner j hj']
        rfl)
    simp only [degnEval, hc1]
    rw [hm]
    rfl

/-- `apply_op_array` looks up `operators[D][op_idx]` (whether `nops ≤ 15` via
`@nif` or `nops > 15` via direct indexing) and applies `degn_eval` elementwise. -/
def applyOpArrayDenote : Prop :=
  ∀ (T : Type) [JlScalar T] (o : OpEnum T) (op n : Nat) (cums : List (JVec T)),
    1 ≤ cums.length → 1 ≤ op → op ≤ o.nops cums.length →
    (∀ c ∈ cums, c.size = n) →
    ∃ g, o.lookup cums.length op = some g ∧
      applyOpArray o op cums =
        .ok ((List.range n).map (fun j => g (cums.map (fun c => c.getD j JlScalar.undef)))).toArray

theorem applyOpArrayDenote_proof : applyOpArrayDenote := by
  intro T _ o op n cums hlen hop1 hop2 hsz
  obtain ⟨g, hg, hnif⟩ := nifOp_lookup o cums.length op hlen hop1 hop2
  have hne : cums ≠ [] := by intro h; simp [h] at hlen
  have hpos : (opsOf o cums.length).length ≠ 0 := by
    have hle : op ≤ (opsOf o cums.length).length := by
      simpa [OpEnum.nops, opsOf, show cums.length ≠ 0 by omega] using hop2
    omega
  refine ⟨g, hg, ?_⟩
  unfold applyOpArray
  simp only [hpos, decide_false, Bool.false_or]
  by_cases hlim : operatorLimit < (opsOf o cums.length).length
  · simp only [hlim, decide_true, ↓reduceIte, idxOp_lookup o cums.length op g hlen hg, jl_ok_bind]
    exact degnEval_eq_len g n cums hne hsz
  · simp only [hlim, decide_false, Bool.false_eq_true, ↓reduceIte, hnif, jl_ok_bind]
    exact degnEval_eq_len g n cums hne hsz

example :
    let o : OpEnum JF := ⟨[[], [fun xs => match xs with | [a, b] => JF.add a b | _ => .nan]]⟩
    let cums : List (JVec JF) := [#[.fin 1, .fin 2], #[.fin 3, .fin 4]]
    1 ≤ cums.length ∧ 1 ≤ 1 ∧ 1 ≤ o.nops cums.length ∧ (∀ c ∈ cums, c.size = 2) := by
  simp [OpEnum.nops]

end DynExpr.Eval
