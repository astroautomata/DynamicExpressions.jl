import DynExpr.Deriv.ChainRules

namespace DynExpr.Deriv

@[simp] private theorem jlPure (a : α) : (pure a : Jl α) = .ok a := rfl
@[simp] private theorem jlBind (a : α) (f : α → Jl β) :
    (Except.ok a >>= f : Jl β) = f a := rfl
@[simp] private theorem jlMap (a : α) (f : α → β) :
    (Except.ok a : Jl α).map f = .ok (f a) := rfl
@[simp] private theorem jfMul (a b : JF) : a * b = JF.mul a b := rfl
@[simp] private theorem jfAdd (a b : JF) : a + b = JF.add a b := rfl
@[simp] private theorem ratMul (a b : Rat) : a * b = Rat.mul a b := rfl
@[simp] private theorem ratAdd (a b : Rat) : a + b = Rat.add a b := rfl


private theorem mapM_congr_mem {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mapM_cons]
    rw [h a (by simp), ih (by intro a ha; exact h a (by simp [ha]))]

def directionalChainRule : Prop :=
  ∀ o x direction t, diffScalar o x direction t = t.denoteDeriv o x direction

theorem directionalChainRule_proof : directionalChainRule := by
  intro o x direction t
  induction t using Tree.induction with
  | hc v => simp [diffScalar, Tree.denoteDeriv]
  | hf k => cases hx : x k <;> simp [diffScalar, Tree.denoteDeriv, hx]
  | hb idx cs ih =>
    simp only [diffScalar, Tree.denoteDeriv]
    rw [mapM_congr_mem cs _ _ ih]
    rfl

def featureDerivative : Prop :=
  ∀ o x k direction v, x k = some v →
    diffScalar o x direction (.feature k) = some (v, if k = direction then one else zero)
theorem featureDerivative_proof : featureDerivative := by
  intro o x k d v h
  simp [diffScalar, h]
example : diffScalar ⟨[]⟩ (fun _ => some one) 1 (.feature 1) = some (one, one) := by simp [diffScalar]

def constantDerivative : Prop :=
  ∀ o x direction v, diffScalar o x direction (.const v) = some (v, zero)
theorem constantDerivative_proof : constantDerivative := by
  unfold constantDerivative
  intros
  simp [diffScalar]

/-- Concrete + and * with their Zygote gradients, src/EvaluateDerivative.jl:111-117. -/
def addOp : DOp := ⟨addTerms, fun _ _ => one⟩
def mulOp : DOp := ⟨fun xs => xs[0]! * xs[1]!,
  fun i xs => if i = 0 then xs[1]! else xs[0]!⟩
def arithmetic : DEnum := ⟨[[], [addOp, mulOp]]⟩
def affine : Tree JF := .branch 1 [.branch 2 [.feature 1, .const (.fin 2)], .const (.fin 5)]

private theorem nifSelect_get (idx : Nat) :
    ∀ (ops : List DOp) (i : Nat), i ≤ idx → idx < i + ops.length →
      nifSelect idx i ops = ops[idx - i]? := by
  intro ops
  induction ops with
  | nil => intro i _ h; simp at h; omega
  | cons op rest ih =>
    intro i h1 h2
    cases rest with
    | nil =>
      simp at h2
      have : idx - i = 0 := by omega
      simp [nifSelect, this]
    | cons op' rest' =>
      simp only [nifSelect]
      by_cases he : idx = i
      · subst he; simp
      · simp only [he, ite_false]
        rw [ih (i + 1) (by omega) (by simp at h2 ⊢; omega)]
        have : idx - i = (idx - (i + 1)) + 1 := by omega
        rw [this]
        rfl

/-- For every operator enum, degree and in-range operator index, the generated
dispatch (the `@nif` chain for at most 15 operators, `operators[degree][op_idx]`
above) selects the operator that `DEnum.lookup` returns, which the gradient and
directional mirrors use. -/
def generatedDispatch : Prop :=
  ∀ (o : DEnum) (degree idx : Nat), 1 ≤ degree → 1 ≤ idx → idx ≤ o.nops degree →
    generatedOp o degree idx = o.lookup degree idx
theorem generatedDispatch_proof : generatedDispatch := by
  intro o degree idx hd h1 h2
  unfold DEnum.nops at h2
  have hd0 : ¬ degree = 0 := by omega
  have hi0 : ¬ idx = 0 := by omega
  simp only [generatedOp, DEnum.lookup, hd0, hi0, or_self, ite_false]
  by_cases hbig : 15 < (o.ops[degree - 1]?.getD []).length
  · simp only [hbig, ite_true]
  · simp only [hbig, ite_false]
    rw [nifSelect_get idx _ 1 h1 (by omega)]
example : 1 ≤ 2 ∧ 1 ≤ 2 ∧ 2 ≤ arithmetic.nops 2 := by decide


private theorem mapM_replicate {α β : Type} (f : α → Option β) (a : α) (b : β)
    (h : f a = some b) (n : Nat) : (List.replicate n a).mapM f = some (List.replicate n b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.mapM_cons, h, ih]

private theorem zipIdx_replicate_map {α β : Type} (p : α) (F : α × Nat → β) (n k : Nat) :
    ((List.replicate n p).zipIdx k).map F = (List.range' k n).map fun i => F (p, i) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.zipIdx_cons, List.range'_succ, ih]

private theorem mapM_replicate_none {α β : Type} (f : α → Option β) (a : α)
    (h : f a = none) (n : Nat) (hn : 1 ≤ n) : (List.replicate n a).mapM f = none := by
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ, List.mapM_cons, h]

/-- Every occurrence of a repeated child contributes its own chain-rule term,
so `x+x`, `x*x` and any operator applied to n copies of one subtree sum the
per-argument partials; the branch is undefined exactly when the child is,
src/EvaluateDerivative.jl:112-120. -/
def repeatedFeatures : Prop :=
  ∀ (o : DEnum) (x : Nat → Option JF) (direction idx n : Nat) (c : Tree JF) (op : DOp),
    1 ≤ n → o.lookup n idx = some op →
    diffScalar o x direction (.branch idx (List.replicate n c)) =
      (diffScalar o x direction c).map fun (v, d) => (op.primal (List.replicate n v),
        addTerms ((List.range n).map fun i => op.deriv i (List.replicate n v) * d))
theorem repeatedFeatures_proof : repeatedFeatures := by
  intro o x direction idx n c op hn hop
  cases hc : diffScalar o x direction c with
  | none => simp [diffScalar, mapM_replicate_none _ c hc n hn]
  | some p =>
    obtain ⟨v, d⟩ := p
    simp [diffScalar, mapM_replicate _ c (v, d) hc n, hop, diffKernel, List.map_replicate,
      zipIdx_replicate_map, List.range_eq_range']
example : 1 ≤ 2 ∧ arithmetic.lookup 2 1 = some addOp := ⟨by decide, rfl⟩

def bothConstantIndex : Prop :=
  ∀ nf nc idx, nf + nc ≤ 65535 → 1 ≤ idx → idx ≤ nc →
    leafIndex .both nf true idx = some (nf + idx)
theorem bothConstantIndex_proof : bothConstantIndex := by
  intro nf nc idx htotal hpos hidx
  have hnf : nf < 65536 := by omega
  have hsum : idx + nf < 65536 := by omega
  simp only [leafIndex, Nat.mod_eq_of_lt hnf, Nat.mod_eq_of_lt hsum]
  exact congrArg some (Nat.add_comm idx nf)
example : 1 + 1 ≤ 65535 ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧ leafIndex .both 1 true 1 = some (1 + 1) := by decide

def registrationInventory : Prop :=
  nonDifferentiableRegistrations.length = 6 ∧
  nonDifferentiableRegistrations.map Prod.snd = [4, 5, 2, 2, 3, 1]
theorem registrationInventory_proof : registrationInventory := by unfold registrationInventory; decide

end DynExpr.Deriv
