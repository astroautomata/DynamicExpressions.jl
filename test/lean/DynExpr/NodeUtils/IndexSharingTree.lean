import DynExpr.NodeUtils.Nodes

namespace DynExpr.NodeUtils

variable {T : Type}

/-- Leaf kinds of a plain tree in depth-first left-to-right order
(src/base.jl:77-158 without sharing): `true` for constants. -/
def leafKinds : Tree T → List Bool
  | .const _ => [true]
  | .feature _ => [false]
  | .branch _ cs => cs.flatMap leafKinds

/-- Specification labels: after `start`, the k-th constant leaf gets
`start + k` and every other leaf gets 0. -/
def numberLeaves : List Bool → Nat → List Nat
  | [], _ => []
  | true :: bs, i => (i + 1) :: numberLeaves bs (i + 1)
  | false :: bs, i => 0 :: numberLeaves bs i

/-- Number of constant leaves in a kind list. -/
def countTrue : List Bool → Nat
  | [] => 0
  | true :: bs => countTrue bs + 1
  | false :: bs => countTrue bs

private theorem countTrue_append : ∀ (a b : List Bool), countTrue (a ++ b) = countTrue a + countTrue b
  | [], b => by simp [countTrue]
  | true :: a, b => by
      simp only [List.cons_append, countTrue, countTrue_append a b]
      omega
  | false :: a, b => by simp only [List.cons_append, countTrue, countTrue_append a b]

private theorem numberLeaves_append : ∀ (a b : List Bool) (i : Nat),
    numberLeaves (a ++ b) i = numberLeaves a i ++ numberLeaves b (i + countTrue a)
  | [], b, i => by simp [numberLeaves, countTrue]
  | true :: a, b, i => by
      have e : i + (countTrue a + 1) = i + 1 + countTrue a := by omega
      simp only [List.cons_append, numberLeaves, countTrue, e, numberLeaves_append a b (i + 1)]
  | false :: a, b, i => by
      simp only [List.cons_append, numberLeaves, countTrue, numberLeaves_append a b i]

private theorem countTrue_leafKinds (t : Tree T) : countTrue (leafKinds t) = countConstantNodes t := by
  induction t using Tree.induction with
  | hc v => simp [leafKinds, countTrue, countConstantNodes]
  | hf i => simp [leafKinds, countTrue, countConstantNodes]
  | hb op cs ih =>
      simp only [leafKinds, countConstantNodes]
      have walk : ∀ ts : List (Tree T), (∀ t ∈ ts, countTrue (leafKinds t) = countConstantNodes t) →
          countTrue (ts.flatMap leafKinds) = (ts.map countConstantNodes).sum := by
        intro ts ht
        induction ts with
        | nil => simp [countTrue]
        | cons c cs iht =>
            simp only [List.flatMap_cons, List.map_cons, List.sum_cons, countTrue_append]
            rw [ht c (by simp), iht (fun t h => ht t (by simp [h]))]
      exact walk cs ih

/-- src/NodeUtils.jl:186-202 on plain Node: from counter `i`, constant leaves
receive consecutive indices in depth-first order and the counter advances by
the constant count, while no UInt16 wraparound occurs. -/
theorem indexConstants_labels (t : Tree T) : ∀ i, i + countConstantNodes t < 65536 →
    indexLeaves (indexConstants t i).1 = numberLeaves (leafKinds t) i ∧
    (indexConstants t i).2 = i + countConstantNodes t := by
  induction t using Tree.induction with
  | hc v =>
      intro i hi
      simp only [countConstantNodes] at hi
      simp [indexConstants, indexLeaves, leafKinds, numberLeaves, countConstantNodes,
        Nat.mod_eq_of_lt hi]
  | hf x =>
      intro i _
      simp [indexConstants, indexLeaves, leafKinds, numberLeaves, countConstantNodes]
  | hb op cs ih =>
      have walk : ∀ ts : List (Tree T), (∀ t ∈ ts, ∀ i, i + countConstantNodes t < 65536 →
            indexLeaves (indexConstants t i).1 = numberLeaves (leafKinds t) i ∧
            (indexConstants t i).2 = i + countConstantNodes t) →
          ∀ i, i + (ts.map countConstantNodes).sum < 65536 →
            (indexForest ts i).1.flatMap indexLeaves = numberLeaves (ts.flatMap leafKinds) i ∧
            (indexForest ts i).2 = i + (ts.map countConstantNodes).sum := by
        intro ts ht
        induction ts with
        | nil => intro i _; simp [indexForest, numberLeaves]
        | cons c cs iht =>
            intro i hi
            simp only [List.map_cons, List.sum_cons] at hi
            obtain ⟨h1, h2⟩ := ht c (by simp) i (by omega)
            obtain ⟨h3, h4⟩ := iht (fun t h => ht t (by simp [h])) (i + countConstantNodes c) (by omega)
            cases hci : indexConstants c i with
            | mk n j =>
                rw [hci] at h1 h2
                simp only at h1 h2
                subst h2
                cases hfi : indexForest cs (i + countConstantNodes c) with
                | mk ns k =>
                    rw [hfi] at h3 h4
                    simp only at h3 h4
                    simp only [indexForest, hci, hfi, List.flatMap_cons, List.map_cons, List.sum_cons]
                    refine ⟨?_, by rw [h4]; omega⟩
                    rw [h1, h3, numberLeaves_append, countTrue_leafKinds]
      intro i hi
      simp only [countConstantNodes] at hi
      obtain ⟨h1, h2⟩ := walk cs ih i hi
      cases hfi : indexForest cs i with
      | mk ns j =>
          rw [hfi] at h1 h2
          simp only at h1 h2
          simp only [indexConstants, hfi, indexLeaves, leafKinds, countConstantNodes]
          exact ⟨h1, h2⟩

/-- src/NodeUtils.jl:186-202 on plain Node: for every tree with at most 65535
constant leaves, the k-th constant leaf in depth-first order gets index k,
every feature leaf gets 0, and the final counter is the constant count. -/
def TreeIndexLabels : Prop := ∀ (T : Type) (t : Tree T),
  countConstantNodes t ≤ 65535 →
    indexLeaves (indexConstants t 0).1 = numberLeaves (leafKinds t) 0 ∧
    (indexConstants t 0).2 = countConstantNodes t

theorem treeIndexLabels_proven : TreeIndexLabels := by
  intro T t h
  simpa using indexConstants_labels t 0 (by omega)

example : countConstantNodes (Tree.const (1 : Nat)) ≤ 65535 := by
  simp [countConstantNodes]

end DynExpr.NodeUtils
