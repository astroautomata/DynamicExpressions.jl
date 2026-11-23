import DynExpr.Model.Tree
import DynExpr.Plumbing.Assembly
import DynExpr.Runtime.Errors
import Std

namespace DynExpr.Plumbing

/-- Symbols for mode dispatch, src/precompile.jl:143-180. -/
inductive CompileMode where
  | compile | precompile | other (symbol : String)
  deriving DecidableEq, Repr

/-- src/precompile.jl:153,168: an unsupported mode raises
`error("Invalid value for mode: " * repr(mode))`, an ErrorException; repr
prints nothing. The repr of a plain identifier Symbol `s` is `:s`. -/
def doPrecompilationWithOutput : CompileMode → List String × Jl Unit
  | .compile | .precompile => ([], .ok ())
  | .other s => ([], .error (.errorException ("Invalid value for mode: :" ++ s)))

def doPrecompilation (mode : CompileMode) : Jl Unit :=
  (doPrecompilationWithOutput mode).2
/-- src/precompile.jl:5-17 suppresses exactly DomainError. -/
def ignoreDomainError (result : Jl Unit) : Jl Unit :=
  match result with
  | .error (.domainError _) => .ok ()
  | result => result

/-- Float16/turbo and both-empty skipping, src/precompile.jl:30-31. -/
def skipCombination (nb nu : Nat) (float16 turbo : Bool) : Bool :=
  (nb == 0 && nu == 0) || (float16 && turbo)

/-- Mixed-loop operator indices of one selected (binops, unaops) pair,
src/precompile.jl:70-74: `eachindex(binops)` and `eachindex(unaops)`. -/
def mixedIndices (nb nu : Nat) : List (Nat × Nat × Nat) :=
  (List.range' 1 nb).flatMap fun i =>
    (List.range' 1 nu).flatMap fun j =>
      (List.range' 1 nu).map fun k => (i,j,k)

/-- The outer loop over alternative operator collections, src/precompile.jl:25-31,69-87:
each non-skipped pair of selected tuple lengths runs its own mixed loop. -/
def mixedLoops (binaryCollections unaryCollections : List Nat) :
    List ((Nat × Nat) × List (Nat × Nat × Nat)) :=
  binaryCollections.flatMap fun nb => unaryCollections.filterMap fun nu =>
    if nb == 0 && nu == 0 then none else some ((nb, nu), mixedIndices nb nu)

/-- Trees actually passed to eval_tree_array for one selected pair,
src/precompile.jl:35-87. The same x/c objects may be aliased, but this
workload only evaluates them. -/
def combinationTrees (nb nu : Nat) : List (Tree Nat) :=
  let leaves := [Tree.feature 1, Tree.const 1]
  leaves ++
  (List.range' 1 nb).flatMap (fun i => leaves.flatMap fun l =>
    leaves.map fun r => .branch i [l,r]) ++
  (List.range' 1 nu).flatMap (fun j => (List.range' 1 nu).flatMap fun k =>
    leaves.flatMap fun l => [.branch j [l], .branch j [.branch k [l]]]) ++
  (mixedIndices nb nu).flatMap (fun (i,j,k) =>
    leaves.flatMap fun l => leaves.flatMap fun r =>
      [.branch i [.branch j [l], .branch k [r]], .branch j [.branch i [l,r]]])

/-- Operator cycling in test_functions_on_trees, src/precompile.jl:103-124. -/
def cycleIndex (i n : Nat) := i % n + 1


/-- The exact final tree built on each Float32/Float64 loop pass,
src/precompile.jl:92-127. Conversion to T changes scalar representation only. -/
def functionsTree (nb nu : Nat) : Tree Nat :=
  let x := Tree.feature 1
  let c := Tree.const 1
  let a1 := Tree.branch 1 [x]
  let u2 := cycleIndex 1 nu
  let a2 := Tree.branch 1 [c,a1]
  let b2 := cycleIndex 1 nb
  let a3 := Tree.branch b2 [x,c]
  let b3 := cycleIndex b2 nb
  let a4 := Tree.branch b3 [a3,a2]
  let b4 := cycleIndex b3 nb
  let a5 := Tree.branch b4 [x,x]
  let b5 := cycleIndex b4 nb
  let a6 := Tree.branch u2 [a5]
  let u3 := cycleIndex u2 nu
  let a7 := Tree.branch u3 [a6]
  let u4 := cycleIndex u3 nu
  let a8 := Tree.branch u4 [a4]
  Tree.branch b5 [a8,a7]

/-- The cycling workload must use valid operator indices for its selected
tuples, src/precompile.jl:103-124. Unlike tree size, this depends on nb and nu. -/
def functionsTreeIndices : Prop := ∀ nb nu,
  0 < nb → nb ≤ 255 → 0 < nu → nu ≤ 255 →
  (functionsTree nb nu).WF 2 (fun d => if d = 1 then nu else if d = 2 then nb else 0) 1
theorem functionsTreeIndices_proof : functionsTreeIndices := by
  intro nb nu hb hb255 hu hu255
  have bmin (i : Nat) : 1 ≤ cycleIndex i nb := by unfold cycleIndex; omega
  have bmax (i : Nat) : cycleIndex i nb ≤ nb := by
    have := Nat.mod_lt i hb; unfold cycleIndex; omega
  have blimit (i : Nat) : cycleIndex i nb ≤ 255 := Nat.le_trans (bmax i) hb255
  have umin (i : Nat) : 1 ≤ cycleIndex i nu := by unfold cycleIndex; omega
  have umax (i : Nat) : cycleIndex i nu ≤ nu := by
    have := Nat.mod_lt i hu; unfold cycleIndex; omega
  have ulimit (i : Nat) : cycleIndex i nu ≤ 255 := Nat.le_trans (umax i) hu255
  have hnb : 1 ≤ nb := hb
  have hnu : 1 ≤ nu := hu
  simp [functionsTree, Tree.WF, bmin, bmax, blimit, umin, umax, ulimit, hnb, hnu]
example : 0 < (4 : Nat) ∧ 4 ≤ 255 ∧ 0 < (2 : Nat) ∧ 2 ≤ 255 := by decide

/-- Core API call sequence after copying and self-assignment,
src/precompile.jl:126-139. No distinct compilation evaluator is introduced. -/
def workloadOperations := ["convert", "copy_node", "set_node!", "string_tree", "count_nodes",
  "count_constant_nodes", "count_depth", "index_constant_nodes", "has_operators",
  "has_constants", "get_scalar_constants", "set_scalar_constants!", "combine_operators!", "simplify_tree!"]


def workloadAgreement : Prop := ∀ name ∈ workloadOperations,
  name ∈ "convert" :: (reexports.flatMap fun group => bindings group.1)
theorem workloadAgreement_proof : workloadAgreement := by unfold workloadAgreement; decide
def modesExact : Prop := ∀ mode, doPrecompilation mode = .ok () ↔
  mode = .compile ∨ mode = .precompile
theorem modesExact_proof : modesExact := by intro m; cases m <;> simp [doPrecompilation, doPrecompilationWithOutput]

/-- An unsupported mode raises the intended ErrorException (fixed in PR #257). -/
def invalidModeError : Prop := ∀ s, ∃ msg,
  doPrecompilation (.other s) = .error (.errorException msg)
theorem invalidModeError_proof : invalidModeError := fun _ => ⟨_, rfl⟩

def domainSuppression : Prop := (∀ msg, ignoreDomainError (.error (.domainError msg)) = .ok ()) ∧
  (∀ e, (∀ msg, e ≠ .domainError msg) → ignoreDomainError (.error e) = .error e)
theorem domainSuppression_proof : domainSuppression := by
  constructor
  · intros; rfl
  · intro e h; cases e <;> simp_all [ignoreDomainError]
example : ∀ msg, JlError.boundsError ≠ .domainError msg := by simp

/-- The mixed-loop triples of every iteration range exactly over that
iteration's selected operator tuples, whatever alternative collections were
supplied (fixed in PR #258). -/
def mixedCoverage : Prop := ∀ (binaryCollections unaryCollections : List Nat) entry,
  entry ∈ mixedLoops binaryCollections unaryCollections → ∀ i j k,
  (i, j, k) ∈ entry.2 ↔
    (1 ≤ i ∧ i ≤ entry.1.1) ∧ (1 ≤ j ∧ j ≤ entry.1.2) ∧ (1 ≤ k ∧ k ≤ entry.1.2)
theorem mixedCoverage_proof : mixedCoverage := by
  intro bcs ucs entry hentry i j k
  simp only [mixedLoops, List.mem_flatMap, List.mem_filterMap] at hentry
  obtain ⟨nb, _, nu, _, hsome⟩ := hentry
  split at hsome
  · cases hsome
  · cases hsome
    simp only [mixedIndices, List.mem_flatMap, List.mem_map, List.mem_range'_1, Prod.mk.injEq]
    constructor
    · rintro ⟨i', ⟨h1, h2⟩, j', ⟨h3, h4⟩, k', ⟨h5, h6⟩, rfl, rfl, rfl⟩
      omega
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
      exact ⟨i, ⟨h1, by omega⟩, j, ⟨h3, by omega⟩, k, ⟨h5, by omega⟩, rfl, rfl, rfl⟩
example : ((1, 2), mixedIndices 1 2) ∈ mixedLoops [1] [2] := by decide

def cycleBounds : Prop := ∀ i n, 0 < n → 1 ≤ cycleIndex i n ∧ cycleIndex i n ≤ n
theorem cycleBounds_proof : cycleBounds := by
  intro i n hn
  have := Nat.mod_lt i hn
  simp only [cycleIndex]; omega
example : 0 < (4 : Nat) := by decide

def skipPolicy : Prop := ∀ nb nu float16 turbo,
  skipCombination nb nu float16 turbo = true ↔
    (nb = 0 ∧ nu = 0) ∨ (float16 = true ∧ turbo = true)
theorem skipPolicy_proof : skipPolicy := by
  intro nb nu float16 turbo
  simp [skipCombination]

end DynExpr.Plumbing
