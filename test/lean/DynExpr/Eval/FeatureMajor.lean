import DynExpr.Eval.Top

/-!
Mirror and proofs for `FeatureMajorMatrix`, `feature_major_matrix`,
`feature_major_batch`, `_kernels_validate`, and the fused `acc += x` validity
checks added in `src/Evaluate.jl`.
-/

namespace DynExpr.Eval

variable {T : Type} [JlScalar T]

/-- `FeatureMajorMatrix{T}` (`src/Evaluate.jl:101-128`): wraps a column-major
`(nsamples, nfeatures)` matrix `data` and exposes logical size
`(nfeatures, nsamples)` so each feature's samples are contiguous in memory. -/
structure FeatureMajorMat (T : Type) where
  data : JMat T

namespace FeatureMajorMat

/-- Logical number of rows (features): `size(A, 1) = size(A.data, 2)` (`src/Evaluate.jl:121`). -/
def nrows (A : FeatureMajorMat T) : Nat := A.data.ncols

/-- Logical number of columns (samples): `size(A, 2) = size(A.data, 1)` (`src/Evaluate.jl:121`). -/
def ncols (A : FeatureMajorMat T) : Nat := A.data.nrows

/-- `Base.getindex(A::FeatureMajorMatrix, f, j) = A.data[j, f]` (`src/Evaluate.jl:123`). -/
def get? (A : FeatureMajorMat T) (f j : Nat) : Jl T := A.data.get? j f

/-- `feature_major_matrix(X)` (`src/Evaluate.jl:105-107`): `permutedims(X)`. -/
def ofMat (X : JMat T) : FeatureMajorMat T :=
  ⟨JMat.ofFn X.ncols X.nrows fun j f =>
    X.data[X.nrows * j.val + f.val]'(by
      rw [X.size_eq]
      have hf : f.val < X.nrows := f.isLt
      have hj : j.val < X.ncols := j.isLt
      calc
        X.nrows * j.val + f.val < X.nrows * j.val + X.nrows := Nat.add_lt_add_left hf _
        _ = X.nrows * (j.val + 1) := by rw [Nat.mul_succ]
        _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_left X.nrows hj)⟩

/-- `first_feature_index(X::FeatureMajorMatrix, feature)` (`src/Evaluate.jl:154-157`):
checks `1 ≤ feature ≤ size(X, 1)` and returns `(feature - 1) * size(X.data, 1) + 1`. -/
def firstFeatureIndex (A : FeatureMajorMat T) (f : Nat) : Jl Nat :=
  if 1 ≤ f ∧ f ≤ A.nrows then .ok ((f - 1) * A.data.nrows + 1)
  else .error .boundsError

/-- `feature_at(X::FeatureMajorMatrix, input_index, feature, j, _)` with
`feature_stride(::FeatureMajorMatrix) = 1` (`src/Evaluate.jl:160, 169-172`):
at sample `j` (1-based), reads `@inbounds X.data[(f - 1) * n + j]`. -/
def featureAtFM (A : FeatureMajorMat T) (f j : Nat) : Jl T :=
  linInb A.data ((f - 1) * A.data.nrows + j)

/-- `get_feature_array(buffer, X::FeatureMajorMatrix, feature)` (`src/Evaluate.jl:133-147`):
copies the contiguous slice `X.data[(f-1)*n + 1 .. f*n]` (unchecked after `checkbounds`). -/
def rowInbFM (A : FeatureMajorMat T) (f : Nat) : Jl (JVec T) :=
  if h : 1 ≤ f ∧ f ≤ A.nrows then
    .ok (Array.ofFn fun j : Fin A.ncols =>
      A.data.data[(f - 1) * A.data.nrows + j.val]'(by
        rw [A.data.size_eq]
        have hj : j.val < A.data.nrows := j.isLt
        have hf : f - 1 < A.data.ncols := by simp [nrows] at h; omega
        calc
          (f - 1) * A.data.nrows + j.val
            < (f - 1) * A.data.nrows + A.data.nrows := Nat.add_lt_add_left hj _
          _ = f * A.data.nrows := by
            rw [← Nat.succ_mul]
            congr 1
            omega
          _ ≤ A.data.ncols * A.data.nrows := Nat.mul_le_mul_right A.data.nrows h.2
          _ = A.data.nrows * A.data.ncols := Nat.mul_comm _ _))
  else .error (.undefinedBehavior "FeatureMajorMatrix feature index out of bounds")

def getFeatureFM : Buf T → FeatureMajorMat T → Nat → Jl (JVec T × Buf T)
  | .none, A, f => do
    let r ← rowInbFM A f
    pure (r, .none)
  | .mat M i, A, f => do
    let (_, b) ← getArray (.mat M i) A.ncols
    let r ← rowInbFM A f
    pure (r, b)
  | .vec arrs i, A, f => do
    let (_, b) ← getArray (.vec arrs i) A.ncols
    let r ← rowInbFM A f
    pure (r, b)

/-- `feature_major_batch(X::Matrix{T}, indices)` (`src/Evaluate.jl:108-120`):
checks `checkbounds(X, :, indices)` first, then gathers transposed columns. -/
def batch (X : JMat T) (indices : List Nat) : Jl (FeatureMajorMat T) :=
  if h : ∀ c ∈ indices, 1 ≤ c ∧ c ≤ X.ncols then
    .ok ⟨JMat.ofFn indices.length X.nrows fun k f =>
      let col := indices[k.val]'(k.isLt)
      have hc : 1 ≤ col ∧ col ≤ X.ncols := h col (List.getElem_mem k.isLt)
      X.data[X.nrows * (col - 1) + f.val]'(by
        rw [X.size_eq]
        have hf : f.val < X.nrows := f.isLt
        calc
          X.nrows * (col - 1) + f.val < X.nrows * (col - 1) + X.nrows := Nat.add_lt_add_left hf _
          _ = X.nrows * col := by rw [← Nat.mul_succ]; congr 1; omega
          _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_left X.nrows hc.2)⟩
  else .error .boundsError

end FeatureMajorMat

/-- Fused validity check `is_valid(acc) || all(is_valid, out)` where
`acc = foldl (+) zero(T) out` (`src/Evaluate.jl:414-421, 478-485, ...`). -/
def fusedValid (a : JVec T) : Bool :=
  valid (a.foldl JlScalar.add JlScalar.zero) || a.all valid

/-- Float16-overflowing fused validity check: `acc` overflows to non-finite when
the exact rational sum leaves `(-65520, 65520)`, falling back to `all(is_valid, a)`. -/
def fusedValid16 (a : List JF) : Bool :=
  let acc := a.foldl JF.add (.fin 0)
  (match acc with
    | .fin q => decide ((-65520 : Rat) < q ∧ q < 65520)
    | _ => false) || a.all JF.valid

/-- `_kernels_validate(T, eval_context)` (`src/Evaluate.jl:222-225`):
true iff `turbo = false`, `early_exit = true`, `use_fused = true`, and
`T <: Union{AbstractFloat, Complex{<:AbstractFloat}}`. -/
def kernelsValidate (T : Type) [JlScalar T] (cx : Ctx) : Bool :=
  cx.earlyExit && cx.useFused && JlScalar.floatLike (T := T)

/-- Mirror of `_eval_tree_array` with `_kernels_validate` active (`src/Evaluate.jl:27-43,
338-351, 407-552`): each kernel computes `fusedValid`/`isValidArray` internally so
`@return_on_nonfinite_array` and the top-level check skip the duplicate pass.
Here we track the exact validity flag returned by every kernel when `v = kernelsValidate T cx`. -/
def kernelWrap (v : Bool) (r : ResultOk T) : ResultOk T :=
  if v then ⟨r.x, r.ok && fusedValid r.x, r.id⟩ else r

/-- Checked child transition in `src/Evaluate.jl:35-43` when `_kernels_validate` is enabled:
the caller checks `!r.ok` and skips `!is_valid_array(r.x)` when `kernelsValidate` is true. -/
def checkedV (cx : Ctx) (ev : Buf T → Jl (ResultOk T × Buf T))
    (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T)) (b : Buf T) :
    Jl (ResultOk T × Buf T) := do
  let (r, b) ← ev b
  if !r.ok then pure (r, b)
  else if cx.earlyExit && !kernelsValidate T cx && !isValidArray r.x then
    pure (⟨r.x, false, r.id⟩, b)
  else k r.x r.id b

/-- Top-level flag check in `eval_tree_array` (`src/Evaluate.jl:336-346`). -/
def finishFlagV (cx : Ctx) (r : ResultOk T) : Bool :=
  if !r.ok then false
  else if !cx.earlyExit || kernelsValidate T cx then true
  else isValidArray r.x

/-! ## Proofs -/

private theorem jf_foldl_valid_implies_all : ∀ (xs : List JF) (acc : JF),
    JF.valid (xs.foldl JF.add acc) = true → JF.valid acc = true ∧ xs.all JF.valid = true
  | [], acc, h => ⟨h, rfl⟩
  | x :: xs, acc, h => by
    have ⟨hstep, hrest⟩ := jf_foldl_valid_implies_all xs (JF.add acc x) h
    have hpair : JF.valid acc = true ∧ JF.valid x = true := by
      cases acc <;> cases x <;> simp_all [JF.valid, JF.add]
    exact ⟨hpair.1, by simp [hpair.2, hrest]⟩

/-- Fused `acc += x` validity (`is_valid(acc) || all(is_valid, out)`) agrees
with `all(is_valid, out)` on every `JF` vector (and with Float16 sum overflow). -/
def fusedValidAgree : Prop :=
  (∀ xs : JVec JF, fusedValid xs = xs.all JF.valid) ∧
  (∀ xs : List JF, fusedValid16 xs = xs.all JF.valid)

theorem fusedValidAgree_proof : fusedValidAgree := by
  constructor
  · intro xs
    cases xs with
    | mk l =>
      have hfold : (Array.mk l).foldl JlScalar.add JlScalar.zero = l.foldl JF.add (.fin 0) := by
        rw [← Array.foldl_toList]
        rfl
      have hall_eq : (Array.mk l).all valid = l.all JF.valid := by
        rw [← Array.all_toList]
        rfl
      have hall_eq2 : (Array.mk l).all JF.valid = l.all JF.valid := by
        rw [← Array.all_toList]
      unfold fusedValid
      rw [hfold, hall_eq, hall_eq2]
      cases hall : l.all JF.valid
      · simp only [Bool.or_false]
        cases hsum : valid (l.foldl JF.add (.fin 0))
        · rfl
        · have h := (jf_foldl_valid_implies_all l (.fin 0) hsum).2
          rw [hall] at h
          cases h
      · simp
  · intro xs
    unfold fusedValid16
    cases hall : xs.all JF.valid
    · simp only [Bool.or_false]
      cases hacc : xs.foldl JF.add (.fin 0) with
      | fin q =>
        have hvalid : JF.valid (xs.foldl JF.add (.fin 0)) = true := by rw [hacc]; rfl
        have h := (jf_foldl_valid_implies_all xs (.fin 0) hvalid).2
        rw [hall] at h
        cases h
      | posInf => rfl
      | negInf => rfl
      | nan => rfl
    · simp

/-- `FeatureMajorMatrix` constructed via `feature_major_matrix(X)` agrees with `X`
on size, `getindex` (including `BoundsError`), `feature_at` (with stride 1), and
`get_feature_array` (buffered and unbuffered). -/
def featureMajorEquiv : Prop :=
  ∀ (T : Type) [JlScalar T] (X : JMat T),
    let A := FeatureMajorMat.ofMat X
    A.nrows = X.nrows ∧ A.ncols = X.ncols ∧
    (∀ f j, A.get? f j = X.get? f j) ∧
    (∀ f, 1 ≤ f → f ≤ X.nrows →
      (∀ j, 1 ≤ j → j ≤ X.ncols → A.featureAtFM f j = featureAt X f j) ∧
      (∀ b : Buf T, FeatureMajorMat.getFeatureFM b A f = getFeature b X f))

omit [JlScalar T] in
private theorem ofMat_data_eq (X : JMat T) (f j : Nat)
    (hf1 : 1 ≤ f) (hf2 : f ≤ X.nrows) (hj1 : 1 ≤ j) (hj2 : j ≤ X.ncols) :
    have hidx : (f - 1) * X.ncols + (j - 1) < (FeatureMajorMat.ofMat X).data.data.size := by
      rw [(FeatureMajorMat.ofMat X).data.size_eq]
      change (f - 1) * X.ncols + (j - 1) < X.ncols * X.nrows
      calc
        (f - 1) * X.ncols + (j - 1) < (f - 1) * X.ncols + X.ncols := Nat.add_lt_add_left (by omega) _
        _ = f * X.ncols := by rw [← Nat.succ_mul]; congr 1; omega
        _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_right X.ncols hf2
        _ = X.ncols * X.nrows := Nat.mul_comm _ _
    have hidxX : X.nrows * (j - 1) + (f - 1) < X.data.size := by
      rw [X.size_eq]
      calc
        X.nrows * (j - 1) + (f - 1) < X.nrows * (j - 1) + X.nrows := Nat.add_lt_add_left (by omega) _
        _ = X.nrows * j := by rw [← Nat.mul_succ]; congr 1; omega
        _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_left X.nrows hj2
    (FeatureMajorMat.ofMat X).data.data[(f - 1) * X.ncols + (j - 1)]'hidx =
      X.data[X.nrows * (j - 1) + (f - 1)]'hidxX := by
  have hjlt : j - 1 < X.ncols := by omega
  have hnc : 0 < X.ncols := by omega
  have hmod : ((f - 1) * X.ncols + (j - 1)) % X.ncols = j - 1 := by
    rw [Nat.mul_comm]
    simp [Nat.mod_eq_of_lt hjlt]
  have hdiv : ((f - 1) * X.ncols + (j - 1)) / X.ncols = f - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnc, Nat.div_eq_of_lt hjlt, Nat.zero_add]
  simp only [FeatureMajorMat.ofMat, JMat.ofFn, Array.getElem_ofFn, hmod, hdiv]

theorem featureMajorEquiv_proof : featureMajorEquiv := by
  intro T _ X
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro f j
    by_cases h : (1 ≤ f ∧ f ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols)
    · rcases h with ⟨⟨hf1, hf2⟩, ⟨hj1, hj2⟩⟩
      unfold FeatureMajorMat.get?
      have hA_nrows : (FeatureMajorMat.ofMat X).data.nrows = X.ncols := rfl
      have hA_ncols : (FeatureMajorMat.ofMat X).data.ncols = X.nrows := rfl
      rw [JMat.get?_inbounds (FeatureMajorMat.ofMat X).data j f hj1 (by rw [hA_nrows]; exact hj2) hf1 (by rw [hA_ncols]; exact hf2)]
      rw [JMat.get?_inbounds X f j hf1 hf2 hj1 hj2]
      congr 1
      have hidx_eq : (FeatureMajorMat.ofMat X).data.nrows * (f - 1) + (j - 1) =
          (f - 1) * X.ncols + (j - 1) := by
        rw [hA_nrows, Nat.mul_comm]
      have hof := ofMat_data_eq X f j hf1 hf2 hj1 hj2
      simpa only [hidx_eq] using hof
    · have h1 : (FeatureMajorMat.ofMat X).get? f j = .error .boundsError := by
        unfold FeatureMajorMat.get?
        apply JMat.get?_oob
        intro hc
        exact h ⟨hc.2, hc.1⟩
      have h2 : X.get? f j = .error .boundsError := JMat.get?_oob X f j h
      rw [h1, h2]
  · intro f hf1 hf2
    constructor
    · intro j hj1 hj2
      unfold FeatureMajorMat.featureAtFM featureAt linInb
      have hA_size : (FeatureMajorMat.ofMat X).data.data.size = X.ncols * X.nrows := by
        simp [FeatureMajorMat.ofMat, JMat.ofFn]
      have hA_nrows : (FeatureMajorMat.ofMat X).data.nrows = X.ncols := rfl
      have h1 : 1 ≤ (f - 1) * (FeatureMajorMat.ofMat X).data.nrows + j ∧
          (f - 1) * (FeatureMajorMat.ofMat X).data.nrows + j ≤ (FeatureMajorMat.ofMat X).data.data.size := by
        rw [hA_size, hA_nrows]
        constructor
        · omega
        · calc
            (f - 1) * X.ncols + j ≤ (f - 1) * X.ncols + X.ncols := Nat.add_le_add_left hj2 _
            _ = f * X.ncols := by rw [← Nat.succ_mul]; congr 1; omega
            _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_right X.ncols hf2
            _ = X.ncols * X.nrows := Nat.mul_comm _ _
      have h2 : 1 ≤ f + (j - 1) * X.nrows ∧ f + (j - 1) * X.nrows ≤ X.data.size := by
        rw [X.size_eq]
        constructor
        · omega
        · calc
            f + (j - 1) * X.nrows ≤ X.nrows + (j - 1) * X.nrows := Nat.add_le_add_right hf2 _
            _ = j * X.nrows := by rw [Nat.add_comm, ← Nat.succ_mul]; congr 1; omega
            _ ≤ X.ncols * X.nrows := Nat.mul_le_mul_right X.nrows hj2
            _ = X.nrows * X.ncols := Nat.mul_comm _ _
      rw [dite_eq_left h1, dite_eq_left h2]
      congr 1
      have hsub1 : (f - 1) * (FeatureMajorMat.ofMat X).data.nrows + j - 1 =
          (f - 1) * X.ncols + (j - 1) := by rw [hA_nrows]; omega
      have hsub2 : f + (j - 1) * X.nrows - 1 = X.nrows * (j - 1) + (f - 1) := by
        rw [Nat.mul_comm]; omega
      have heq := ofMat_data_eq X f j hf1 hf2 hj1 hj2
      simpa [hsub1, hsub2] using heq
    · have hrow : FeatureMajorMat.rowInbFM (FeatureMajorMat.ofMat X) f = rowInb X f := by
        unfold FeatureMajorMat.rowInbFM rowInb JMat.row
        have hf : 1 ≤ f ∧ f ≤ X.nrows := ⟨hf1, hf2⟩
        have hfA : 1 ≤ f ∧ f ≤ (FeatureMajorMat.ofMat X).nrows := hf
        rw [dite_eq_left hfA, ite_eq_left hf, dite_eq_left hf]
        congr 1
        apply Array.ext
        · simp [FeatureMajorMat.ncols, FeatureMajorMat.ofMat, JMat.ofFn]
        · intro j hj1 hj2
          simp only [Array.getElem_ofFn]
          have hj : j < X.ncols := by simpa [FeatureMajorMat.ncols, FeatureMajorMat.ofMat, JMat.ofFn] using hj1
          have heq := ofMat_data_eq X f (j + 1) hf1 hf2 (by omega) (by omega)
          simpa [FeatureMajorMat.ofMat, JMat.ofFn] using heq
      intro b
      cases b with
      | none =>
        simp only [FeatureMajorMat.getFeatureFM, getFeature, hrow]
      | mat M i =>
        simp only [FeatureMajorMat.getFeatureFM, getFeature, hrow]
        rfl
      | vec arrs i =>
        simp only [FeatureMajorMat.getFeatureFM, getFeature, hrow]
        rfl

/-- `feature_major_batch(X, indices)` never exhibits undefined behaviour: any
out-of-bounds column index raises `BoundsError`, and in-bounds indices produce a
`FeatureMajorMatrix` whose `(f, k)` entry equals `X[f, indices[k]]`. -/
def featureMajorBatchSafe : Prop :=
  ∀ (T : Type) [JlScalar T] (X : JMat T) (indices : List Nat),
    ((∃ c ∈ indices, ¬ (1 ≤ c ∧ c ≤ X.ncols)) →
      FeatureMajorMat.batch X indices = .error .boundsError) ∧
    ((∀ c ∈ indices, 1 ≤ c ∧ c ≤ X.ncols) →
      ∃ B, FeatureMajorMat.batch X indices = .ok B ∧
        B.nrows = X.nrows ∧ B.ncols = indices.length ∧
        ∀ f k (hk : 1 ≤ k ∧ k ≤ indices.length),
          1 ≤ f → f ≤ X.nrows →
          B.get? f k = X.get? f (indices[k - 1]'(by omega)))

theorem featureMajorBatchSafe_proof : featureMajorBatchSafe := by
  intro T _ X indices
  constructor
  · intro ⟨c, hcm, hbad⟩
    unfold FeatureMajorMat.batch
    have hn : ¬ (∀ c ∈ indices, 1 ≤ c ∧ c ≤ X.ncols) := fun h => hbad (h c hcm)
    rw [dite_eq_right hn]
  · intro hall
    unfold FeatureMajorMat.batch
    rw [dite_eq_left hall]
    refine ⟨_, rfl, rfl, rfl, ?_⟩
    intro f k hk hf1 hf2
    have hcol : 1 ≤ indices[k - 1]'(by omega) ∧ indices[k - 1]'(by omega) ≤ X.ncols :=
      hall _ (List.getElem_mem (by omega))
    have hB := JMat.get_ofFn indices.length X.nrows (fun (k' : Fin indices.length) (f' : Fin X.nrows) =>
      let col := indices[k'.val]'(k'.isLt)
      X.data[X.nrows * (col - 1) + f'.val]'(by
        rw [X.size_eq]
        have hf' : f'.val < X.nrows := f'.isLt
        have hc' := hall col (List.getElem_mem k'.isLt)
        calc
          X.nrows * (col - 1) + f'.val < X.nrows * (col - 1) + X.nrows := Nat.add_lt_add_left hf' _
          _ = X.nrows * col := by rw [← Nat.mul_succ]; congr 1; omega
          _ ≤ X.nrows * X.ncols := Nat.mul_le_mul_left X.nrows hc'.2))
      k f hk.1 hk.2 hf1 hf2
    rw [FeatureMajorMat.get?, hB, JMat.get?_eq X f _ hf1 hf2 hcol.1 hcol.2]

/-- Soundness of skipping `@return_on_nonfinite_array` and the top-level
`is_valid_array` check when `_kernels_validate` is active: if every kernel
returns `kernelWrap (kernelsValidate T cx) r` and `fusedValid` agrees with
`isValidArray`, then `checkedV` and `finishFlagV` agree identically with
unvalidated `checked` and `evalArr`'s final flag (for every result, valid or not). -/
def kernelsValidateSound : Prop :=
  ∀ (T : Type) [JlScalar T] (cx : Ctx) (r : ResultOk T),
    (∀ a : JVec T, fusedValid a = isValidArray a) →
    finishFlagV cx (kernelWrap (kernelsValidate T cx) r) =
      (r.ok && (!cx.earlyExit || isValidArray r.x)) ∧
    ∀ (k : JVec T → Ident → Buf T → Jl (ResultOk T × Buf T)) (b : Buf T),
      checkedV cx (fun b' => .ok (kernelWrap (kernelsValidate T cx) r, b')) k b =
      checked cx (fun b' => .ok (r, b')) k b

theorem kernelsValidateSound_proof : kernelsValidateSound := by
  intro T _ cx r hfg
  rcases r with ⟨rx, rok, rid⟩
  rcases cx with ⟨ee, fu, D⟩
  constructor
  · unfold finishFlagV kernelWrap kernelsValidate
    cases rok <;> cases ee <;> cases fu <;>
      cases hfl : JlScalar.floatLike (T := T) <;> simp [hfg]
  · intro k b
    unfold checkedV checked kernelWrap kernelsValidate
    cases rok <;> cases ee <;> cases fu <;>
      cases hfl : JlScalar.floatLike (T := T) <;> cases hv : isValidArray rx <;>
      simp [hfg, hv]

example :
    (∀ a : JVec JF, fusedValid a = isValidArray a) ∧
    (∀ c ∈ ([1] : List Nat), 1 ≤ c ∧ c ≤ (⟨1, 1, #[.fin 0], rfl⟩ : JMat JF).ncols) := by
  refine ⟨fun a => ?_, by simp⟩
  rw [fusedValidAgree_proof.1 a]
  unfold isValidArray
  have hfl : JlScalar.floatLike (T := JF) = true := rfl
  simp only [hfl, ↓reduceIte]
  cases hall : a.all valid
  · simp only [Bool.or_false]
    cases hs : valid (jsum a)
    · rfl
    · have ha : a.toList.all JF.valid = true := by
        cases hlist : a.toList with
        | nil => rfl
        | cons x xs =>
          have hs' : JF.valid (xs.foldl JF.add x) = true := by
            change JF.valid (jsum a) = true at hs
            rw [jsum, hlist] at hs
            exact hs
          have ⟨hx, hxs⟩ := jf_foldl_valid_implies_all xs x hs'
          simp [hx, hxs]
      have ha' : a.all valid = true := by
        rw [← Array.all_toList]
        exact ha
      rw [ha'] at hall
      cases hall
  · simp

end DynExpr.Eval
