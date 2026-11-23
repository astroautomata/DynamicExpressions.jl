import DynExpr.ParamStruct.Mirror

/-! General laws for the parameter-augmented sample matrix built by `augment`
(src/ParametricExpression.jl:378-397). Every statement quantifies over all
parameter matrices, feature matrices, class vectors, trees, and operator enums;
the proofs follow the mirror's control flow (`checkClasses`, the column `mapM`,
and `ofColumnsN`). -/

namespace DynExpr.ParamStruct

private theorem bind_ok_inv {α β : Type} {x : Jl α} {f : α → Jl β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A successful `mapM` in `Jl` returns one result per input, each produced by
the mapped function at the same position. -/
private theorem mapM_ok {α β : Type} {f : α → Jl β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ys.length = xs.length ∧
      ∀ (k : Nat) (h₁ : k < xs.length) (h₂ : k < ys.length), f xs[k] = .ok ys[k]
  | [], ys, h => by
    simp [List.mapM_nil] at h
    subst h
    exact ⟨rfl, fun k h₁ => absurd h₁ (by simp)⟩
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_ok_inv h
    obtain ⟨zs, hzs, h⟩ := bind_ok_inv h
    simp at h
    subst h
    obtain ⟨hl, hk⟩ := mapM_ok hzs
    refine ⟨by simp [hl], ?_⟩
    intro k h₁ h₂
    cases k with
    | zero => simpa using hy
    | succ k => simpa using hk k (by simpa using h₁) (by simpa using h₂)

private theorem mapM_congr_local {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons, List.mapM_cons, h a (by simp)]
    rw [ih (by intro b hb; exact h b (by simp [hb]))]

private theorem mapM_map_local {α β γ : Type} (xs : List α)
    (f : α → β) (g : β → Option γ) :
    (xs.map f).mapM g = xs.mapM (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, ih]

/-- Successful class validation fixes the class count to the sample count. -/
private theorem checkClasses_ok {n m : Nat} {classes : List Int} {u : Unit}
    (h : checkClasses n m classes = .ok u) : classes.length = n := by
  simp only [checkClasses] at h
  split at h
  · cases h
  · rename_i hne
    simpa using hne

/-- Dimensions of a successful fixed-row column construction. -/
theorem ofColumnsN_dims {n : Nat} {xs : List (List JF)} {X : JMat JF}
    (hX : ofColumnsN n xs = some X) :
    X.nrows = n ∧ X.ncols = xs.length := by
  unfold ofColumnsN at hX
  split at hX
  · cases hX
    exact ⟨rfl, rfl⟩
  · cases hX

/-- Entry `(i, j)` of a matrix built from columns is entry `i` of column `j`
(one-based). -/
theorem get_ofColumnsN {n : Nat} {xs : List (List JF)} {X : JMat JF}
    (hX : ofColumnsN n xs = some X) (i j : Nat)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ n) (hj₁ : 1 ≤ j) (hj₂ : j ≤ xs.length) :
    ∃ v, X.get? i j = .ok v ∧ (xs[j - 1]?).bind (fun col => col[i - 1]?) = some v := by
  unfold ofColumnsN at hX
  split at hX
  · rename_i hrect
    cases hX
    refine ⟨_, JMat.get_ofFn _ _ _ i j hi₁ hi₂ hj₁ hj₂, ?_⟩
    have hlen := hrect ⟨j - 1, by omega⟩
    dsimp at hlen
    rw [List.getElem?_eq_getElem (by omega)]
    simp only [Option.bind_some]
    rw [List.getElem?_eq_getElem (by rw [hlen]; omega)]
  · cases hX

/-- Coordinate description of the columns gathered by a successful `augment`. -/
private theorem augment_spec {P X Y : JMat JF} {classes : List Int}
    (h : augment P X classes = .ok Y) :
    classes.length = X.ncols ∧ ∃ cols : List (List JF),
      ofColumnsN (P.nrows + X.nrows) cols = some Y ∧ cols.length = classes.length ∧
      ∀ k, k < classes.length → ∃ col, cols[k]? = some col ∧
        col.length = P.nrows + X.nrows ∧
        (∀ c, classes[k]? = some c → ∀ i, i < P.nrows →
          ∃ v, col[i]? = some v ∧ parameterAt P (i + 1) c = .ok v) ∧
        (∀ i, i < X.nrows →
          ∃ v, col[P.nrows + i]? = some v ∧ X.get? (i + 1) (k + 1) = .ok v) := by
  unfold augment at h
  obtain ⟨u, hcc, h⟩ := bind_ok_inv h
  have hlen := checkClasses_ok hcc
  obtain ⟨cols, hcols, h⟩ := bind_ok_inv h
  cases hY : ofColumnsN (P.nrows + X.nrows) cols with
  | none => simp [hY] at h
  | some Y' =>
    simp [hY] at h
    subst h
    obtain ⟨hcl, hck⟩ := mapM_ok hcols
    refine ⟨hlen, cols, hY, by simpa using hcl, ?_⟩
    intro k hk
    have hkz : k < classes.zipIdx.length := by simpa using hk
    have hkc : k < cols.length := by rw [hcl]; exact hkz
    have hcol := hck k hkz hkc
    simp only [List.getElem_zipIdx, Nat.zero_add] at hcol
    obtain ⟨ps, hps, hcol⟩ := bind_ok_inv hcol
    obtain ⟨xs, hxs, hcol⟩ := bind_ok_inv hcol
    simp at hcol
    obtain ⟨hpl, hpk⟩ := mapM_ok hps
    obtain ⟨hxl, hxk⟩ := mapM_ok hxs
    simp only [List.length_range] at hpl hxl
    refine ⟨cols[k], List.getElem?_eq_getElem hkc, ?_, ?_, ?_⟩
    · rw [← hcol]; simp [hpl, hxl]
    · intro c hc i hi
      have hck' : classes[k] = c := by
        rw [List.getElem?_eq_getElem hk] at hc
        simpa using hc
      have hp := hpk i (by simpa using hi) (by omega)
      simp only [List.getElem_range] at hp
      refine ⟨ps[i]'(by omega), ?_, by rw [← hck']; exact hp⟩
      rw [← hcol, List.getElem?_append_left (by omega)]
      exact List.getElem?_eq_getElem (by omega)
    · intro i hi
      have hx := hxk i (by simpa using hi) (by omega)
      simp only [List.getElem_range] at hx
      refine ⟨xs[i]'(by omega), ?_, hx⟩
      rw [← hcol, List.getElem?_append_right (by omega)]
      have : P.nrows + i - ps.length = i := by omega
      rw [this]
      exact List.getElem?_eq_getElem (by omega)

/-- A successful augmentation stacks the parameter rows above the feature rows
and keeps one column per sample. -/
theorem augment_shape (P X Y : JMat JF) (classes : List Int)
    (h : augment P X classes = .ok Y) :
    Y.nrows = P.nrows + X.nrows ∧ Y.ncols = X.ncols := by
  obtain ⟨hlen, cols, hY, hcl, -⟩ := augment_spec h
  obtain ⟨hr, hc⟩ := ofColumnsN_dims hY
  exact ⟨hr, by rw [hc, hcl, hlen]⟩

/-- Every parameter row `i` of sample column `j` holds the class-`c` parameter
selected by the mirror's signed class lookup. -/
theorem augment_parameter (P X Y : JMat JF) (classes : List Int) (i j : Nat) (c : Int)
    (h : augment P X classes = .ok Y) (hi : 1 ≤ i ∧ i ≤ P.nrows)
    (hj : 1 ≤ j ∧ j ≤ X.ncols) (hc : classes[j - 1]? = some c) :
    Y.get? i j = parameterAt P i c := by
  obtain ⟨hlen, cols, hY, hcl, hspec⟩ := augment_spec h
  obtain ⟨hr, hcn⟩ := ofColumnsN_dims hY
  obtain ⟨hsr, hsc⟩ := augment_shape P X Y classes h
  obtain ⟨v, hv, hcolv⟩ := get_ofColumnsN hY i j hi.1 (by omega) hj.1 (by omega)
  obtain ⟨col, hcol, -, hpar, -⟩ := hspec (j - 1) (by omega)
  obtain ⟨w, hw, hpw⟩ := hpar c hc (i - 1) (by omega)
  rw [hcol, Option.bind_some, hw] at hcolv
  cases hcolv
  have hi' : i - 1 + 1 = i := by omega
  rw [hi'] at hpw
  rw [hv, hpw]

/-- Every feature row `f` of the input appears at row `P.nrows + f` of the
augmented matrix in the same sample column. -/
theorem augment_feature (P X Y : JMat JF) (classes : List Int) (f j : Nat)
    (h : augment P X classes = .ok Y) (hf : 1 ≤ f ∧ f ≤ X.nrows)
    (hj : 1 ≤ j ∧ j ≤ X.ncols) :
    Y.get? (P.nrows + f) j = X.get? f j := by
  obtain ⟨hlen, cols, hY, hcl, hspec⟩ := augment_spec h
  obtain ⟨hr, hcn⟩ := ofColumnsN_dims hY
  obtain ⟨hsr, hsc⟩ := augment_shape P X Y classes h
  obtain ⟨v, hv, hcolv⟩ :=
    get_ofColumnsN hY (P.nrows + f) j (by omega) (by omega) hj.1 (by omega)
  obtain ⟨col, hcol, -, -, hfeat⟩ := hspec (j - 1) (by omega)
  obtain ⟨w, hw, hxw⟩ := hfeat (f - 1) (by omega)
  have hidx : P.nrows + f - 1 = P.nrows + (f - 1) := by omega
  rw [hcol, Option.bind_some, hidx, hw] at hcolv
  cases hcolv
  have hf' : f - 1 + 1 = f := by omega
  have hj' : j - 1 + 1 = j := by omega
  rw [hf', hj'] at hxw
  rw [hv, hxw]

/-- Leaf index bounds for a parametric tree with `np` parameter rows and `nf`
features: parameters in `1..np`, features in `1..nf`, constants unrestricted. -/
def PLeafBounds (np nf : Nat) : PTree → Prop
  | .const (.constant _) => True
  | .const (.parameter p) => 1 ≤ p ∧ p ≤ np
  | .feature f => 1 ≤ f ∧ f ≤ nf
  | .branch _ cs => ∀ c ∈ cs, PLeafBounds np nf c

/-- The UInt16 feature shift is ordinary addition below 65536. -/
private theorem feature_shift (n i nf : Nat) (hi : i ≤ nf) (hcap : n + nf < 65536) :
    (UInt16.ofNat i + UInt16.ofNat n).toNat = n + i := by
  rw [UInt16.toNat_add, UInt16.toNat_ofNat', UInt16.toNat_ofNat']
  have h1 : i % 2 ^ 16 = i := Nat.mod_eq_of_lt (by omega)
  have h2 : n % 2 ^ 16 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
  omega

/-- For every tree and arbitrary operator enum, evaluating the converted tree on
sample `j` of the augmented matrix agrees with the direct parametric
denotation that reads features from `X` and parameters from class `c`. -/
theorem augmented_denotation (P X Y : JMat JF) (classes : List Int) (t : PTree)
    (o : OpEnum JF) (j : Nat) (c : Int)
    (h : augment P X classes = .ok Y) (hcap : P.nrows + X.nrows < 65536)
    (hbound : PLeafBounds P.nrows X.nrows t) (hj : 1 ≤ j ∧ j ≤ X.ncols)
    (hc : classes[j - 1]? = some c) :
    (convertTree (UInt16.ofNat P.nrows) t).denoteRow o Y j =
      denoteP o (fun f => (X.get? f j).toOption)
        (fun p => (parameterAt P p c).toOption) t := by
  unfold Tree.denoteRow
  induction t using Tree.induction with
  | hc v =>
    cases v with
    | constant v => simp [convertTree, Tree.denote, denoteP]
    | parameter p =>
      simp only [PLeafBounds] at hbound
      simp only [convertTree, Tree.denote, denoteP]
      rw [augment_parameter P X Y classes p j c h hbound hj hc]
  | hf i =>
    simp only [PLeafBounds] at hbound
    simp only [convertTree, Tree.denote, denoteP,
      feature_shift P.nrows i X.nrows hbound.2 hcap]
    rw [augment_feature P X Y classes i j h hbound hj]
  | hb op cs ih =>
    simp only [PLeafBounds] at hbound
    simp only [convertTree, Tree.denote, denoteP, List.length_map]
    rw [mapM_map_local, mapM_congr_local cs _ _ (fun a ha => ih a ha (hbound a ha))]

/-- A `Jl` `mapM` succeeds when every element succeeds; each result satisfies
the per-element postcondition `Q`. -/
private theorem mapM_exists {α β : Type} {f : α → Jl β} {Q : β → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, ∃ y, f x = .ok y ∧ Q y) →
      ∃ ys, xs.mapM f = .ok ys ∧ ys.length = xs.length ∧ ∀ y ∈ ys, Q y
  | [], _ => ⟨[], by simp [List.mapM_nil]⟩
  | x :: xs, h => by
    obtain ⟨y, hy, hq⟩ := h x (by simp)
    obtain ⟨ys, hys, hl, hqs⟩ := mapM_exists (xs := xs) (fun a ha => h a (by simp [ha]))
    refine ⟨y :: ys, ?_, by simp [hl], ?_⟩
    · rw [List.mapM_cons, hy, jl_bind_ok, hys, jl_bind_ok, jl_pure]
    · intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hq
      · exact hqs z hz

/-- The mirror's running maximum stays below any common upper bound. -/
private theorem foldl_max_le (B : Int) :
    ∀ (l : List Int) (acc : Int), acc ≤ B → (∀ x ∈ l, x ≤ B) → l.foldl max acc ≤ B
  | [], _, hacc, _ => hacc
  | x :: xs, acc, hacc, h => by
    simp only [List.foldl_cons]
    apply foldl_max_le B xs
    · have hx := h x (by simp)
      simp only [Int.max_def]
      split <;> omega
    · intro y hy
      exact h y (by simp [hy])

/-- For reasonable inputs, `augment` raises no exception: one class per sample
and every class a valid one-based column of `P`, including the empty class
vector since PR #246. -/
theorem augment_exists_any (P X : JMat JF) (classes : List Int)
    (hlen : classes.length = X.ncols)
    (hcls : ∀ c ∈ classes, 1 ≤ c ∧ c ≤ Int.ofNat P.ncols) :
    ∃ Y, augment P X classes = .ok Y := by
  have hcc : checkClasses X.ncols P.ncols classes = .ok () := by
    cases classes with
    | nil =>
      have hl : ([] : List Int).length = X.ncols := hlen
      simp only [checkClasses, hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    | cons c cs =>
      have hmax : cs.foldl max c ≤ Int.ofNat P.ncols :=
        foldl_max_le _ cs c (hcls c (by simp)).2
          (fun x hx => (hcls x (by simp [hx])).2)
      have hl : (c :: cs).length = X.ncols := hlen
      simp only [checkClasses, hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have hgt : ¬ cs.foldl max c > Int.ofNat P.ncols := by omega
      simp only [hgt, ↓reduceIte]
  unfold augment
  rw [hcc, jl_bind_ok]
  obtain ⟨cols, hcols, hcl, hclen⟩ := mapM_exists
    (Q := fun col : List JF => col.length = P.nrows + X.nrows)
    (xs := classes.zipIdx) (f := fun (cj : Int × Nat) => match cj with
      | (c, j) => do
        let ps ← (List.range P.nrows).mapM (fun i => parameterAt P (i+1) c)
        let xs ← (List.range X.nrows).mapM (fun i => X.get? (i+1) (j+1))
        pure (ps ++ xs)) (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
      have hkc : k < classes.length := by simpa using hk
      simp only [List.getElem_zipIdx, Nat.zero_add]
      have hc := hcls classes[k] (List.getElem_mem hkc)
      have hc2 : classes[k] ≤ (P.ncols : Int) := hc.2
      obtain ⟨ps, hps, hpl, -⟩ := mapM_exists (Q := fun _ => True)
        (xs := List.range P.nrows) (f := fun i => parameterAt P (i+1) classes[k]) (by
          intro r hr
          have hr' : r < P.nrows := by simpa using hr
          obtain ⟨v, hv⟩ := JMat.get?_exists P (r + 1) classes[k].toNat
            (by omega) (by omega) (by omega) (by omega)
          refine ⟨v, ?_, trivial⟩
          have hnot : ¬ classes[k] < 1 := by omega
          simp only [parameterAt, hnot, ↓reduceIte]
          exact hv)
      obtain ⟨xs, hxs, hxl, -⟩ := mapM_exists (Q := fun _ => True)
        (xs := List.range X.nrows) (f := fun i => X.get? (i+1) (k+1)) (by
          intro r hr
          have hr' : r < X.nrows := by simpa using hr
          obtain ⟨v, hv⟩ := JMat.get?_exists X (r + 1) (k + 1)
            (by omega) (by omega) (by omega) (by omega)
          exact ⟨v, hv, trivial⟩)
      refine ⟨ps ++ xs, ?_, by simp [hpl, hxl]⟩
      rw [hps, jl_bind_ok, hxs, jl_bind_ok, jl_pure])
  rw [hcols, jl_bind_ok]
  have hrect : ∀ k : Fin cols.length, (cols[k.val]).length = P.nrows + X.nrows :=
    fun k => hclen _ (List.getElem_mem k.isLt)
  cases hY : ofColumnsN (P.nrows + X.nrows) cols with
  | none =>
    unfold ofColumnsN at hY
    rw [dif_pos hrect] at hY
    cases hY
  | some Y => exact ⟨Y, rfl⟩

theorem augment_exists (P X : JMat JF) (classes : List Int)
    (hlen : classes.length = X.ncols) (_hne : classes ≠ [])
    (hcls : ∀ c ∈ classes, 1 ≤ c ∧ c ≤ Int.ofNat P.ncols) :
    ∃ Y, augment P X classes = .ok Y :=
  augment_exists_any P X classes hlen hcls

/-! Satisfiable hypotheses: one parameter row, two classes, one feature row,
two samples using classes `[2, 1]`. -/

private def exP : JMat JF := ⟨1, 2, #[.fin 10, .fin 20], rfl⟩
private def exX : JMat JF := ⟨1, 2, #[.fin 1, .fin 2], rfl⟩
private def exY : JMat JF := ⟨2, 2, #[.fin 20, .fin 1, .fin 10, .fin 2], rfl⟩
private def exTree : PTree := .branch 1 [.const (.parameter 1), .feature 1]

example : augment exP exX [2, 1] = .ok exY := by rfl

example : ∃ (P X Y : JMat JF) (classes : List Int) (i j : Nat) (c : Int),
    augment P X classes = .ok Y ∧ (1 ≤ i ∧ i ≤ P.nrows) ∧
    (1 ≤ j ∧ j ≤ X.ncols) ∧ classes[j - 1]? = some c :=
  ⟨exP, exX, exY, [2, 1], 1, 1, 2, by rfl, by decide, by decide, rfl⟩

example : ∃ (P X Y : JMat JF) (classes : List Int) (f j : Nat),
    augment P X classes = .ok Y ∧ (1 ≤ f ∧ f ≤ X.nrows) ∧ (1 ≤ j ∧ j ≤ X.ncols) :=
  ⟨exP, exX, exY, [2, 1], 1, 2, by rfl, by decide, by decide⟩

example : ∃ (P X Y : JMat JF) (classes : List Int) (t : PTree) (j : Nat) (c : Int),
    augment P X classes = .ok Y ∧ P.nrows + X.nrows < 65536 ∧
    PLeafBounds P.nrows X.nrows t ∧ (1 ≤ j ∧ j ≤ X.ncols) ∧
    classes[j - 1]? = some c := by
  refine ⟨exP, exX, exY, [2, 1], exTree, 1, 2, by rfl, by decide, ?_, by decide, rfl⟩
  simp [PLeafBounds, exTree, exP, exX]

/-- The general law applied to the witnesses above: parameter 1 of class 2 is
`20`, feature 1 of sample 1 is `1`. -/
example (o : OpEnum JF) :
    (convertTree (UInt16.ofNat exP.nrows) exTree).denoteRow o exY 1 =
      denoteP o (fun f => (exX.get? f 1).toOption)
        (fun p => (parameterAt exP p 2).toOption) exTree :=
  augmented_denotation exP exX exY [2, 1] exTree o 1 2 (by rfl) (by decide)
    (by simp [PLeafBounds, exTree, exP, exX]) (by decide) rfl

example : ∃ (P X : JMat JF) (classes : List Int),
    classes.length = X.ncols ∧ classes ≠ [] ∧
    ∀ c ∈ classes, 1 ≤ c ∧ c ≤ Int.ofNat P.ncols :=
  ⟨exP, exX, [2, 1], rfl, by simp, by decide⟩

example : ∃ Y, augment exP exX [2, 1] = .ok Y :=
  augment_exists exP exX [2, 1] rfl (by simp) (by decide)

end DynExpr.ParamStruct
