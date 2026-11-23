import DynExpr.ParamStruct.ScalarLaws
import DynExpr.ParamStruct.MatrixLaws
import DynExpr.ParamStruct.LeafLaws
import DynExpr.Eval.Scalars

namespace DynExpr.ParamStruct

private def zero : JF := .fin 0
private def one : JF := .fin 1
private def two : JF := .fin 2
private def ten : JF := .fin 10
private def twenty : JF := .fin 20
private def ops : OpEnum JF := ⟨[[fun xs => xs.headD zero], [fun xs => xs.foldl JF.add zero]]⟩
private def params : JMat JF := ⟨1, 2, #[ten, twenty], rfl⟩
private def input : JMat JF := ⟨1, 2, #[one, two], rfl⟩
private def fixture (t : PTree) : PExpression := ⟨t,ops,none,params,none⟩

/-- Feature/constant equality should be symmetric on initialized legal leaves
(fixed in PR #244). -/
def EqualitySymmetric : Prop := ∀ a b : Leaf,
  LeafActiveInitialized a → LeafActiveInitialized b →
  leafEqual a b = leafEqual b a ∧
  (a.constant ≠ b.constant → leafEqual a b = .ok false) ∧
  (leafEqual a b = .ok true → hashKey a = hashKey b)

theorem equalitySymmetric_proven : EqualitySymmetric := by
  intro a b ha hb
  have hab := guardedLeafEqual_eq_leafEqual_master a b ha hb
  have hba := guardedLeafEqual_eq_leafEqual_master b a hb ha
  refine ⟨?_, ?_, ?_⟩
  · rw [← hab, ← hba]
    exact guardedLeafEqual_symmetric a b ha hb
  · intro hne
    have htag : ActiveTag a ≠ ActiveTag b := by
      rcases a with ⟨ac, av, af, ap, ai⟩
      rcases b with ⟨bc, bv, bf, bp, bi⟩
      cases ac <;> cases bc <;> cases ap <;> cases bp <;> simp_all [ActiveTag]
    rw [← hab]
    exact guardedLeafEqual_tagDistinct a b htag
  · intro h
    exact guardedLeafEqual_hashKey a b ha hb (hab.trans h)

/-- Copy and conversion preserve all active tags and indices. -/
def LeafCopyConvert : Prop := ∀ i : UInt16, ∀ v : JF, ∀ f : JF → JF,
  leafCopy (featureLeaf i) = .ok (featureLeaf i) ∧
  leafCopy (parameterLeaf i) = .ok (parameterLeaf i) ∧
  leafCopy (constantLeaf v) = .ok (constantLeaf v) ∧
  leafConvert f (featureLeaf i) = .ok (featureLeaf i) ∧
  leafConvert f (parameterLeaf i) = .ok (parameterLeaf i) ∧
  leafConvert f (constantLeaf v) = .ok (constantLeaf (f v))

theorem leafCopyConvert_proven : LeafCopyConvert := by
  unfold LeafCopyConvert; intros; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Parameter-name count is enforced. -/
def NameCount : Prop := ∀ e : PExpression, ∀ ns,
  e.parameterNames = some ns → ns.length ≠ e.parameters.nrows →
  constructP e = .error (.assertionError "parameter_names length")

theorem nameCount_proven : NameCount := by
  intro e ns hn h
  simp [constructP, hn, h]
example : (fixture (.feature 1)).parameters.nrows ≠ ([] : List String).length := by decide

/-- Exact-length scalar array set/get replaces every entry, including empty arrays. -/
def ArrayRoundtrip : Prop := ∀ old vs : List JF,
  old.length = vs.length → setArray old vs = vs

theorem arrayRoundtrip_proven : ArrayRoundtrip := by
  intro old
  induction old with
  | nil => intro vs h; cases vs <;> simp_all [setArray]
  | cons x xs ih =>
    intro vs h
    cases vs with
    | nil => simp at h
    | cons v vs => simp only [List.length_cons, Nat.add_right_cancel_iff] at h
                   simp [setArray, ih vs h]
example : [one,two].length = [ten,twenty].length := rfl

/-- Wrong length should be rejected, rather than partially replacing parameters
(fixed in PR #245). -/
def ParameterLengthChecked : Prop := ∀ s : ConstantState, ∀ old vs,
  s.refs.Nodup → getConstants s = .ok old → vs.length ≠ old.length →
  (setConstants s vs).toOption.isNone = true

theorem parameterLength_proven : ParameterLengthChecked := by
  intro s old vs _ hg hne
  have hl := getConstants_length s old hg
  have hbad : vs.length ≠ s.refs.length + s.params.length := by omega
  rw [setConstants, if_pos hbad]
  rfl

private def state : ConstantState := ⟨Heap.empty, [], [ten,twenty]⟩

/-- Zero-sample evaluation with matching empty classes raises no class-handling
error (fixed in PR #246): it hands the converted tree and a
`(size(parameters, 1) + size(X, 1)) × 0` augmented matrix to the ordinary
evaluator, whose zero-sample behaviour is covered by eval-zero-samples-*. -/
def EmptyClassesAccepted : Prop :=
  ∀ backend : Tree JF → JMat JF → OpEnum JF → Jl (Array JF × Bool),
  ∀ e : PExpression, ∀ X : JMat JF,
  X.ncols = 0 → e.parameters.nrows < 65536 →
  ∃ Y : JMat JF, Y.nrows = e.parameters.nrows + X.nrows ∧ Y.ncols = 0 ∧
    evalP backend e X [] =
      backend (convertTree (UInt16.ofNat e.parameters.nrows) e.tree) Y e.operators

theorem emptyClasses_proven : EmptyClassesAccepted := by
  intro backend e X hX hcap
  obtain ⟨Y, hY⟩ := augment_exists_any e.parameters X [] (by simp [hX]) (by simp)
  obtain ⟨hr, hc⟩ := augment_shape _ _ _ _ hY
  refine ⟨Y, hr, by rw [hc, hX], ?_⟩
  simp [evalP, hY, convertP, checkedUInt16, hcap]

/-- Length and upper-bound checks occur before parameter indexing. -/
def ClassChecks : Prop := ∀ P X : JMat JF, ∀ classes : List Int, ∀ i c,
  (classes.length ≠ X.ncols →
    checkClasses X.ncols P.ncols classes = .error (.assertionError "class length")) ∧
  (c < 1 → parameterAt P i c = .error .boundsError) ∧
  (∀ first rest, classes = first :: rest → classes.length = X.ncols →
    Int.ofNat P.ncols < rest.foldl max first →
    checkClasses X.ncols P.ncols classes = .error (.assertionError "class upper bound"))

theorem classChecks_proven : ClassChecks := by
  intro P X classes i c
  refine ⟨?_,?_,?_⟩
  · intro h; simp [checkClasses,h]
  · intro h; simp [parameterAt,h]
  · intro first rest hc hn hmax; subst classes
    have hmax' : (P.ncols : Int) < rest.foldl max first := hmax
    simp [checkClasses,hn,hmax']

/-- Direct parameter-leaf denotation is exactly the parameter matrix at class c. -/
def ParameterDenotation : Prop := ∀ P : JMat JF, ∀ i c : Nat, ∀ o x,
  denoteP o x (fun p => (P.get? p c).toOption) (.const (.parameter i)) =
    (P.get? i c).toOption

theorem parameterDenotation_proven : ParameterDenotation := by
  unfold ParameterDenotation; intros; simp [denoteP]

/-- Conversion prepends parameter features and shifts ordinary features. -/
def ConversionTags : Prop := ∀ np i : UInt16, ∀ v : JF,
  convertTree np (.const (.parameter i.toNat)) = .feature i.toNat ∧
  convertTree np (.const (.constant v)) = .const v ∧
  convertTree np (.feature i.toNat) = .feature ((i + np).toNat)

theorem conversionTags_proven : ConversionTags := by
  intro np i v
  simp [convertTree]

/-- No wrapping below the UInt16 capacity. -/
def FeatureShift : Prop := ∀ i np : UInt16,
  i.toNat + np.toNat < 65536 → (i + np).toNat = i.toNat + np.toNat

theorem featureShift_proven : FeatureShift := by
  intro i np h
  simp [UInt16.toNat_add, Nat.mod_eq_of_lt h]
example : (1 : UInt16).toNat + (2 : UInt16).toNat < 65536 := by decide

/-- Comprehension aligns per-sample parameters and input features. -/
def AugmentationAlignment : Prop := ∀ P X Y : JMat JF, ∀ classes,
  augment P X classes = .ok Y →
  Y.nrows = P.nrows + X.nrows ∧ Y.ncols = X.ncols ∧
  (∀ i j c, 1 ≤ i ∧ i ≤ P.nrows → 1 ≤ j ∧ j ≤ X.ncols →
    classes[j-1]? = some c → Y.get? i j = parameterAt P i c) ∧
  (∀ f j, 1 ≤ f ∧ f ≤ X.nrows → 1 ≤ j ∧ j ≤ X.ncols →
    Y.get? (P.nrows+f) j = X.get? f j)

theorem augmentationAlignment_proven : AugmentationAlignment := by
  intro P X Y classes h
  exact ⟨(augment_shape P X Y classes h).1,(augment_shape P X Y classes h).2,
    fun i j c hi hj hc => augment_parameter P X Y classes i j c h hi hj hc,
    fun f j hf hj => augment_feature P X Y classes f j h hf hj⟩

/-- Mixed feature-plus-parameter evaluation agrees with the converted plain tree. -/
def ConvertedEvaluation : Prop := ∀ P X Y : JMat JF, ∀ classes t o j c,
  augment P X classes = .ok Y → P.nrows + X.nrows < 65536 →
  PLeafBounds P.nrows X.nrows t → 1 ≤ j ∧ j ≤ X.ncols → classes[j-1]? = some c →
  (convertTree (UInt16.ofNat P.nrows) t).denoteRow o Y j =
    denoteP o (fun f => (X.get? f j).toOption) (fun p => (parameterAt P p c).toOption) t

theorem convertedEvaluation_proven : ConvertedEvaluation := augmented_denotation

example : augment params input [2,1] = .ok ⟨2,2,#[twenty,one,ten,two],rfl⟩ := by rfl

/-- Callable output passes through when complete and invalidates all entries otherwise. -/
def CallableBehavior : Prop := ∀ xs : Array JF,
  callP (.ok (xs,true)) = .ok xs ∧
  callP (.ok (xs,false)) = .ok (Array.replicate xs.size .nan)

theorem callableBehavior_proven : CallableBehavior := by intro xs; exact ⟨rfl,rfl⟩

/-- Parameter-only and constant-only trees have max feature zero and render without a reduction failure. -/
def FeatureFreeRendering : Prop := ∀ e : PExpression,
  maxFeature e.tree = 0 → e.parameters.nrows < 65536 →
  (∀ names, e.parameterNames = some names → names.length = e.parameters.nrows) →
  ∃ names, stringNames e = .ok names

theorem featureFreeRendering_proven : FeatureFreeRendering := by
  intro e hmax hcap hnames
  cases hp : e.parameterNames with
  | none =>
    cases hv : e.variableNames with
    | none => simp [stringNames,checkedUInt16,hcap,hmax,hp,hv]
    | some vs => simp [stringNames,checkedUInt16,hcap,hmax,hp,hv]
  | some ps =>
    have hl := hnames ps hp
    cases hv : e.variableNames with
    | none => simp [stringNames,checkedUInt16,hcap,hmax,hp,hv,hl,
        Nat.mod_eq_of_lt hcap]
    | some vs => simp [stringNames,checkedUInt16,hcap,hmax,hp,hv,hl,
        Nat.mod_eq_of_lt hcap]

/-- Parsing preserves parameter identity, and variable names take precedence when names overlap. -/
def ParseTags : Prop := ∀ s : String, ∀ vn pn : List String, ∀ i,
  (vn.idxOf? s = some i → i+1 < 65536 →
    parseSymbol s vn pn = .ok (.feature (i+1))) ∧
  (vn.idxOf? s = none → pn.idxOf? s = some i → i+1 < 65536 →
    parseSymbol s vn pn = .ok (.const (.parameter (i+1)))) ∧
  (∀ t, parseOther (.node t) = .ok t)

theorem parseTags_proven : ParseTags := by
  intro s vn pn i
  refine ⟨?_,?_,?_⟩
  · intro h hcap; simp [parseSymbol,h,checkedUInt16,hcap,UInt16.toNat_ofNat,
      Nat.mod_eq_of_lt hcap]
  · intro h hn hcap; simp [parseSymbol,h,hn,checkedUInt16,hcap,UInt16.toNat_ofNat,
      Nat.mod_eq_of_lt hcap]
  · intro t; rfl


/-- Structure receives original named contents, including their order. -/
def StructuredComposition : Prop := ∀ s : SExpression,
  getTreeS s = s.structureFn s.trees

theorem structuredComposition_proven : StructuredComposition := by unfold StructuredComposition; intros; rfl

/-- Empty named member tuple is rejected by first(), before calling structure. -/
def EmptyStructuredRejected : Prop := ∀ f : List (String × PExpression) → PTree,
  constructS [] f = .error (.argumentError "empty first")

theorem emptyStructured_proven : EmptyStructuredRejected := by unfold EmptyStructuredRejected; intros; rfl

/-- Defaults are taken from the first member and explicit names/operators override them. -/
def StructuredMetadata : Prop := ∀ k e es f o vn,
  constructS ((k,e)::es) f (some o) (some vn) =
    .ok ⟨(k,e)::es,f,o,some vn⟩

theorem structuredMetadata_proven : StructuredMetadata := by unfold StructuredMetadata; intros; rfl


/-- Flatten uses named order and column-major parameter order within each member. -/
def StructuredFlatten : Prop := ∀ left right : List (List JF),
  flattenS (left ++ right) = flattenS left ++ flattenS right

theorem structuredFlatten_proven : StructuredFlatten := flattenS_append

/-- Exact-length set/get distributes entries across member boundaries. -/
def StructuredRoundtrip : Prop := ∀ states result : List ConstantState,
    ∀ oldGroups : List (List JF), ∀ vs,
  (∀ s ∈ states, s.refs.Nodup) → states.mapM getConstants = .ok oldGroups →
  vs.length = oldGroups.flatten.length → setS states vs = .ok result →
  (result.mapM getConstants).map List.flatten = .ok vs

theorem structuredRoundtrip_proven : StructuredRoundtrip := setS_read_values

/-- Structured setters should reject unused excess scalars (fixed in PR #245). -/
def StructuredExtraRejected : Prop := ∀ states : List ConstantState,
    ∀ oldGroups : List (List JF), ∀ vs,
  (∀ s ∈ states, s.refs.Nodup) → states.mapM getConstants = .ok oldGroups →
  oldGroups.flatten.length < vs.length → (setS states vs).toOption.isNone = true

theorem structuredExtra_proven : StructuredExtraRejected := by
  intro states oldGroups vs _ hg hlt
  have hbad : vs.length ≠ (oldGroups.map List.length).sum := by
    rw [← List.length_flatten]; omega
  simp only [setS, hg, jl_bind_ok]
  rw [if_pos hbad]
  rfl



/-- Witnesses for feature-free rendering and general parsing hypotheses. -/
example : let e := fixture (.const (.parameter 1))
    maxFeature e.tree = 0 ∧ e.parameters.nrows < 65536 ∧
    (∀ ns, e.parameterNames = some ns → ns.length = e.parameters.nrows) := by
  refine ⟨by simp [fixture,maxFeature],by decide,?_⟩
  intro ns h
  cases h

example : (["x"] : List String).idxOf? "x" = some 0 ∧ 0+1 < 65536 := by
  exact ⟨rfl,by decide⟩
example : (["x"] : List String).idxOf? "p" = none ∧
    (["p"] : List String).idxOf? "p" = some 0 ∧ 0+1 < 65536 := by
  exact ⟨rfl,rfl,by decide⟩

example : let e := fixture (.feature 1)
    let d : PContainer := ⟨[],filledBuffer e.parameters⟩
    (fun (_ : List Addr) (t : PTree) => (Except.ok t : Jl PTree)) d.slots e.tree = .ok e.tree ∧
    d.parameters.nrows = e.parameters.nrows ∧ d.parameters.ncols = e.parameters.ncols :=
  ⟨rfl,rfl,rfl⟩

example : let e := fixture (.feature 1)
    let src : SExpression := ⟨[("member",e)],fun _ => e.tree,ops,none⟩
    let d : List (String × PContainer) := [("member",⟨[],filledBuffer e.parameters⟩)]
    d.length = src.trees.length ∧
    (∀ pair ∈ d.zip src.trees,
      (fun (_ : PContainer) (value : PExpression) => (Except.ok value : Jl PExpression))
        pair.1.2 pair.2.2 = .ok pair.2.2) := by
  exact ⟨rfl,fun _ _ => rfl⟩

end DynExpr.ParamStruct
