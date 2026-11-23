import DynExpr.ParamStruct.Storage

namespace DynExpr.ParamStruct

/-- Tree/metadata copy delegates to their existing interfaces,
src/ParametricExpression.jl:196-218. -/
def copyP (copyTree : PTree → PTree) (copyMetadata : PExpression → PExpression)
    (e : PExpression) : PExpression :=
  { copyMetadata e with tree := copyTree e.tree }

/-- Forbidden ambiguous constant-count utilities raise InterfaceError,
src/ParametricExpression.jl:225-237. -/
def ambiguousConstantUtility : Jl Nat := .error (.userError "InterfaceError")


/-- Gradient flattening has exactly the getter's static-then-parameter order. -/
def GradientFlattening : Prop := ∀ constants parameters : List JF,
  extractGradient constants parameters = constants ++ parameters

theorem gradientFlattening_proven : GradientFlattening := by
  unfold GradientFlattening
  intros
  rfl

/-- Every parameter leaf reads its selected matrix class after actual augmentation,
src/ParametricExpression.jl:378-397. All operators are arbitrary. -/
def ParameterClassEvaluation : Prop := ∀ P X Y : JMat JF,
    ∀ classes : List Int, ∀ o : OpEnum JF, ∀ p j c,
  augment P X classes = .ok Y → 1 ≤ p ∧ p ≤ P.nrows →
  1 ≤ j ∧ j ≤ X.ncols → classes[j-1]? = some c →
  (convertTree (UInt16.ofNat P.nrows) (.const (.parameter p))).denoteRow o Y j =
    (parameterAt P p c).toOption

theorem parameterClassEvaluation_proven : ParameterClassEvaluation := by
  intro P X Y classes o p j c h hi hj hc
  simpa [convertTree,Tree.denoteRow,Tree.denote] using
    congrArg Except.toOption (augment_parameter P X Y classes p j c h hi hj hc)

/-- First-member metadata defaults match the ordinary expression interface. -/
def StructuredDefaults : Prop := ∀ k e es f,
  constructS ((k,e)::es) f =
    .ok ⟨(k,e)::es,f,e.operators,e.variableNames⟩

theorem structuredDefaults_proven : StructuredDefaults := by
  unfold StructuredDefaults
  intros
  rfl

/-- Name-count hypotheses have a concrete satisfiable constructor input. -/
example : let P : JMat JF := ⟨1,1,#[.fin 2],rfl⟩
    let e : PExpression := ⟨.const (.constant (.fin 1)),⟨[]⟩,none,P,some []⟩
    e.parameterNames = some [] ∧ ([] : List String).length ≠ e.parameters.nrows := by
  exact ⟨rfl,by decide⟩

/-- The fresh-storage premise is inhabited by a real allocated prototype. -/
example : let P : JMat JF := ⟨1,1,#[.fin 2],rfl⟩
    0 < ((Heap.empty : MatrixStore).alloc (filledBuffer P)).2.next := by decide

/-- Oversized parameter row counts fail checked UInt16 conversion before tree
conversion or rendering, src/ParametricExpression.jl:322,410. -/
def ParameterWidthChecked : Prop := ∀ e : PExpression,
  65536 ≤ e.parameters.nrows →
  convertP e = .error (.userError "InexactError UInt16") ∧
  stringNames e = .error (.userError "InexactError UInt16")

theorem parameterWidthChecked_proven : ParameterWidthChecked := by
  intro e h
  have hn : ¬ e.parameters.nrows < 65536 := by omega
  simp [convertP, stringNames, checkedUInt16, hn]

example : let P : JMat JF := ⟨65536,0,#[],rfl⟩
    65536 ≤ P.nrows := by decide

end DynExpr.ParamStruct
