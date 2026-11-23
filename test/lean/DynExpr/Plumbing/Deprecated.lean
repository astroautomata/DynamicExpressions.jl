import DynExpr.NodeBase.Heap
import DynExpr.Simplify.EnumProofs

namespace DynExpr.Plumbing

/-- Base.depwarn requests, subject to Julia's configured printing policy,
src/deprecated.jl:1-118. The result includes the target's error and heap state. -/
structure DeprecatedResult (R : Type) where
  requested : List String
  result : Jl R

/-- Fixed module/type compatibility bindings, src/deprecated.jl:72-77. -/
def deprecatedBindings := [("EquationModule", "NodeModule"),
  ("EquationUtilsModule", "NodeUtilsModule"), ("EvaluateEquationModule", "EvaluateModule"),
  ("EvaluateEquationDerivativeModule", "EvaluateDerivativeModule"),
  ("SimplifyEquationModule", "SimplifyModule"), ("EvalOptions", "EvalContext")]
def bindingTargets : Prop := deprecatedBindings.map Prod.snd = ["NodeModule", "NodeUtilsModule",
  "EvaluateModule", "EvaluateDerivativeModule", "SimplifyModule", "EvalContext"]
theorem bindingTargets_proof : bindingTargets := by unfold bindingTargets; decide

/-- The five positional signatures, src/deprecated.jl:6-69. An explicitly typed
constant retains its original input type and the Julia convert(T,value) method;
that method may fail before allocation. -/
inductive LegacyConstructor (T : Type) where
  | constant (degree : Int) (flag : Bool) (value : T)
  | typedConstant (inputType : Type) (degree : Int) (flag : Bool)
      (convertValue : inputType → Jl T) (value : inputType)
  | feature (degree : Int) (flag : Bool) (index : Nat)
  | unary (degree : Int) (flag : Bool) (op : Nat) (child : Addr)
  | binary (degree : Int) (flag : Bool) (op : Nat) (left right : Addr)

/-- Exact explicitly written warning text for the generated methods,
src/deprecated.jl:9-15,21-27,33-39,46-52,59-65. -/
def constructorWarning (name : String) : LegacyConstructor T → String
  | .constant _ _ _ => name ++ "(d, c, v) is deprecated. Use " ++ name ++ "{T}(val=v) instead."
  | .typedConstant _ _ _ _ _ => name ++ "(T, d, c, v) is deprecated. Use " ++ name ++ "{T}(val=v) instead."
  | .feature _ _ _ => name ++ "(T, d, c, v, f) is deprecated. Use " ++ name ++ "{T}(feature=f) instead."
  | .unary _ _ _ _ => name ++ "(d, c, v, f, o, l) is deprecated. Use " ++ name ++ "(op=o, l=l) instead."
  | .binary _ _ _ _ _ => name ++ "(d, c, v, f, o, l, r) is deprecated. Use " ++ name ++ "(op=o, l=l, r=r) instead."

/-- Assertion order and concrete keyword forwarding, src/deprecated.jl:8-68.
The unary/binary methods pass l/r; the modern ctor performs the children rewrite.
Warnings are requested before any assertion or modern constructor error. -/
def legacyConstruct (name : String) (g : NodeBase.SGraph T) (D : Nat)
    (call : LegacyConstructor T) : DeprecatedResult (Addr × NodeBase.SGraph T) :=
  let result := match call with
    | .constant d c v =>
      if d ≠ 1 then .error (.assertionError "d == 1")
      else if c = false then .error (.assertionError "c == true")
      else NodeBase.ctor g D true { val := some v }
    | .typedConstant _ d c convertValue value =>
      if d ≠ 1 then .error (.assertionError "d == 1")
      else if c = false then .error (.assertionError "c == true")
      else do
        let converted ← convertValue value
        NodeBase.ctor g D true { val := some converted }
    | .feature d c f =>
      if d ≠ 1 then .error (.assertionError "d == 1")
      else if c = true then .error (.assertionError "c == false")
      else NodeBase.ctor g D true { feature := some f }
    | .unary d _ op child =>
      if d ≠ 1 then .error (.assertionError "d == 1")
      else NodeBase.ctor g D false { op := some op, l := some child }
    | .binary d _ op left right =>
      if d ≠ 2 then .error (.assertionError "d == 2")
      else NodeBase.ctor g D false { op := some op, l := some left, r := some right }
  ⟨[constructorWarning name call], result⟩

/-- Independent specification of the accepted old signature and the modern
keyword API with explicit child tuples. -/
def validLegacy : LegacyConstructor T → Prop
  | .constant d c _ => d = 1 ∧ c = true
  | .typedConstant _ d c _ _ => d = 1 ∧ c = true
  | .feature d c _ => d = 1 ∧ c = false
  | .unary d _ _ _ => d = 1
  | .binary d _ _ _ _ => d = 2

def modernLegacyTarget (g : NodeBase.SGraph T) (D : Nat) :
    LegacyConstructor T → Jl (Addr × NodeBase.SGraph T)
  | .constant _ _ v => NodeBase.ctor g D true { val := some v }
  | .typedConstant _ _ _ convertValue value => do
    let converted ← convertValue value
    NodeBase.ctor g D true { val := some converted }
  | .feature _ _ f => NodeBase.ctor g D true { feature := some f }
  | .unary _ _ op child => NodeBase.ctor g D false { op := some op, children := some [child] }
  | .binary _ _ op left right => NodeBase.ctor g D false { op := some op, children := some [left,right] }

/-- All five signature rewrites exercise the modern constructor's control flow,
including l/r normalization, degree/operator bounds and allocation. -/
def constructorEquivalence : Prop := ∀ (T : Type) name (g : NodeBase.SGraph T) D call,
  (validLegacy call → (legacyConstruct name g D call).result = modernLegacyTarget g D call) ∧
  (¬ validLegacy call → ∃ msg, (legacyConstruct name g D call).result = .error (.assertionError msg)) ∧
  (legacyConstruct name g D call).requested = [constructorWarning name call]
theorem constructorEquivalence_proof : constructorEquivalence := by
  intro T name g D call
  refine ⟨?_, ?_, rfl⟩
  · intro h
    cases call <;>
      simp_all [validLegacy, legacyConstruct, modernLegacyTarget, NodeBase.ctor, bind, Except.bind]
  · intro h
    cases call with
    | constant d flag value =>
      by_cases hd : d = 1
      · cases flag <;> simp_all [validLegacy, legacyConstruct]
      · exact ⟨"d == 1", by simp [legacyConstruct, hd]⟩
    | typedConstant U d flag convertValue value =>
      by_cases hd : d = 1
      · cases flag <;> simp_all [validLegacy, legacyConstruct]
      · exact ⟨"d == 1", by simp [legacyConstruct, hd]⟩
    | feature d flag index =>
      by_cases hd : d = 1
      · cases flag <;> simp_all [validLegacy, legacyConstruct]
      · exact ⟨"d == 1", by simp [legacyConstruct, hd]⟩
    | unary d flag op child =>
      have hd : d ≠ 1 := h
      exact ⟨"d == 1", by simp [legacyConstruct, hd]⟩
    | binary d flag op left right =>
      have hd : d ≠ 2 := h
      exact ⟨"d == 2", by simp [legacyConstruct, hd]⟩
example : validLegacy (.binary (T := Nat) 2 false 1 0 1) := rfl
example : validLegacy (.constant 1 true (3 : Nat)) := by simp [validLegacy]

/-- Base.@deprecate embeds a compiled warning string, including source-path
and line-node printing for @nospecialize. That compile-time text is an
environment parameter; the runtime call requests it before the real target.
Source: src/deprecated.jl:95-118, including unchanged kwargs. -/
def legacyEnum (compiledWarning : String) (inBase : Simplify.Fn → Bool)
    (kind : Simplify.EnumKind) (binary unary : Option (List Simplify.Fn))
    (helpers emptyOld : Bool) (st : Simplify.Globals) :
    DeprecatedResult (List (List Simplify.Fn) × Simplify.Globals) :=
  ⟨[compiledWarning], Simplify.makeEnumKw inBase kind binary unary helpers emptyOld st⟩

/-- Source keyword constructors from the public Simplify mirror, including
helper-function/global-state options and broadcast validation, src/deprecated.jl:95-118.
Both flavours return the same ordered tuples as degree pairs and preserve the
selected modern constructor's result/state. -/
def enumEquivalence : Prop := ∀ compiledWarning inBase kind (binary unary : Option (List Simplify.Fn))
    helpers emptyOld (st : Simplify.Globals),
  (helpers = true → Simplify.EnumInput (1, unary.getD []) [(2, binary.getD [])]) →
  (legacyEnum compiledWarning inBase kind binary unary helpers emptyOld st).result =
    Simplify.makeEnum inBase kind (1, unary.getD []) [(2, binary.getD [])] helpers emptyOld st ∧
  (legacyEnum compiledWarning inBase kind binary unary helpers emptyOld st).requested = [compiledWarning] ∧
  ∃ st', (legacyEnum compiledWarning inBase kind binary unary helpers emptyOld st).result =
    .ok ([unary.getD [],binary.getD []],st')
theorem enumEquivalence_proof : enumEquivalence := by
  intro compiledWarning inBase kind binary unary helpers emptyOld st h
  exact ⟨rfl, rfl, Simplify.enum_kw_shape_proof inBase kind binary unary helpers emptyOld st h⟩
example : (false = true → Simplify.EnumInput (1, []) [(2, [])]) := by simp

end DynExpr.Plumbing
