import DynExpr.StringsParse.GeneralOwnership
import DynExpr.StringsParse.Roundtrip.Normalize

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 400000

/-- Independent specification of the signed-base bracket: a spelling ending in
`^` encloses a left operand that starts with `-` in one more pair
(`src/Strings.jl:110-114`). -/
def signedLeft (op left : String) : String :=
  if op.toList.getLast? = some '^' ∧ left.toList.head? = some '-' then "(" ++ left ++ ")" else left

/-- Infix selection depends only on the operator spelling; arbitrary operand
strings are enclosed by one pair, with the signed-base bracket on the left
operand, src/Strings.jl:106-120. -/
def InfixGrouping : Prop := ∀ op left right,
  (∃ c, op.toList.head? = some c ∧
    (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || op == "!=") = true) →
  (op.toList.getLast? = some '^' → left.toList ≠ []) →
  combineOpWithInputs op [left, right] =
    .ok ("(" ++ signedLeft op left ++ " " ++ op ++ " " ++ right ++ ")")
theorem infixGrouping : InfixGrouping := by
  intro op left right ⟨c, hh, hi⟩ hne
  simp only [combineOpWithInputs, List.length_cons, List.length_nil, Nat.reduceAdd,
    beq_self_eq_true, hh, hi, bind, Except.bind, pure, Except.pure, ↓reduceIte,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  by_cases hl : op.toList.getLast? = some '^'
  · cases h : left.toList with
    | nil => exact absurd h (hne hl)
    | cons l0 ls =>
      by_cases h0 : l0 = '-' <;> simp [signedLeft, hl, h, h0]
  · simp [signedLeft, hl]
example : ∃ c, "+".toList.head? = some c ∧
  (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || "+" == "!=") = true :=
  ⟨'+', rfl, rfl⟩
example : "^".toList.getLast? = some '^' → "-2.0".toList ≠ [] := by decide

/-- Newline printing preserves every rendering result, including errors,
`src/Strings.jl:201-223`. -/
def PrintNewline : Prop := ∀ cfg tree,
  printTree cfg tree = (stringTree cfg tree).map (fun text => text ++ "\n")
theorem printNewline : PrintNewline := by intro cfg tree; rfl

/-- The sink is read and written at the same identity; successful and failed
renderings follow the same result path, `src/Strings.jl:218-221`. -/
def PrintIOSink : Prop := ∀ cfg tree (io : Heap String) address before,
  io.cells address = some before →
  ((printTreeIO cfg tree io address).map (fun result => result.2.read address)) =
    ((printTree cfg tree).map (fun text => (Except.ok (before ++ text) : Jl String)))
theorem printIOSink : PrintIOSink := by
  intro cfg tree io address before h
  have hr : io.read address = .ok before := by simp [Heap.read, h]
  unfold printTreeIO
  rw [hr]
  cases hp : printTree cfg tree with
  | error e => rfl
  | ok text =>
    simp [bind, pure, Except.bind, Except.pure, Heap.write, h, Heap.read, Except.map]
example : (((Heap.empty : Heap String).alloc "prefix:").2).cells 0 = some "prefix:" := by rfl

/-- Name-array reads preserve caller storage on every rendering result,
`src/Strings.jl:173-182`. -/
def NamesUnchanged : Prop := ∀ cfg names address tree,
  cfg.fVariable = stringVariable → cfg.fConstant = stringConstant →
  (renderNames cfg names address tree).map Prod.snd =
    (renderNames cfg names address tree).map (fun _ => names)
theorem namesUnchanged : NamesUnchanged := by
  intro cfg names address tree _ _
  unfold renderNames
  cases hr : names.read address with
  | error error => rfl
  | ok values =>
    simp only [bind, Except.bind]
    cases ht : stringTree {cfg with names := some values} tree <;> rfl
example : renderCfg.fVariable = stringVariable ∧ renderCfg.fConstant = stringConstant := ⟨rfl, rfl⟩

/-- Declared names take priority over every possible module binding,
`src/Parse.jl:578-593`. -/
def ModuleVariablePriority : Prop := ∀ cfg name index,
  variableIndex name cfg.names = some index →
  parseLeaf cfg (.symbol name) = .ok ⟨cfg.nodeType, .feature index⟩
theorem moduleVariablePriority : ModuleVariablePriority := by
  intro cfg name index h
  simp only [parseLeaf, h]
example : variableIndex "alpha" (some ["alpha", "beta"]) = some 1 := rfl

/-- Unresolved calls evaluate the complete AST in the chosen module, without
first parsing its operands, `src/Parse.jl:394-409`. The environment may return
any value or error. -/
def ModuleFolding : Prop := ∀ cfg fuel name args env error,
  cfg.env.builtin name = none →
  findOperatorByName cfg.operators name args.length = .error error →
  cfg.moduleEnv = some env → env.functions name = true →
  parseCore cfg (fuel + 1) (.call name args) =
    (env.evaluate (.call name args) (cfg.names.getD [])).map
      (fun value => ⟨cfg.nodeType, Tree.const value⟩)
theorem moduleFolding : ModuleFolding := by
  intro cfg fuel name args env error hb ho hm hf
  simp only [parseCore, hb, ho, hm, hf, ↓reduceIte]
  rfl
private def moduleCfg : ParseConfig :=
  { env := { builtin := fun _ => none }, moduleEnv := some { functions := fun _ => true } }
example : moduleCfg.env.builtin "external" = none ∧
    findOperatorByName moduleCfg.operators "external" 1 =
      .error (.argumentError "Function not found in operators.") ∧
    ∃ env, moduleCfg.moduleEnv = some env ∧ env.functions "external" = true :=
  ⟨rfl, rfl, _, rfl, rfl⟩

/-- A declared name keeps its symbol, an undeclared `im` becomes the imaginary
unit, and the mathematical complex constructor folds arbitrary components,
`src/Parse.jl:219-249`. -/
def ComplexNormalization : Prop :=
  (∀ (names : List String) (s : String), names.contains s = true →
    normalize (some names) (.symbol s) = .symbol s) ∧
  (∀ names : List String, names.contains "im" = false →
    normalize (some names) (.symbol "im") = .literal (.complex (.fin 0) (.fin 1))) ∧
  (∀ real imag : JF, normalizeCall "+" [.literal (.real real), .literal (.complex (.fin 0) imag)] =
    .literal (.complex real imag))
theorem complexNormalization : ComplexNormalization := by
  refine ⟨?_, ?_, ?_⟩
  · intro names s h
    exact Roundtrip.normalize_symbol_mem h
  · intro names h
    exact Roundtrip.normalize_im h
  · intro real imag
    rfl
example : (["im"] : List String).contains "im" = true ∧ ([] : List String).contains "im" = false :=
  ⟨rfl, rfl⟩

/-- Nonempty operator names and operands always produce a formatted call,
`src/Strings.jl:106-133`. These conditions exclude both empty-text failures. -/
def NonemptyOperator : Prop := ∀ op args,
  op.toList.head?.isSome = true → args ≠ [] →
  (∀ text ∈ args, text.isEmpty = false) →
  ∃ text, combineOpWithInputs op args = .ok text
private theorem stripForest (args : List String) (h : ∀ text ∈ args, text.isEmpty = false) :
    ∃ texts, args.mapM stripBrackets = .ok texts := by
  induction args with
  | nil => exact ⟨[], rfl⟩
  | cons a args ih =>
    have ha := h a (by simp)
    have ht : ∀ text ∈ args, text.isEmpty = false := fun text hm => h text (by simp [hm])
    obtain ⟨texts, he⟩ := ih ht
    have hs : ∃ text, stripBrackets a = .ok text := by
      unfold stripBrackets
      simp only [ha, Bool.false_eq_true, ↓reduceIte]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨text, hs⟩ := hs
    refine ⟨text :: texts, ?_⟩
    simp only [List.mapM_cons, hs, he, bind, pure, Except.bind, Except.pure]
theorem nonemptyOperator : NonemptyOperator := by
  intro op args ho hn ht
  obtain ⟨texts, he⟩ := stripForest args ht
  have hne : args.isEmpty = false := by cases args <;> simp_all
  unfold combineOpWithInputs
  by_cases hl : (args.length == 2) = true
  · simp only [hl, ↓reduceIte]
    cases hh : op.toList.head? with
    | none => simp [hh] at ho
    | some c =>
      simp only [bind, Except.bind]
      by_cases hi : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || op == "!=") = true
      · simp only [hi, ↓reduceIte]
        obtain ⟨a, as, rfl⟩ : ∃ a as, args = a :: as := by
          cases args with
          | nil => simp at hne
          | cons a as => exact ⟨a, as, rfl⟩
        have ha := ht a (by simp)
        have hal : a.toList ≠ [] := by
          intro h
          have : a = "" := String.toList_inj.mp (by rw [h]; rfl)
          subst this
          simp at ha
        cases hla : a.toList with
        | nil => exact absurd hla hal
        | cons x xs =>
          simp only [List.getElem?_cons_zero, Option.getD_some, hla, List.head?_cons]
          split <;> exact ⟨_, rfl⟩
      · simp only [hi, hne, Bool.false_eq_true, ↓reduceIte, he, bind, pure, Except.bind, Except.pure]
        exact ⟨_, rfl⟩
  · simp only [hl, hne, Bool.false_eq_true, ↓reduceIte, he, bind, pure, Except.bind, Except.pure]
    exact ⟨_, rfl⟩
example : "f".toList.head?.isSome = true ∧ (["x"] : List String) ≠ [] ∧
  (∀ text ∈ (["x"] : List String), text.isEmpty = false) := by decide

/-- Nonempty custom leaf renderings for constants and valid UInt16 features,
src/Strings.jl:173-197. -/
def LeafRenderingInput (cfg : RenderConfig) : Tree Scalar → Prop
  | .const value => (cfg.fConstant value).isEmpty = false
  | .feature index => 1 ≤ index ∧ index ≤ 65535 ∧
      (cfg.fVariable index cfg.names).isEmpty = false
  | .branch _ _ => False
def NonemptyLeafRenderer : Prop := ∀ cfg tree,
  cfg.varMap = none → LeafRenderingInput cfg tree →
  ∃ text, stringTree cfg tree = .ok text
theorem nonemptyLeafRenderer : NonemptyLeafRenderer := by
  intro cfg tree hm he
  cases tree with
  | const value =>
    change (cfg.fConstant value).isEmpty = false at he
    simp only [stringTree, resolveNames, hm, bind, pure, Except.bind, Except.pure, rawTree]
    unfold stripBrackets
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩
  | feature index =>
    obtain ⟨_, _, he⟩ := he
    simp only [stringTree, resolveNames, hm, bind, pure, Except.bind, Except.pure, rawTree]
    unfold stripBrackets
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    split <;> exact ⟨_, rfl⟩
  | branch index children => exact False.elim he
example : renderCfg.varMap = none ∧ LeafRenderingInput renderCfg (.feature 1) := by
  exact ⟨rfl, by decide, by decide, rfl⟩
example : renderCfg.varMap = none ∧ LeafRenderingInput renderCfg (.const (num 3)) := ⟨rfl, rfl⟩



end DynExpr.StringsParse.General
