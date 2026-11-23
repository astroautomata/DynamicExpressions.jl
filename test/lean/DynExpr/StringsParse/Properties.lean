import DynExpr.StringsParse.Equality

namespace DynExpr.StringsParse

set_option maxRecDepth 3000
set_option maxHeartbeats 400000
attribute [local semireducible] Rat.add Rat.mul Rat.inv


def zero : Scalar := .real (.fin 0)
def num (n : Int) : Scalar := .real (.fin (n : Rat))
def named (name : String) (f : List Scalar → Scalar) : NamedOp :=
  ⟨name, name, name, name, name, false, f⟩
def powScalar (args : List Scalar) : Scalar :=
  match args with
  | [.real (.fin q), .real (.fin e)] =>
      if e.den = 1 && e.num ≥ 0 then .real (.fin (q ^ e.num.toNat)) else .real .nan
  | _ => .real .nan

def testOps : Operators :=
  [[named "-" (fun xs => (xs.headD zero).neg),
    named "twice" (fun xs => (xs.headD zero).add (xs.headD zero))],
   [named "+" (fun xs => (xs[0]?.getD zero).add (xs[1]?.getD zero)),
    named "-" (fun xs => (xs[0]?.getD zero).sub (xs[1]?.getD zero)),
    named "*" (fun xs => (xs[0]?.getD zero).mul (xs[1]?.getD zero)),
    named "^" powScalar]]

def renderCfg : RenderConfig := { operators := some testOps, names := some ["x1", "x2"] }
def parseCfg : ParseConfig := { operators := testOps, names := some ["x1", "x2"] }

def roundtripTree : Tree Scalar := .branch 3 [
  .branch 1 [.feature 1, .const (num 2)],
  .branch 2 [.feature 2, .const (num 3)]]

def semanticOps (f : Nat → Nat → List Scalar → Scalar) : Operators :=
  [[named "-" (f 1 1), named "twice" (f 1 2)],
   [named "+" (f 2 1), named "-" (f 2 2), named "*" (f 2 3), named "^" (f 2 4)]]

def roundtripSurface : Surface := .call "*" [
  .call "+" [.symbol "x1", .literal (num 2)],
  .call "-" [.symbol "x2", .literal (num 3)]]

theorem roundtripSyntax : metaParse "(x1 + 2.0) * (x2 - 3.0)" = .ok roundtripSurface := by
  decide +kernel

def RoundtripDenotation : Prop := ∀ f x,
  (parseString {parseCfg with operators := semanticOps f}
    (stringTree {renderCfg with operators := some (semanticOps f)} roundtripTree).toOption.get!).toOption.bind
    (fun n => n.tree.denote (semanticOps f).enum x) = roundtripTree.denote (semanticOps f).enum x

theorem roundtripDenotation : RoundtripDenotation := by
  intro f x
  have h : parseString {parseCfg with operators := semanticOps f} "(x1 + 2.0) * (x2 - 3.0)" =
      .ok ⟨"Node", roundtripTree⟩ := by
    unfold parseString
    rw [roundtripSyntax]
    change parseExpression {parseCfg with operators := semanticOps f} roundtripSurface = _
    simp only [parseExpression, roundtripSurface, surfaceDepth, argsDepth, normalize, normalizeArgs, normalizeCall]
    rfl
  have hs : stringTree {renderCfg with operators := some (semanticOps f)} roundtripTree =
      .ok "(x1 + 2.0) * (x2 - 3.0)" := by
    have da : dispatchOpName (some (semanticOps f)) 2 1 false = .ok "+" := by rfl
    have ds : dispatchOpName (some (semanticOps f)) 2 2 false = .ok "-" := by rfl
    have dm : dispatchOpName (some (semanticOps f)) 2 3 false = .ok "*" := by rfl
    simp only [stringTree, roundtripTree, rawTree, rawForest, renderCfg, resolvePretty, List.length_cons, List.length_nil]
    simp only [Option.getD_none, Option.map_none, Nat.reduceAdd]
    rw [dm, da, ds]
    decide +kernel
  unfold RoundtripDenotation at *
  rw [hs]
  change (parseString {parseCfg with operators := semanticOps f} "(x1 + 2.0) * (x2 - 3.0)").toOption.bind _ = _
  rw [h]
  rfl
example : roundtripTree.WF 2 testOps.enum.nops 2 := by
  simp [roundtripTree, Tree.WF, OpEnum.nops, testOps, Operators.enum]

def InfixGrouping : Prop := ∀ l r : String,
  combineOpWithInputs "+" [l, r] = .ok ("(" ++ l ++ " + " ++ r ++ ")")
theorem infixGrouping : InfixGrouping := by
  intro l r
  simp [combineOpWithInputs, String.append_assoc]
  rfl
example : combineOpWithInputs "+" ["a", "b"] = .ok "(a + b)" := rfl

def PrefixStripping : Prop := combineOpWithInputs "twice" ["(x1 + x2)"] = .ok "twice(x1 + x2)"
theorem prefixStripping : PrefixStripping := by unfold PrefixStripping; decide +kernel

def PrintNewline : Prop := ∀ cfg t s, stringTree cfg t = .ok s → printTree cfg t = .ok (s ++ "\n")
theorem printNewline : PrintNewline := by
  intro cfg t s h
  simp [printTree, h]
  rfl
example : printTree renderCfg (.feature 1) = .ok "x1\n" := by decide +kernel

def PrettyRaw : Prop := ∀ raw, resolvePretty (some true) raw = true ∧
  resolvePretty (some false) raw = false
theorem prettyRaw : PrettyRaw := by intro raw; exact ⟨rfl, rfl⟩
example : resolvePretty none (some true) = false := rfl

example : stringTree {fVariable := fun _ _ => ""} (.feature 1) = .error .boundsError := rfl
example (left right : String) : combineOpWithInputs "" [left, right] = .error .boundsError := rfl

def FiniteLiteralRoundtrip : Prop :=
  numericToken "1.0e-20" = some (.real (.fin (1 / (10 ^ 20 : Nat)))) ∧
  numericToken "1.0e20" = some (.real (.fin (10 ^ 20 : Nat))) ∧
  numericToken "-1.5" = some (.real (.fin (-3 / 2))) ∧
  numericToken "1.25f0" = some (.float32 (.fin (5 / 4)))
theorem finiteLiteralRoundtrip : FiniteLiteralRoundtrip := by unfold FiniteLiteralRoundtrip; decide +kernel

def finiteConstantSamples : List Scalar := [.real (.fin 1), .real (.fin (-3 / 2)),
  .real (.fin (1 / (10 ^ 20 : Nat))), .real (.fin (10 ^ 20 : Nat))]

def FiniteConstantRoundtrip : Prop := ∀ v ∈ finiteConstantSamples,
  (parseString parseCfg (stringConstant v)).toOption.map ParsedNode.tree = some (.const v)
theorem finiteConstantRoundtrip : FiniteConstantRoundtrip := by
  intro v hv
  simp only [finiteConstantSamples, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide +kernel

example : (parseString parseCfg (stringConstant (.float32 (.fin (5 / 4))))).toOption.map
    ParsedNode.tree = some (.const (.real (.fin (5 / 4)))) := by decide +kernel

def VariableFirst : Prop := ∀ s tail, variableIndex s (some (s :: tail)) = some 1
theorem variableFirst : VariableFirst := by
  intro s tail
  simp [variableIndex, List.zipIdx_cons]
example : variableIndex "y" (some ["x", "y"]) = some 2 := rfl

def ExactArityAlias : Prop :=
  findOpIndex [[{named "custom" (fun _ => zero) with alias := "+"}], []] "+" 1 = some 1 ∧
  findOpIndex [[{named "custom" (fun _ => zero) with alias := "+"}], []] "+" 2 = none ∧
  findOperatorByName [[named "f" (fun _ => zero)], [named "f" (fun _ => zero)]] "f" 2 = .ok "f" ∧
  (findOperatorByName [[named "f" (fun _ => zero), named "f" (fun _ => zero)]] "f" 1).isOk = false
theorem exactArityAlias : ExactArityAlias := by unfold ExactArityAlias; decide +kernel

def NaryChain : Prop :=
  (parseExpression parseCfg (.call "-" [.symbol "x1", .symbol "x2", .literal (num 3)])).toOption.map
    ParsedNode.tree = some (.branch 2 [.branch 2 [.feature 1, .feature 2], .const (num 3)])
theorem naryChain : NaryChain := by unfold NaryChain; decide +kernel

def ModuleVariablePriority : Prop := ∀ v,
  parseLeaf {parseCfg with moduleEnv := some {globals := fun _ => some v}} (.symbol "x1") =
    .ok ⟨"Node", .feature 1⟩
theorem moduleVariablePriority : ModuleVariablePriority := by intro v; rfl
example : parseLeaf {parseCfg with moduleEnv := some {globals := fun _ => some (num 9)}}
  (.symbol "x1") = .ok ⟨"Node", .feature 1⟩ := rfl

def ModuleFolding : Prop := ∀ v,
  parseExpression {parseCfg with moduleEnv := some {
    functions := (fun _ => true)
    evaluate := (fun _ _ => .ok v)}} (.call "external_constant" [.literal (num 2)]) =
      .ok ⟨"Node", .const v⟩
theorem moduleFolding : ModuleFolding := by intro v; rfl
example : parseExpression {parseCfg with moduleEnv := some {
  functions := (fun _ => true)
  evaluate := (fun _ _ => .ok (num 7))}} (.call "external_constant" [.literal (num 2)]) =
    .ok ⟨"Node", .const (num 7)⟩ := rfl

def ExternalOptIn : Prop :=
  (parseExpression {parseCfg with env := {builtin := fun _ => some "external"}}
    (.call "external" [.symbol "x1"])).isOk = false ∧
  (parseExpression {parseCfg with evaluateOn := ["external"], env := {
    builtin := fun _ => some "external", external := fun _ cs => .ok (cs.headD ⟨"Node", .feature 0⟩)}}
    (.call "external" [.symbol "x1"])).toOption.map ParsedNode.tree = some (.feature 1)
theorem externalOptIn : ExternalOptIn := by unfold ExternalOptIn; decide +kernel

def ComplexRoundtrip : Prop :=
  (parseString parseCfg (stringConstant (.complex (.fin 1) (.fin 2)))).toOption.map ParsedNode.tree =
    some (.const (.complex (.fin 1) (.fin 2))) ∧
  normalize (some ["im"]) (.symbol "im") = .symbol "im"
theorem complexRoundtrip : ComplexRoundtrip := by
  constructor
  · decide +kernel
  · rfl



def MacroCallsParser : Prop := ∀ cfg ex, parseMacro cfg ex = parseExpression cfg ex
theorem macroCallsParser : MacroCallsParser := by intro cfg ex; rfl
example : parseMacro parseCfg (.symbol "x1") = .ok ⟨"Node", .feature 1⟩ := by decide +kernel

def graphExample : Addr × Graph Scalar := Id.run do
  let (a, g) := (Heap.empty : Graph Scalar).alloc ⟨0, false, none, 1, 0, []⟩
  return g.alloc ⟨2, false, none, 0, 1, [a, a]⟩
def SharedMarker : Prop := stringGraph renderCfg graphExample.2 3 graphExample.1 = .ok "x1 + {x1}"
theorem sharedMarker : SharedMarker := by unfold SharedMarker; decide +kernel

def DispatchNames : Prop :=
  dispatchOpName none 3 2 false = .ok "operator_deg3[2]" ∧
  broadcastName "+" = ".+" ∧ broadcastName "cos" = "cos." ∧
  dispatchOpName (some [[{named "f" (fun _ => zero) with pretty := "F"}]]) 1 1 true = .ok "F"
theorem dispatchNames : DispatchNames := by unfold DispatchNames; decide +kernel

def NamedPrefixRoundtrip : Prop :=
  (parseString parseCfg (stringTree renderCfg (.branch 2 [roundtripTree])).toOption.get!).toOption.map
    ParsedNode.tree = some (.branch 2 [roundtripTree])
theorem namedPrefixRoundtrip : NamedPrefixRoundtrip := by unfold NamedPrefixRoundtrip; decide +kernel

example : (parseString {parseCfg with operators := [[{named "cos" (fun _ => zero) with
    identity := "broadcast_cos", display := "cos.", pretty := "cos.", broadcast := true}]]}
    "cos.(x1)").toOption.map ParsedNode.tree = some (.branch 1 [.feature 1]) := by decide +kernel

def FallbackFeatureNames : Prop := ∀ i, stringVariable i none = "x" ++ toString i
theorem fallbackFeatureNames : FallbackFeatureNames := by intro i; rfl
example : stringVariable 2 (some ["alpha"]) = "x2" := rfl

def DeprecatedNames : Prop := ∀ ns, resolveNames none (some ns) = .ok (some ns) ∧
  (resolveNames (some ns) (some ns)).isOk = false
theorem deprecatedNames : DeprecatedNames := by intro ns; exact ⟨rfl, rfl⟩
example : resolveNames none (some ["alpha"]) = .ok (some ["alpha"]) := rfl

def ConstructorFamilyConversion : Prop :=
  (parseExpression {parseCfg with nodeType := "GraphNode"}
    (.call "+" [.node "Node" (.feature 1), .literal (num 2)])).toOption.map ParsedNode.tag = some "GraphNode" ∧
  (parseExpression {parseCfg with nodeType := "GraphNode", evaluateOn := ["external"], env := {
    builtin := fun _ => some "external", external := fun _ cs => .ok (cs.headD ⟨"Node", .feature 0⟩)}}
    (.call "external" [.node "Node" (.feature 1)])).toOption.map ParsedNode.tag = some "GraphNode"
theorem constructorFamilyConversion : ConstructorFamilyConversion := by
  unfold ConstructorFamilyConversion
  decide +kernel

example : (parseString {parseCfg with nodeType := "GraphNode"}
    (stringGraph renderCfg graphExample.2 3 graphExample.1).toOption.get!).isOk = false := by
  rw [sharedMarker]
  decide +kernel

def VariadicArityPriority : Prop :=
  (parseString {
    operators := [[], [], [named "+" (fun _ => zero)]]
    names := some ["x1", "x2", "x3"]
    nodeType := "Node3"} "x1 + x2 + x3").toOption.map
    ParsedNode.tree = some (.branch 1 [.feature 1, .feature 2, .feature 3])
theorem variadicArityPriority : VariadicArityPriority := by unfold VariadicArityPriority; decide +kernel

def sharedBranchGraph : Addr × Graph Scalar := Id.run do
  let (left, g) := (Heap.empty : Graph Scalar).alloc ⟨0, false, none, 1, 0, []⟩
  let (right, g) := g.alloc ⟨0, false, none, 2, 0, []⟩
  let (child, g) := g.alloc ⟨2, false, none, 0, 3, [left, right]⟩
  pure (g.alloc ⟨2, false, none, 0, 1, [child, child]⟩)

example : stringGraph renderCfg sharedBranchGraph.2 3 sharedBranchGraph.1 =
  .ok "(x1 * x2) + {(x1 * x2)}" := by decide +kernel

end DynExpr.StringsParse
