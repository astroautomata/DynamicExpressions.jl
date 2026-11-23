import DynExpr.StringsParse.Roundtrip.Graph
import DynExpr.StringsParse.Roundtrip.Float32
import DynExpr.StringsParse.Roundtrip.Nonfinite

/-! General character-level serialization roundtrip (`src/Strings.jl:71-225`,
`src/Parse.jl:209-504`). The accepted numerical runtime prints terminating
decimal rationals exactly; IEEE shortest-digit rounding and signed zero are
outside this model. Operator semantics are arbitrary, except at Julia literal
fold sites when denotation preservation is requested. Inputs are finite trees
of degree at most two with complete unique ASCII names and matching operator
spellings; complex constants require im to be absent from feature names. -/

namespace DynExpr.StringsParse.General

open DynExpr.StringsParse.Roundtrip

/-- Input-only conditions of the roundtrip. -/
def CleanInput (ops : Operators) (names : List String) (t : Tree Scalar) : Prop :=
  CleanOps ops ∧ CleanNames names ∧ t.WF 2 ops.enum.nops names.length ∧ Admissible ops names t ∧
    NoPlusBase ops t

/-- Rendering succeeds and reparsing yields the tree up to Julia's literal
folding (unary `-`/`+` on numeric literals, imaginary-unit products). -/
def CleanSerializationRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (t : Tree Scalar), CleanInput ops names t →
    ∃ text, stringTree {operators := some ops, names := some names} t = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok ⟨"Node", expect ops t⟩
theorem cleanSerializationRoundtrip : CleanSerializationRoundtrip :=
  fun _ _ t ⟨hops, hn, hw, ha, hp⟩ => roundtrip hops hn t hw ha hp

/-- Trees without fold sites reparse to themselves. -/
def CleanFoldFreeIdentity : Prop :=
  ∀ (ops : Operators) (names : List String) (t : Tree Scalar), CleanInput ops names t →
    FoldFree ops t →
    ∃ text, stringTree {operators := some ops, names := some names} t = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok ⟨"Node", t⟩
theorem cleanFoldFreeIdentity : CleanFoldFreeIdentity := by
  intro ops names t ⟨hops, hn, hw, ha, hp⟩ hf
  obtain ⟨text, hs, hp⟩ := roundtrip hops hn t hw ha hp
  rw [expect_foldFree t hf] at hp
  exact ⟨text, hs, hp⟩

/-- Under the standard meaning of the folded operators, the reparsed tree
denotes the original tree's value at every input. -/
def CleanRoundtripDenotation : Prop :=
  ∀ (ops : Operators) (names : List String) (t : Tree Scalar), CleanInput ops names t →
    StdFold ops →
    ∃ text node, stringTree {operators := some ops, names := some names} t = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok node ∧ node.tag = "Node" ∧
      ∀ x, node.tree.denote ops.enum x = t.denote ops.enum x
theorem cleanRoundtripDenotation : CleanRoundtripDenotation := by
  intro ops names t ⟨hops, hn, hw, ha, hp⟩ hstd
  obtain ⟨text, hs, hp⟩ := roundtrip hops hn t hw ha hp
  exact ⟨text, _, hs, hp, rfl, expect_denote hops hstd t hw ha⟩

/-- Unary calls of named operators other than `-`/`+` reparse to the same call
of the reparsed child. -/
def CleanNamedPrefixRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (idx : Nat) (c : Tree Scalar),
    CleanInput ops names (.branch idx [c]) → opName ops 1 idx ≠ "-" → opName ops 1 idx ≠ "+" →
    ∃ text, stringTree {operators := some ops, names := some names} (.branch idx [c]) = .ok text ∧
      parseString {operators := ops, names := some names} text =
        .ok ⟨"Node", .branch idx [expect ops c]⟩
theorem cleanNamedPrefixRoundtrip : CleanNamedPrefixRoundtrip := by
  intro ops names idx c ⟨hops, hn, hw, ha, hnp⟩ hm hp
  obtain ⟨text, hs, hparse⟩ := roundtrip hops hn _ hw ha hnp
  have h1 : (opName ops 1 idx == "-") = false := by simpa using hm
  have h2 : (opName ops 1 idx == "+") = false := by simpa using hp
  have he : expect ops (.branch idx [c]) = .branch idx [expect ops c] := by
    simp only [expect]
    unfold unaryFold
    split <;> simp_all
  rw [he] at hparse
  exact ⟨text, hs, hparse⟩

/-- Every admissible constant reparses exactly. -/
def CleanFiniteConstantRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (v : Scalar), CleanOps ops → CleanNames names →
    CleanConst (!names.contains "im") v →
    ∃ text, stringTree {operators := some ops, names := some names} (.const v) = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok ⟨"Node", .const v⟩
theorem cleanFiniteConstantRoundtrip : CleanFiniteConstantRoundtrip :=
  fun _ _ v hops hn hv =>
    roundtrip hops hn (.const v) (by simp [Tree.WF]) (by simp only [Admissible]; exact hv)
      (by simp [NoPlusBase])

/-- `Meta.parse` reads every finite terminating decimal as printed. -/
def FiniteDecimalMetaParse : Prop :=
  ∀ q : Rat, Terminating q → metaParse (realText (.fin q)) = .ok (.literal (.real (.fin q)))
theorem finiteDecimalMetaParse : FiniteDecimalMetaParse := by
  intro q htq
  have hl := lexOK_real htq (r := []) (ts := []) (by intro x hx; simp at hx) lexOK_nil
  simp only [List.append_nil] at hl
  have hlexed : lex ((realText (.fin q)).length + 1) (realText (.fin q)).toList = realToks q :=
    hl _ (by rw [String.length_toList]; simp [realText])
  have hfuel : (realToks q).length ≤ (realText (.fin q)).length + 1 := by
    rw [← hlexed]; exact lex_length _ _
  unfold metaParse
  rw [hlexed]
  exact parse_real htq _ hfuel

/-- Float32 constants print like Float64 constants, so a tree with Float32
constants roundtrips to the Float64 version of its expected tree. -/
def CleanFloat32Roundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (t : Tree Scalar), CleanOps ops → CleanNames names →
    t.WF 2 ops.enum.nops names.length → Admissible ops names (demote t) → NoPlusBase ops (demote t) →
    ∃ text, stringTree {operators := some ops, names := some names} t = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok ⟨"Node", expect ops (demote t)⟩
theorem cleanFloat32Roundtrip : CleanFloat32Roundtrip := by
  intro ops names t hops hn hw ha hp
  obtain ⟨text, hs, hp⟩ := roundtrip hops hn (demote t) (wf_demote t hw) ha hp
  rw [stringTree_demote] at hs
  exact ⟨text, hs, hp⟩

/-- A finite Float32 constant reparses as the Float64 constant of the same
value. -/
def CleanFloat32ValueRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (q : Rat), CleanOps ops → CleanNames names →
    Terminating q →
    ∃ text, stringTree {operators := some ops, names := some names} (.const (.float32 (.fin q))) =
        .ok text ∧
      parseString {operators := ops, names := some names} text = .ok ⟨"Node", .const (.real (.fin q))⟩
theorem cleanFloat32ValueRoundtrip : CleanFloat32ValueRoundtrip := by
  intro ops names q hops hn htq
  obtain ⟨text, hs, hp⟩ := cleanFloat32Roundtrip ops names (.const (.float32 (.fin q))) hops hn
    (by simp [Tree.WF]) (by simp only [demote, demoteScalar, Admissible, CleanConst]; exact htq)
    (by simp [NoPlusBase, demote])
  simp only [demote, demoteScalar, expect] at hp
  exact ⟨text, hs, hp⟩

/-- An unshared `GraphNode` graph renders as its unfolded tree and reparses,
with the `GraphNode` family requested, to the expected tree. -/
def CleanUnsharedGraphRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (g : Graph Scalar) (root : Addr) (fuel : Nat)
    (t : Tree Scalar), CleanOps ops → CleanNames names → Graph.NoAlias g root →
    Graph.unfold g fuel root = some t → t.WF 2 ops.enum.nops names.length → Admissible ops names t →
    NoPlusBase ops t →
    ∃ text, stringGraph {operators := some ops, names := some names} g fuel root = .ok text ∧
      parseString {operators := ops, names := some names, nodeType := "GraphNode"} text =
        .ok ⟨"GraphNode", expect ops t⟩
theorem cleanUnsharedGraphRoundtrip : CleanUnsharedGraphRoundtrip := by
  intro ops names g root fuel t hops hn hna hu hw ha hp
  obtain ⟨text, hs, hp⟩ := roundtripT hops hn "GraphNode" t hw ha hp
  exact ⟨text, stringGraph_tree ops names g root hna hu hs, hp⟩

/-- Every finite terminating complex constant retains its value when im is
not a feature name, src/Strings.jl:87-93 and src/Parse.jl:219-249. -/
def CleanComplexRoundtrip : Prop := ∀ ops names real imag,
  CleanOps ops → CleanNames names → names.contains "im" = false →
  Terminating real → Terminating imag →
  ∃ text, stringTree {operators := some ops, names := some names}
      (.const (.complex (.fin real) (.fin imag))) = .ok text ∧
    parseString {operators := ops, names := some names} text =
      .ok ⟨"Node", .const (.complex (.fin real) (.fin imag))⟩
theorem cleanComplexRoundtrip : CleanComplexRoundtrip := by
  intro ops names real imag ho hn hm hr hi
  apply cleanFiniteConstantRoundtrip ops names (.complex (.fin real) (.fin imag)) ho hn
  change (!names.contains "im") = true ∧ Terminating real ∧ Terminating imag
  exact ⟨by rw [hm]; rfl, hr, hi⟩

/-- `^` brackets a printed left operand that starts with `-` (PR #228),
src/Strings.jl:106-120. Power trees whose base is not a unary `+` call,
including negative constants and unary `-` calls, reparse to their expected
tree. Julia reads a printed `+(c) ^ b` as `+(c ^ b)` (Q40), so in general every
clean tree keeps its value when unary `+` operators are the identity. -/
def NegativePowerRoundtrip : Prop :=
  (∀ (ops : Operators) (names : List String) (idx : Nat) (base exponent : Tree Scalar),
    CleanInput ops names (.branch idx [base, exponent]) → opName ops 2 idx = "^" →
    ∃ text, stringTree {operators := some ops, names := some names} (.branch idx [base, exponent]) =
        .ok text ∧
      parseString {operators := ops, names := some names} text =
        .ok ⟨"Node", expect ops (.branch idx [base, exponent])⟩) ∧
  (∀ (ops : Operators) (names : List String) (t : Tree Scalar), CleanOps ops → CleanNames names →
    t.WF 2 ops.enum.nops names.length → Admissible ops names t → StdFold ops → PlusIdentity ops →
    ∃ text node, stringTree {operators := some ops, names := some names} t = .ok text ∧
      parseString {operators := ops, names := some names} text = .ok node ∧ node.tag = "Node" ∧
      ∀ x, node.tree.denote ops.enum x = t.denote ops.enum x)

theorem negativePowerRoundtrip : NegativePowerRoundtrip := by
  refine ⟨fun ops names _ _ _ hin _ => cleanSerializationRoundtrip ops names _ hin, ?_⟩
  intro ops names t hops hn hw ha hstd hplus
  obtain ⟨text, hs, hp⟩ := roundtripRotT hops hn "Node" t hw ha
  refine ⟨text, _, hs, hp, rfl, fun x => ?_⟩
  show (expect ops (rotT ops t)).denote ops.enum x = _
  rw [expect_denote hops hstd _ (rotT_wf ops t hw) (rotT_admissible ops names t ha),
    rotT_denote hplus t hw]

/-- Every scalar constant whose finite parts are terminating decimals, including
NaN and the infinities, prints and reparses to the same value, with Float32
values read back as Float64 (Q19), when the names vector does not declare `NaN`
or `Inf` (Q41) or, for complex constants, `im` (Q21). PR #229 folds the printed
`NaN`, `Inf`, `-Inf`, and `Inf*im` forms back into constants,
src/Strings.jl:87-93 and src/Parse.jl:219-249. -/
def NonfiniteRoundtrip : Prop :=
  ∀ (ops : Operators) (names : List String) (v : Scalar), ConstOK v →
    names.contains "NaN" = false → names.contains "Inf" = false →
    (∀ r i, v = .complex r i → names.contains "im" = false) →
    ∃ text, stringTree {operators := some ops, names := some names} (.const v) = .ok text ∧
      parseString {operators := ops, names := some names} text =
        .ok ⟨"Node", .const (demoteScalar v)⟩

theorem nonfiniteRoundtrip : NonfiniteRoundtrip :=
  fun ops names v hv hnan hinf him => constRoundtrip ops names v hv hnan hinf him

example : ConstOK (.complex (.fin 1) .negInf) ∧ (["x1"] : List String).contains "NaN" = false ∧
    (["x1"] : List String).contains "Inf" = false ∧
    ∀ r i, Scalar.complex (.fin 1) .negInf = .complex r i → (["x1"] : List String).contains "im" = false :=
  ⟨⟨⟨0, by simp⟩, trivial⟩, rfl, rfl, fun _ _ _ => rfl⟩

private def powOp : NamedOp := ⟨"^", "^", "^", "^", "^", false, fun _ => .real (.fin 0)⟩
private def plusOp : NamedOp := ⟨"+", "+", "+", "+", "+", false, fun xs => xs.headD (.real (.fin 0))⟩
private def plusPowOps : Operators := [[plusOp], [powOp]]

example : CleanInput plusPowOps ["x1"] (.branch 1 [.const (num (-2)), .feature 1]) ∧
    opName plusPowOps 2 1 = "^" := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · simp [CleanOps, plusPowOps, plusOp, powOp, opNameOK, infixName]
  · simp [CleanNames, plainName, asciiIdent, reservedWords]
  · simp [Tree.WF, Operators.enum, OpEnum.nops, plusPowOps]
  · simp only [Admissible, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨0, by simp⟩, trivial⟩
  · simp [NoPlusBase, PlusLed]

/-- A declared `im` variable shadows the imaginary unit (Q21, Q43), while the
nonfinite folds still apply, and every constant roundtrips when `NaN`, `Inf`,
and `im` are not declared, src/Parse.jl:219-249. -/
def ComplexVariableRoundtrip : Prop :=
  (∀ names : List String, names.contains "im" = true →
    normalize (some names) (.symbol "im") = .symbol "im") ∧
  (∀ names : List String, names.contains "Inf" = false →
    normalize (some names) (.call "-" [.symbol "Inf"]) = .literal (.real .negInf)) ∧
  NonfiniteRoundtrip

theorem complexVariableRoundtrip : ComplexVariableRoundtrip := by
  refine ⟨fun _ h => normalize_symbol_mem h, fun _ h => ?_, nonfiniteRoundtrip⟩
  rw [normalize_call, normalizeArgs_cons, normalizeArgs_nil, normalize_Inf h]
  rfl

example : (["im"] : List String).contains "im" = true ∧ (["im"] : List String).contains "Inf" = false :=
  ⟨rfl, rfl⟩

example : CleanOps plusPowOps ∧ CleanNames ["x1", "x2"] ∧
    (Tree.branch 1 [.branch 1 [.feature 1], .feature 2] : Tree Scalar).WF 2 plusPowOps.enum.nops 2 ∧
    Admissible plusPowOps ["x1", "x2"] (.branch 1 [.branch 1 [.feature 1], .feature 2]) ∧
    StdFold plusPowOps ∧ PlusIdentity plusPowOps := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CleanOps, plusPowOps, plusOp, powOp, opNameOK, infixName]
  · simp [CleanNames, plainName, asciiIdent, reservedWords]
  · simp [Tree.WF, Operators.enum, OpEnum.nops, plusPowOps]
  · simp [Admissible]
  · simp [StdFold, plusPowOps, plusOp, powOp]
  · simp [PlusIdentity, plusPowOps, plusOp]

private theorem emptyOpsClean : CleanOps [] := by simp [CleanOps]
private theorem emptyNamesClean : CleanNames [] := by simp [CleanNames]
private theorem zeroTerminating : Terminating (0 : Rat) := ⟨0, by simp⟩
private theorem featureClean : CleanInput [] ["x"] (.feature 1) := by
  simp [CleanInput, CleanOps, CleanNames, plainName, asciiIdent, reservedWords,
    Tree.WF, Admissible, NoPlusBase]

example : CleanInput [] ["x"] (.feature 1) ∧ FoldFree [] (.feature 1) ∧ StdFold [] := by
  exact ⟨featureClean, by simp [FoldFree], by simp [StdFold]⟩

private def witnessOp : NamedOp := ⟨"f", "f", "f", "f", "f", false, fun _ => .real (.fin 0)⟩
private def witnessOps : Operators := [[witnessOp]]
example : CleanInput witnessOps ["x"] (.branch 1 [.feature 1]) ∧
    opName witnessOps 1 1 ≠ "-" ∧ opName witnessOps 1 1 ≠ "+" := by
  simp [CleanInput, CleanOps, CleanNames, Tree.WF, Operators.enum, OpEnum.nops,
    Admissible, NoPlusBase, opName, opNameOK, plainName, asciiIdent, reservedWords,
    witnessOps, witnessOp]

example : CleanOps [] ∧ CleanNames [] ∧ CleanConst (!([].contains "im")) (.real (.fin 0)) :=
  ⟨emptyOpsClean, emptyNamesClean, zeroTerminating⟩
example : Terminating (0 : Rat) := zeroTerminating
example : CleanOps [] ∧ CleanNames [] ∧ Terminating (0 : Rat) :=
  ⟨emptyOpsClean, emptyNamesClean, zeroTerminating⟩
example : CleanOps [] ∧ CleanNames [] ∧
    (Tree.const (Scalar.float32 (.fin 0))).WF 2 (Operators.enum ([] : Operators)).nops 0 ∧
    Admissible [] [] (demote (.const (.float32 (.fin 0)))) ∧
    NoPlusBase [] (demote (.const (.float32 (.fin 0)))) := by
  refine ⟨emptyOpsClean, emptyNamesClean, ?_, ?_, by simp [NoPlusBase, demote]⟩
  · simp [Tree.WF]
  · simpa only [demote, demoteScalar, Admissible, CleanConst] using zeroTerminating
example : CleanOps [] ∧ CleanNames [] ∧ ([].contains "im") = false ∧
    Terminating (0 : Rat) ∧ Terminating (0 : Rat) :=
  ⟨emptyOpsClean, emptyNamesClean, rfl, zeroTerminating, zeroTerminating⟩
example : let p := Graph.ofTree (Heap.empty : Graph Scalar) (.feature 1)
    Graph.NoAlias p.2 p.1 ∧ p.2.unfold 1 p.1 = some (.feature 1) ∧
    CleanInput [] ["x"] (.feature 1) := by
  refine ⟨Graph.noAlias_ofTree _ _, ?_, featureClean⟩
  exact Graph.unfold_ofTree _ _ (by simp [Tree.Representable]) 1 (by simp [Tree.depth])

end DynExpr.StringsParse.General
