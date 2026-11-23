import DynExpr.Registry.Types
import DynExpr.StringsParse.GeneralBroadcast
import DynExpr.StringsParse.GeneralLiterals
import DynExpr.StringsParse.GeneralNames
import DynExpr.StringsParse.GeneralParse
import DynExpr.StringsParse.GeneralRemaining
import DynExpr.StringsParse.GeneralRoundtrip
import DynExpr.StringsParse.MacroDiagnostics

namespace DynExpr.StringsParse

private def checked (id file : String) (fns : List String) (statement conditions : String)
    (status : Registry.Status) (prop thm : Lean.Name) (notes : String := "") : Registry.Entry :=
  { id, juliaFile := file, juliaFns := fns, statement, preconditions := conditions,
    status, prop, thm := some thm, notes }

/-- Exact numerical runtime success for all finite terminating decimals,
src/Strings.jl:87-93 and src/Parse.jl:297. -/
def ExactDecimalCodec : Prop := ∀ q single, Terminating q →
  numericToken (finiteText q single) = some (scalarOf single q)
theorem exactDecimalCodec : ExactDecimalCodec := by
  intro q single h
  exact numericToken_finiteText_any h single
example : Terminating (mkRat 12 (10 ^ 30)) := terminating_decimal _ _

def entries : List Registry.Entry := [
  checked "stringsparse-roundtrip" "src/Strings.jl" ["string_tree"]
    "All clean trees preserve denotation after character-level printing and parsing, with arbitrary feature bindings and operator semantics."
    "Finite unshared trees; complete unique parseable names and matching operator spellings; finite terminating-decimal real/complex constants, no Float32 or im collision; no unary + power base; standard meanings at Julia literal-fold sites."
    .proven ``General.CleanRoundtripDenotation ``General.cleanRoundtripDenotation
    "Companion for broadcast: excludes broadcast spellings through input conditions. Unary + power bases are covered by stringsparse-negative-power (Q40).",
  checked "stringsparse-infix-grouping" "src/Strings.jl" ["string_tree", "combine_op_with_inputs"]
    "Every infix spelling encloses arbitrary operand strings in one pair of parentheses, and a spelling ending in ^ also brackets a left operand that starts with -."
    "The operator spelling starts with a supported infix character or is !=; a ^-ending spelling has a nonempty left operand."
    .proven ``General.InfixGrouping ``General.infixGrouping,
  checked "stringsparse-prefix-stripping" "src/Strings.jl" ["string_tree", "strip_brackets", "combine_op_with_inputs"]
    "Every prefix call strips one outer pair from each arbitrary nonempty operand string."
    "Nonempty operands and prefix selection from operator spelling/arity."
    .proven ``General.PrefixStripping ``General.prefixStripping,
  checked "stringsparse-print-newline" "src/Strings.jl" ["print_tree"]
    "Printing appends exactly one newline to every successful rendered result and preserves rendering errors."
    "Arbitrary renderer configuration and tree; append-only sink semantics."
    .proven ``General.PrintNewline ``General.printNewline,
  checked "stringsparse-pretty-raw" "src/Strings.jl" ["string_tree", "print_tree"]
    "An explicit pretty setting overrides every deprecated raw setting."
    "Well-typed optional Bool flags."
    .proven ``PrettyRaw ``prettyRaw,
  checked "stringsparse-negative-power" "src/Strings.jl" ["string_tree", "combine_op_with_inputs"]
    "Every clean power tree whose base is not a unary + call, including negative constants and unary - calls, reparses to its expected tree; every clean tree keeps its value when unary + operators are the identity."
    "Clean operator/name tables, valid indices, terminating real/complex constants without im collision; first clause: no unary + power base; second clause: standard fold meanings and identity unary +."
    .proven ``General.NegativePowerRoundtrip ``General.negativePowerRoundtrip
    "PR #228 brackets -led ^ bases. Q40: Miles ruled the unary + base is not a bug; +(c) ^ b reparses as +(c ^ b), which has the same value.",
  checked "stringsparse-feature-collision" "src/Strings.jl" ["string_tree", "string_variable"]
    "Supplied names print within the names vector and x<i> beyond it, and all valid features print distinctly when the supplied names are unique and do not spell the fallback of a later index."
    "Valid one-based indices up to n; unique parseable supplied names, possibly shorter than n; no supplied name equals x<k> for an index k beyond the names."
    .proven ``General.FeaturesDistinct ``General.featuresDistinct
    "Q42: Miles ruled partial variable_names falling back to xN is intended. Companion: stringsparse-complete-feature-names.",
  checked "stringsparse-empty-renderer" "src/Strings.jl" ["string_tree", "strip_brackets"]
    "Every custom constant or feature leaf renderer with nonempty output successfully renders the leaf."
    "Arbitrary custom renderer and constant/valid UInt16 feature leaf; nonempty leaf output and no deprecated varMap."
    .proven ``General.NonemptyLeafRenderer ``General.nonemptyLeafRenderer
    "Q18: empty custom renderer output is unreasonable input; nonempty output is required.",
  checked "stringsparse-empty-operator" "src/Strings.jl" ["string_tree", "combine_op_with_inputs"]
    "Every nonempty callable spelling formats every nonempty list of nonempty operand Strings."
    "Arbitrary nonempty callable display name and nonempty operand Strings."
    .proven ``General.NonemptyOperator ``General.nonemptyOperator
    "Q18: empty callable names and empty rendered operands are unreasonable input.",
  checked "stringsparse-nonfinite" "src/Strings.jl" ["string_tree", "string_constant", "_normalize_expression_for_parse"]
    "Every scalar constant, including NaN and infinities, prints and reparses to the same value, with Float32 read back as Float64."
    "Finite parts are terminating decimals; the names vector does not contain NaN or Inf, nor im for complex constants; arbitrary operators."
    .proven ``General.NonfiniteRoundtrip ``General.nonfiniteRoundtrip
    "PR #229 folds NaN, Inf, -Inf, and x*im forms. Q41: a variable named NaN or Inf shadows the constant, by analogy with Q21.",
  checked "stringsparse-float32-type" "src/Strings.jl" ["string_tree", "string_constant"]
    "Every finite terminating Float32 constant preserves its numeric value when printed and reparsed."
    "Arbitrary terminating rational value with clean matching operator/name metadata; the parsed scalar tag may become real."
    .proven ``General.CleanFloat32ValueRoundtrip ``General.cleanFloat32ValueRoundtrip
    "Q19: string_tree is display text, so precision-tag preservation is not required.",
  checked "stringsparse-shared-marker" "src/Strings.jl" ["string_tree"]
    "Every previously cached GraphNode identity renders cached text in braces without changing the cache."
    "Arbitrary graph, configuration, cached text/address, and positive traversal fuel; input cache contains the revisited identity."
    .proven ``General.SharedMarker ``General.sharedMarker,
  checked "stringsparse-dispatch-names" "src/Strings.jl" ["dispatch_op_name", "get_op_name", "get_pretty_op_name", "string_tree"]
    "Operator placeholders and display/pretty dispatch follow the degree/index and selected operator for arbitrary tables."
    "Positive degree/index and a valid lookup when a table is present; arbitrary semantics and names."
    .proven ``General.DispatchNames ``General.dispatchNames,
  checked "stringsparse-named-prefix" "src/Strings.jl" ["string_tree"]
    "Every clean named unary call reparses to its expected tree with Julia literal folds."
    "Arbitrary clean child tree and complete unique names; matching plain unary operator name."
    .proven ``General.CleanNamedPrefixRoundtrip ``General.cleanNamedPrefixRoundtrip,
  checked "stringsparse-broadcast" "src/Strings.jl" ["string_tree", "parse_expression", "_find_operator_by_name"]
    "Every well-formed tree whose operators are broadcast callables of plainly named functions has reparsable printed text."
    "Unique plain variable names without NaN or Inf; plain operator names unique per degree, each operator a broadcast callable spelled f.; finite parts of constants are terminating decimals, and im is undeclared for complex constants (Q55)."
    .proven ``General.BroadcastRoundtrip ``General.broadcastRoundtrip
    "PR #230 rewrites the printed f.(args) dot call into a call of f. and matches broadcast callables by get_op_name. Companion: stringsparse-clean-serialization requires display = plain callable name.",
  checked "stringsparse-fallback-names" "src/Strings.jl" ["string_tree", "string_variable"]
    "Every feature prints as x followed by its index when no names are supplied."
    "One-based representable feature indices in Julia; universal rendering equation also covers all natural indices."
    .proven ``FallbackFeatureNames ``fallbackFeatureNames,
  checked "stringsparse-cache-collision" "src/Strings.jl" ["get_op_name", "string_tree"]
    "After every sequence of earlier get_op_name calls, every queried callable gets its own display name."
    "Arbitrary call sequences; singleton callables with the same objectid print one name (Q44)."
    .proven ``General.CacheDisplayPreserved ``General.cacheDisplayPreserved
    "PR #231 caches names by objectid only for singleton callable types.",
  checked "stringsparse-finite-literals" "src/Parse.jl" ["parse_expression"]
    "Every literal AST value parses to the same constant and the requested node family for every configuration."
    "Arbitrary scalar literal value, operators, names, environments, and requested family."
    .proven ``General.FiniteLiteralRoundtrip ``General.finiteLiteralRoundtrip
    "The separate stringsparse-decimal-codec proves arbitrary terminating decimal text decoding, including scientific notation and f suffixes.",
  checked "stringsparse-variadic-arity" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "For every variadic arithmetic call an exact-arity operator wins over binary chaining and external evaluation."
    "Arbitrary small valid operator tables and input-grammar operands with sufficient traversal fuel; stated exact/binary/external route conditions hold."
    .proven ``General.GrammarVariadicArity ``General.grammarVariadicArity
    "Uses stringsparse-grammar-success to establish recursive parsing from ForestGrammar inputs; no recursive parse result is assumed.",
  checked "stringsparse-shared-graph" "src/Strings.jl" ["string_tree", "parse_expression"]
    "Every clean finite unshared GraphNode has reparsable character text with the same expected tree."
    "Arbitrary finite graph/root/fuel with an unfolding, unique paths to reachable identities, and clean serialization inputs."
    .proven ``General.CleanUnsharedGraphRoundtrip ``General.cleanUnsharedGraphRoundtrip
    "Q30: brace sharing markers are display-only; reparsing is promised only for unshared graphs.",
  checked "stringsparse-complex-variable" "src/Strings.jl" ["string_tree", "string_constant", "parse_expression"]
    "A declared im variable shadows the imaginary unit while the nonfinite folds still apply, and every constant roundtrips when NaN, Inf, and im are undeclared."
    "Arbitrary names vectors; the constant clause has the stringsparse-nonfinite conditions."
    .proven ``General.ComplexVariableRoundtrip ``General.complexVariableRoundtrip
    "Q43: not a bug, per Q21's ruling on a variable named im.",
  checked "stringsparse-print-io-sink" "src/Strings.jl" ["print_tree"]
    "Printing retains the sink identity and appends the rendered text, with errors preserved."
    "Arbitrary configuration/tree; the supplied address refers to an allocated append-only String sink."
    .proven ``General.PrintIOSink ``General.printIOSink,
  checked "stringsparse-constructor-family" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "All operator constructors and external-return constructors use the requested family; prebuilt leaves retain their source family."
    "Arbitrary small valid operator tables and input-grammar operands with sufficient traversal fuel; stated exact/binary/external route conditions hold."
    .proven ``General.GrammarConstructorFamily ``General.grammarConstructorFamily
    "Uses stringsparse-grammar-success to establish recursive parsing from ForestGrammar inputs; no recursive parse result is assumed.",
  checked "stringsparse-deprecated-names" "src/Strings.jl" ["string_tree", "print_tree"]
    "Deprecated varMap forwards every supplied name vector and rejects simultaneous variable_names."
    "Well-typed optional name vectors."
    .proven ``DeprecatedNames ``deprecatedNames,
  checked "stringsparse-finite-constants" "src/Strings.jl" ["string_tree", "string_constant", "parse_expression"]
    "Every clean finite terminating-decimal real or complex constant reparses to the same scalar value."
    "Unique parseable names and matching operators; finite terminating components, no Float32 tag, and im absent for complex constants."
    .proven ``General.CleanFiniteConstantRoundtrip ``General.cleanFiniteConstantRoundtrip
    "Companion for nonfinite rejection, using only finite input-value restrictions. Numerical domain follows Q21.",
  checked "stringsparse-variable-first" "src/Parse.jl" ["parse_expression", "parse_leaf"]
    "A queried name at the head of any names list selects its first matching feature index."
    "Arbitrary name and tail; first index is within UInt16 capacity."
    .proven ``VariableFirst ``variableFirst,
  checked "stringsparse-node-type" "src/Parse.jl" ["parse_expression", "parse_leaf"]
    "Every prebuilt node parses to the requested node family with its tree unchanged."
    "Arbitrary source family, tree, and parser configuration."
    .proven ``General.NodeTypeHonored ``General.nodeTypeHonored
    "PR #232: parse_leaf returns convert(node_type, ex).",
  checked "stringsparse-arity-alias" "src/Parse.jl" ["parse_expression", "_find_operator_by_name"]
    "Operator identity/alias lookup selects the first exact-degree match, and name resolution rejects missing or duplicate arity matches."
    "Arbitrary small valid operator tables, names, identities, degrees, and table prefixes."
    .proven ``General.ExactArityAlias ``General.exactArityAlias,
  checked "stringsparse-nary-chain" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "Every variadic +, -, or * call without an exact-arity match chains its arbitrary operands left-to-right."
    "Arbitrary small valid operator tables and input-grammar operands with sufficient traversal fuel; stated exact/binary/external route conditions hold."
    .proven ``General.GrammarNaryChain ``General.grammarNaryChain
    "Uses stringsparse-grammar-success to establish recursive parsing from ForestGrammar inputs; no recursive parse result is assumed.",
  checked "stringsparse-module-variable-priority" "src/Parse.jl" ["parse_expression", "parse_leaf"]
    "Every declared feature takes priority over all possible same-named module bindings."
    "Arbitrary parser configuration and queried declared name/index."
    .proven ``General.ModuleVariablePriority ``General.moduleVariablePriority,
  checked "stringsparse-module-folding" "src/Parse.jl" ["parse_expression", "_resolve_module_value"]
    "Every unresolved function recognized by eval_module evaluates the complete input AST before recursive child parsing."
    "Arbitrary AST arguments and module evaluator; resolution fails and the selected module recognizes the function. Module evaluation may return any value or error."
    .proven ``General.ModuleFolding ``General.moduleFolding,
  checked "stringsparse-external-opt-in" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "Every external function requires explicit evaluate_on opt-in after operator and chaining routes fail."
    "Arbitrary small valid operator tables and input-grammar operands with sufficient traversal fuel; stated exact/binary/external route conditions hold."
    .proven ``General.GrammarExternalOptIn ``General.grammarExternalOptIn
    "Uses stringsparse-grammar-success to establish recursive parsing from ForestGrammar inputs; no recursive parse result is assumed.",
  checked "stringsparse-complex" "src/Parse.jl" ["parse_expression", "_replace_imaginary_unit_symbol"]
    "Every clean finite terminating complex constant prints and parses to its original complex value."
    "Arbitrary terminating real and imaginary parts; matching clean operator/name tables with no im variable."
    .proven ``General.CleanComplexRoundtrip ``General.cleanComplexRoundtrip
    "Companion for stringsparse-complex-variable; the restriction is the input names vector.",
  checked "stringsparse-macro-keywords" "src/Parse.jl" ["@parse_expression", "_parse_kws"]
    "For every keyword list containing an invalid Symbol name, the first-error diagnostic lists exactly operators, variable_names, node_type, expression_type, evaluate_on, eval_module, and extra_metadata; soft-deprecated binary_operators and unary_operators are omitted but remain accepted."
    "Arbitrary Symbol keyword-name list and its first unrecognized name; interpolated values are resolved separately."
    .proven ``Macro.NondeprecatedDiagnostic ``Macro.nondeprecatedDiagnostic
    "Q34: Miles ruled that omitting the soft-deprecated operator-list keywords is intended; the diagnostic recommends operators. Companion: stringsparse-common-keywords accepts all valid consistent input-key lists.",
  checked "stringsparse-macro-parser" "src/Parse.jl" ["@parse_expression", "parse_expression"]
    "The macro routes every quoted AST and resolved configuration through the public parser."
    "Arbitrary well-typed resolved keyword values and AST; keyword assertions hold."
    .proven ``MacroCallsParser ``macroCallsParser,
  checked "stringsparse-node-exposure" "src/Parse.jl" ["parse_leaf", "parse_expression"]
    "A prebuilt node of the requested family keeps its caller-owned identity and heaps; a node of another family converts to a fresh identity leaving existing nodes and arrays unchanged."
    "Arbitrary node address, object heaps, global environment, and parser configuration."
    .proven ``General.ParsedNodeExposed ``General.parsedNodeExposed
    "PR #232 convert semantics (src/base.jl:535-552). Julia identity checks are in stringsparse-ownership-checks.jl.",
  checked "stringsparse-array-exposure" "src/Parse.jl" ["parse_leaf", "parse_expression"]
    "Every array literal is stored in a fresh constant node without copying its array identity."
    "Arbitrary caller-owned array address, object heaps, globals, and configuration; constructor value sharing is permitted."
    .proven ``General.LiteralArrayExposed ``General.literalArrayExposed,
  checked "stringsparse-module-array-exposure" "src/Parse.jl" ["parse_leaf", "parse_expression"]
    "Every module-global array retains its array identity when stored in a parsed constant."
    "Arbitrary name/global binding/object heaps/configuration; the name is absent from feature names and resolves to the array."
    .proven ``General.ModuleArrayExposed ``General.moduleArrayExposed,
  checked "stringsparse-module-result-exposure" "src/Parse.jl" ["_resolve_module_value", "parse_expression"]
    "Every module-returned array is stored without copying its live array identity."
    "Arbitrary object heaps and explicit module result containing an array reference."
    .proven ``General.ModuleResultExposed ``General.moduleResultExposed,
  checked "stringsparse-external-node-exposure" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "Every enabled external callback retains its returned node identity and heap, including callbacks returning input nodes."
    "Arbitrary argument references, object heaps, and explicit compatible callback result."
    .proven ``General.ExternalNodeExposed ``General.externalNodeExposed,
  checked "stringsparse-names-unchanged" "src/Strings.jl" ["string_tree", "print_tree"]
    "Every rendering reads variable_names without replacing its caller-owned names heap."
    "Arbitrary tree/names heap/address and default variable/constant renderers; all successful and failed result paths are modelled."
    .proven ``General.NamesUnchanged ``General.namesUnchanged,
  checked "stringsparse-complete-feature-names" "src/Strings.jl" ["string_variable", "string_tree"]
    "Every pair of valid indices has distinct rendered names in a complete unique names vector."
    "Arbitrary unique names covering both positive feature indices."
    .proven ``General.CompleteFeatureNames ``General.completeFeatureNames
    "Companion for stringsparse-feature-collision; completeness excludes fallback collisions.",
  checked "stringsparse-nonempty-strip" "src/Strings.jl" ["strip_brackets", "string_tree"]
    "Every nonempty rendered String strips at most one outer pair without a bounds error."
    "Arbitrary nonempty String; no balanced-parenthesis assumption."
    .proven ``General.NonemptyStrip ``General.nonemptyStrip
    "Q18 requires nonempty rendering output as reasonable input.",

  checked "stringsparse-compatible-node-type" "src/Parse.jl" ["parse_expression", "parse_leaf"]
    "Every prebuilt tree with the requested source family returns that family and tree unchanged."
    "Arbitrary configuration and tree; source family equals requested family."
    .proven ``General.CompatibleNodeType ``General.compatibleNodeType
    "Companion for stringsparse-node-type.",
  checked "stringsparse-collision-free-cache" "src/Strings.jl" ["get_op_name", "string_tree"]
    "For every cache, a non-singleton callable renders its own display, and a singleton callable keeps its display when every cached entry at its objectid holds that display."
    "Arbitrary cache contents and callable object."
    .proven ``General.CollisionFreeCache ``General.collisionFreeCache
    "Companion for stringsparse-cache-collision (PR #231).",
  checked "stringsparse-common-keywords" "src/Parse.jl" ["@parse_expression", "_parse_kws"]
    "Every recognized keyword list with a consistent operator source passes macro validation."
    "Arbitrary recognized names, including soft-deprecated operator-list keywords; operators excludes separate operator lists, or an operator list is supplied."
    .proven ``Macro.ValidKeywords ``Macro.validKeywords
    "Companion for stringsparse-macro-keywords; soft-deprecated names remain valid inputs despite their omission from diagnostics, without assuming validation succeeds.",
  checked "stringsparse-grammar-success" "src/Parse.jl" ["parse_expression", "_parse_expression"]
    "Every finite grammar-valid AST and operand forest parses successfully at sufficient traversal depth."
    "Arbitrary small valid operator tables/configuration; inductively valid input grammar and sufficient fuel, without parse-success assumptions."
    .proven ``General.GrammarSuccess ``General.grammarSuccess
    "Establishes recursive-success prerequisites used by arity/chaining/external/constructor route properties.",
  checked "stringsparse-clean-serialization" "src/Strings.jl" ["string_tree", "parse_expression"]
    "Every clean unshared tree has successfully rendered and reparsable character text with only Julia literal folds."
    "Clean operator/name tables, valid indices, terminating real/complex constants, no Float32/im collision/unary + power bases."
    .proven ``General.CleanSerializationRoundtrip ``General.cleanSerializationRoundtrip
    "General clean-input companion for negative-power, broadcast, nonfinite, and complex-variable bugs.",
  checked "stringsparse-fold-free-identity" "src/Strings.jl" ["string_tree", "parse_expression"]
    "Every clean tree without literal-fold sites reparses to exactly the same tree structure."
    "CleanInput and FoldFree, with arbitrary trees, operators, names, and semantics."
    .proven ``General.CleanFoldFreeIdentity ``General.cleanFoldFreeIdentity,
  checked "stringsparse-complex-normalization" "src/Parse.jl" ["_normalize_expression_for_parse", "parse_expression"]
    "A declared name keeps its symbol, an undeclared im becomes the imaginary unit, and complex-constructor folding preserves arbitrary components."
    "Arbitrary names vectors, symbols, and real/imaginary JF components."
    .proven ``General.ComplexNormalization ``General.complexNormalization,
  checked "stringsparse-decimal-codec" "src/Strings.jl" ["string_constant", "string_tree", "parse_expression"]
    "Every terminating decimal rational prints and decodes exactly for both ordinary and f-suffixed numeric tokens."
    "Arbitrary rational whose denominator divides a power of ten; arbitrary precision suffix flag, with no digit limit."
    .proven ``ExactDecimalCodec ``exactDecimalCodec
    "Q21 specifies exact terminating decimals as the numerical domain. This establishes numeric syntax success independently of package parsing."
]

end DynExpr.StringsParse
