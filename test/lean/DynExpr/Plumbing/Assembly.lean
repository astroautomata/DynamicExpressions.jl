import DynExpr.Runtime.Errors
import Std

namespace DynExpr.Plumbing

/-- Top-level executable includes, src/DynamicExpressions.jl:6-25,111-120,140.
The ignored language-server test include at line 138 does not execute. -/
def includes : List String := ["ValueInterface.jl", "Utils.jl", "ExtensionInterface.jl",
  "OperatorEnum.jl", "Node.jl", "NodeUtils.jl", "NodePreallocation.jl", "Strings.jl",
  "Evaluate.jl", "EvaluateDerivative.jl", "ChainRules.jl", "EvaluationHelpers.jl",
  "Simplify.jl", "OperatorEnumConstruction.jl", "Expression.jl", "ExpressionAlgebra.jl",
  "Random.jl", "Parse.jl", "ParametricExpression.jl", "StructuredExpression.jl",
  "Interfaces.jl", "NonDifferentiableDeclarations.jl", "PatchMethods.jl", "deprecated.jl",
  "precompile.jl"]

/-- Explicit re-export groups, src/DynamicExpressions.jl:41-108. The empty
EvaluationHelpersModule import exports no names. -/
def reexports : List (String × List String) := [
  ("NodeModule", ["AbstractNode", "AbstractExpressionNode", "GraphNode", "Node", "get_child",
    "set_child!", "get_children", "set_children!", "copy_node", "set_node!", "tree_mapreduce", "filter_map", "filter_map!"]),
  ("NodeUtilsModule", ["count_nodes", "count_constant_nodes", "count_depth", "NodeIndex",
    "index_constant_nodes", "has_operators", "has_constants", "count_scalar_constants", "get_scalar_constants", "set_scalar_constants!"]),
  ("StringsModule", ["string_tree", "print_tree"]),
  ("OperatorEnumModule", ["AbstractOperatorEnum"]),
  ("OperatorEnumConstructionModule", ["OperatorEnum", "GenericOperatorEnum", "@extend_operators", "set_default_variable_names!"]),
  ("EvaluateModule", ["eval_tree_array", "differentiable_eval_tree_array", "EvalContext"]),
  ("EvaluateDerivativeModule", ["eval_diff_tree_array", "eval_grad_tree_array"]),
  ("ChainRulesModule", ["NodeTangent", "extract_gradient"]),
  ("SimplifyModule", ["combine_operators", "combine_operators!", "simplify_tree!"]), ("EvaluationHelpersModule", []),
  ("ExtensionInterfaceModule", ["node_to_symbolic", "symbolic_to_node"]),
  ("RandomModule", ["NodeSampler"]),
  ("ExpressionModule", ["AbstractExpression", "Expression", "with_contents", "with_metadata", "get_contents", "get_metadata", "get_tree"]),
  ("ExpressionAlgebraModule", ["@declare_expression_operator"]),
  ("ParseModule", ["@parse_expression", "parse_expression"]),
  ("ParametricExpressionModule", ["ParametricExpression", "ParametricNode"]),
  ("StructuredExpressionModule", ["StructuredExpression"])]

/-- Independent submodule binding inventory: declarations/imports in the named
modules (src/Node.jl and base.jl, NodeUtils.jl, OperatorEnumConstruction.jl,
Evaluate.jl, Expression.jl, and the other source files named by includes).
This is binding existence, not a claim that a binding's implementation is correct. -/
def bindings (m : String) : List String :=
  if m == "NodeModule" then ["Node", "GraphNode", "AbstractNode", "AbstractExpressionNode", "copy_node", "tree_mapreduce", "filter_map", "filter_map!", "set_node!", "get_child", "set_child!", "get_children", "set_children!"]
  else if m == "NodeUtilsModule" then ["NodeIndex", "count_depth", "count_nodes", "count_constant_nodes", "has_constants", "has_operators", "index_constant_nodes", "count_scalar_constants", "get_scalar_constants", "set_scalar_constants!"]
  else if m == "StringsModule" then ["print_tree", "string_tree"]
  else if m == "OperatorEnumModule" then ["AbstractOperatorEnum", "OperatorEnum", "GenericOperatorEnum"]
  else if m == "OperatorEnumConstructionModule" then ["GenericOperatorEnum", "OperatorEnum", "set_default_variable_names!", "@extend_operators"]
  else if m == "EvaluateModule" then ["EvalContext", "eval_tree_array", "differentiable_eval_tree_array"]
  else if m == "EvaluateDerivativeModule" then ["eval_grad_tree_array", "eval_diff_tree_array"]
  else if m == "ChainRulesModule" then ["extract_gradient", "NodeTangent"]
  else if m == "SimplifyModule" then ["simplify_tree!", "combine_operators!", "combine_operators"]
  else if m == "ExtensionInterfaceModule" then ["symbolic_to_node", "node_to_symbolic"]
  else if m == "RandomModule" then ["NodeSampler"]
  else if m == "ExpressionModule" then ["Expression", "AbstractExpression", "get_tree", "get_contents", "get_metadata", "with_contents", "with_metadata"]
  else if m == "ExpressionAlgebraModule" then ["@declare_expression_operator"]
  else if m == "ParseModule" then ["parse_expression", "@parse_expression"]
  else if m == "ParametricExpressionModule" then ["ParametricNode", "ParametricExpression"]
  else if m == "StructuredExpressionModule" then ["StructuredExpression"]
  else []

/-- pkgdir, TOML parse, dictionary lookup, and VersionNumber parsing can fail;
the caught failures and missing pkgdir return 0.0.0, src/DynamicExpressions.jl:124-135.
A successful parsed version is retained verbatim. -/
def packageVersion (pkgdir : Option String) (parsedVersion : Jl String) : String :=
  match pkgdir, parsedVersion with
  | some _, .ok v => v
  | _, _ => "0.0.0"

def exportsResolve : Prop := ∀ group ∈ reexports, ∀ name ∈ group.2, name ∈ bindings group.1
theorem exportsResolve_proof : exportsResolve := by unfold exportsResolve; decide

def bootstrapOrder : Prop := includes.idxOf "Node.jl" < includes.idxOf "NodeUtils.jl" ∧
  includes.idxOf "Simplify.jl" < includes.idxOf "deprecated.jl" ∧
  includes.idxOf "Interfaces.jl" < includes.idxOf "precompile.jl" ∧
  ¬ "../test/runtests.jl" ∈ includes
theorem bootstrapOrder_proof : bootstrapOrder := by unfold bootstrapOrder; decide

def versionSuccess : Prop := ∀ dir v, packageVersion (some dir) (.ok v) = v
theorem versionSuccess_proof : versionSuccess := by intro dir v; rfl

def versionFallback : Prop := (∀ e dir, packageVersion dir (.error e) = "0.0.0") ∧
  (∀ result, packageVersion none result = "0.0.0")
theorem versionFallback_proof : versionFallback := by
  constructor
  · intro e dir; cases dir <;> rfl
  · intro result; cases result <;> rfl

/-- Project.toml version at origin/master 65884b65, also checked in repro/plumbing-checks.jl. -/
def checkoutVersion : Prop := packageVersion (some "DynamicExpressions") (.ok "2.14.0") = "2.14.0"
theorem checkoutVersion_proof : checkoutVersion := rfl

end DynExpr.Plumbing
