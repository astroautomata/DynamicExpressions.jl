import DynExpr.Registry.Types
import DynExpr.Registry.Generality
import DynExpr.NodeBase
import DynExpr.NodeUtils
import DynExpr.Eval
import DynExpr.Deriv
import DynExpr.Simplify
import DynExpr.StringsParse
import DynExpr.Expressions
import DynExpr.ParamStruct
import DynExpr.Plumbing
import DynExpr.NoAlias

namespace DynExpr.Registry

/-- Every registered property. Each slice contributes its own `entries`. -/
def all : List Entry :=
  DynExpr.NodeBase.entries
    ++ DynExpr.NodeUtils.entries
    ++ DynExpr.Eval.entries
    ++ DynExpr.Deriv.entries
    ++ DynExpr.Simplify.entries
    ++ DynExpr.StringsParse.entries
    ++ DynExpr.Expressions.entries
    ++ DynExpr.ParamStruct.entries
    ++ DynExpr.Plumbing.entries
    ++ DynExpr.NoAlias.entries

/-- Ids of properties about fixed package code that takes no inputs (include
order, registration tables, version string). Every other property must
quantify over inputs. Add to this list only with a justification in review. -/
def staticFacts : List String := [
  "plumbing-include-order",            -- fixed include sequence in src/DynamicExpressions.jl
  "plumbing-checkout-version",         -- version string in Project.toml
  "plumbing-parametric-registration",  -- fixed interface registration table
  "plumbing-legacy-bindings",          -- fixed deprecated binding table
  "deriv-nondiff-inventory",           -- fixed @non_differentiable registration table
  "plumbing-exports",                  -- fixed re-export lists in src/DynamicExpressions.jl
  "plumbing-workload-api"              -- fixed list of API names called by src/precompile.jl
]

end DynExpr.Registry
