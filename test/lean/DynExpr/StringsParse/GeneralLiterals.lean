import DynExpr.StringsParse.GeneralDomain

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 400000
set_option maxRecDepth 3000

/-- Literal ASTs preserve their decoded value independently of operator/name tables,
src/Parse.jl:547-557,596-597. -/
theorem parseLiteral (cfg : ParseConfig) (v : Scalar) :
  parseExpression cfg (.literal v) = .ok ⟨cfg.nodeType, .const v⟩ := by
  unfold parseExpression normalize
  rfl

/-- Arbitrary literal AST values retain their value and requested family for
every operator/name configuration, src/Parse.jl:547-557,596-597. -/
def FiniteLiteralRoundtrip : Prop := ∀ cfg value,
  parseExpression cfg (.literal value) = .ok ⟨cfg.nodeType, .const value⟩

theorem finiteLiteralRoundtrip : FiniteLiteralRoundtrip := by
  intro cfg value
  exact parseLiteral cfg value

example : metaParse "1.25f0" = .ok (.literal (.float32 (.fin (5 / 4)))) := by decide +kernel
example : metaParse "1.0e-20" = .ok (.literal (.real (.fin (1 / (10 ^ 20 : Nat))))) := by decide +kernel



end DynExpr.StringsParse.General
