import DynExpr.Plumbing.Deprecated
import DynExpr.NodeUtils.Success
import DynExpr.NodeUtils.GraphIndex
import DynExpr.NodeUtils.Composite
import DynExpr.Simplify.SimplifyTree

namespace DynExpr.Plumbing

/-- Base.@deprecate function warning text for src/deprecated.jl:4,79-94.
Source signatures are retained rather than depending on the actual input type. -/
def aliasWarning (name : String) : String :=
  if name = "simplify_tree" then
    "`simplify_tree(tree, operators)` is deprecated, use `simplify_tree!(tree, operators)` instead."
  else if name = "count_constants" then
    "`count_constants(tree::Union{AbstractExpression, AbstractExpressionNode})` is deprecated, use `count_constant_nodes(tree)` instead."
  else if name = "index_constants" then
    "`index_constants(tree::Union{AbstractExpression, AbstractExpressionNode}, T::Type = UInt16)` is deprecated, use `index_constant_nodes(tree, T)` instead."
  else if name = "get_constants" then
    "`get_constants(tree::Union{AbstractExpression, AbstractExpressionNode})` is deprecated, use `get_scalar_constants(tree)` instead."
  else
    "`set_constants!(tree::Union{AbstractExpression, AbstractExpressionNode}, constants, refs)` is deprecated, use `set_scalar_constants!(tree, constants, refs)` instead."

/-- src/deprecated.jl:79-82, plain-Node overload with unchanged argument. -/
def countConstants (t : Tree T) : DeprecatedResult Nat :=
  ⟨[aliasWarning "count_constants"], .ok (NodeUtils.countConstantNodes t)⟩
/-- Shared GraphNode overload of the same alias. -/
def countSharedConstants (g : Graph T) (fuel root : Nat) : DeprecatedResult Nat :=
  ⟨[aliasWarning "count_constants"], NodeUtils.sharedConstantCount g fuel root⟩
/-- src/deprecated.jl:83-86, the omitted type argument becomes UInt16. -/
def indexConstants (t : Tree T) : DeprecatedResult NodeUtils.NodeIndex :=
  ⟨[aliasWarning "index_constants"], .ok (NodeUtils.indexConstants t 0).1⟩
/-- Explicit unsigned index type: preserve its modulus, heap, and sharing policy. -/
def indexGraphConstants (g : Graph T) (sharing : Bool) (modulus fuel root : Nat) :
    DeprecatedResult NodeUtils.NodeIndex :=
  ⟨[aliasWarning "index_constants"],
    (NodeUtils.indexGraphWalk g sharing modulus fuel root 0 []).map (fun r => r.1)⟩
/-- src/deprecated.jl:87-90 returns both values and node references unchanged. -/
def getConstants (g : Graph T) (sharing : Bool) (fuel root : Nat) :
    DeprecatedResult (List T × List Addr) :=
  ⟨[aliasWarning "get_constants"], NodeUtils.getScalarConstants g sharing fuel root⟩
/-- src/deprecated.jl:91-94 preserves the reference objects and mutates their
node heap. Root identity is returned by the source setter at NodeUtils.jl:142. -/
def setConstants (g : Graph T) (root : Addr) (vs : List T) (refs : List Addr) :
    DeprecatedResult (Addr × Graph T) :=
  ⟨[aliasWarning "set_constants!"], (NodeUtils.setScalarConstants g vs refs).map (fun h => (root,h))⟩
/-- src/deprecated.jl:4 preserves operators, node identity and mutation effects. -/
def simplifyTree [JlValue T] (o : OpEnum T) (fuel : Nat) (g : Graph T) (root : Addr) :
    DeprecatedResult (Addr × Graph T) :=
  ⟨[aliasWarning "simplify_tree"], Simplify.simplifyTree o fuel g root⟩

/-- Non-number dispatch preserves the composite packing protocol and its errors. -/
def getCompositeConstants (p : NodeUtils.ValueProtocol T) (g : Graph T)
    (sharing : Bool) (fuel root : Nat) : DeprecatedResult (List JF × List Addr) :=
  ⟨[aliasWarning "get_constants"], NodeUtils.getCompositeScalarConstants p g sharing fuel root⟩
def setCompositeConstants (p : NodeUtils.ValueProtocol T) (g : Graph T) (root : Addr)
    (nums : List JF) (refs : List Addr) : DeprecatedResult (Addr × Graph T) :=
  ⟨[aliasWarning "set_constants!"],
    (NodeUtils.setCompositeConstants p g nums 1 refs).map (fun h => (root,h))⟩

/-- One compatibility concern: the five concrete aliases forward all arguments
and optional index-type information to the real public modern mirrors. Equality
is on complete exception/state results, so allocation and object identities are
also retained. The Julia aliases literally call these targets. -/
def constantsAliasTargets : Prop := ∀ (T : Type) [JlValue T]
    (t : Tree T) (g : Graph T) sharing modulus fuel root vs refs (o : OpEnum T)
    (protocol : NodeUtils.ValueProtocol T) (nums : List JF),
  (countConstants t).result = .ok (NodeUtils.countConstantNodes t) ∧
  (countSharedConstants g fuel root).result = NodeUtils.sharedConstantCount g fuel root ∧
  (indexConstants t).result = .ok (NodeUtils.indexConstants t 0).1 ∧
  (indexGraphConstants g sharing modulus fuel root).result =
    (NodeUtils.indexGraphWalk g sharing modulus fuel root 0 []).map (fun r => r.1) ∧
  (getConstants g sharing fuel root).result = NodeUtils.getScalarConstants g sharing fuel root ∧
  (setConstants g root vs refs).result = (NodeUtils.setScalarConstants g vs refs).map (fun h => (root,h)) ∧
  (simplifyTree o fuel g root).result = Simplify.simplifyTree o fuel g root ∧
  (getCompositeConstants protocol g sharing fuel root).result =
    NodeUtils.getCompositeScalarConstants protocol g sharing fuel root ∧
  (setCompositeConstants protocol g root nums refs).result =
    (NodeUtils.setCompositeConstants protocol g nums 1 refs).map (fun h => (root,h)) ∧
  (countConstants t).requested = [aliasWarning "count_constants"] ∧
  (indexConstants t).requested = [aliasWarning "index_constants"] ∧
  (setConstants g root vs refs).requested = [aliasWarning "set_constants!"] ∧
  (getConstants g sharing fuel root).requested = [aliasWarning "get_constants"] ∧
  (simplifyTree o fuel g root).requested = [aliasWarning "simplify_tree"]
theorem constantsAliasTargets_proof : constantsAliasTargets := by
  intro T inst t g sharing modulus fuel root vs refs o protocol nums
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end DynExpr.Plumbing
