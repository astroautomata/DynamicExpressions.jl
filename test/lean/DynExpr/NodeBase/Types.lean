import DynExpr.Runtime.Errors
import DynExpr.Model.Tree

/-!
Type-level model of node construction, promotion and conversion
(`src/Node.jl:308-483`, `src/base.jl:193-201,496-564`).

Only the observable node types are modelled: the wrapper (`Node` or
`GraphNode`), the element type `T`, and the maximum degree `D`. Type
expressions may leave `T` or `D` unspecified (Julia `UnionAll`s such as
`Node` or `Node{Float64}`).
-/

namespace DynExpr.NodeBase

/-- Concrete node wrappers declared at `src/Node.jl:75-91`. -/
inductive Kind where
  | node
  | graph
  deriving DecidableEq, Repr

/-- Element types used in the observable promotion rules: three concrete
numeric types and the abstract `Real`. -/
inductive Elt where
  | float32
  | float64
  | int64
  | real
  deriving DecidableEq, Repr

/-- Julia `promote_type` on the modelled element types
(`promote_type(Float32, Int64) == Float32`, anything with `Real` is `Real`). -/
def promoteElt : Elt → Elt → Elt
  | .real, _ | _, .real => .real
  | .float64, _ | _, .float64 => .float64
  | .float32, _ | _, .float32 => .float32
  | .int64, .int64 => .int64

/-- Runtime type `rt` of a value is a subtype of the declared element type. -/
def isaElt (rt decl : Elt) : Bool := rt == decl || decl == .real

/-- A node type expression such as `Node` (`⟨node, none, none⟩`),
`Node{Float64}` (`⟨node, some float64, none⟩`) or `GraphNode{Real,3}`. -/
structure NType where
  kind : Kind
  elt : Option Elt
  deg : Option Nat
  deriving DecidableEq, Repr

/-- Concrete type `N{T,D}` of a node object (`src/Node.jl:76`). -/
structure CType where
  kind : Kind
  elt : Elt
  deg : Nat
  deriving DecidableEq, Repr

/-- A concrete type viewed as a type expression. -/
def CType.asN (c : CType) : NType := ⟨c.kind, some c.elt, some c.deg⟩

/-- `max_degree` (`src/Node.jl:308-310`): unspecified `D` defaults to
`DEFAULT_MAX_DEGREE = 2` (`src/Node.jl:9`). -/
def maxDegree (N : NType) : Nat := N.deg.getD 2

/-- `defines_eltype` (`src/Node.jl:443-444`). -/
def definesEltype (N : NType) : Bool := N.elt.isSome

/-- `with_type_parameters` (`src/Node.jl:325-327`). -/
def withTypeParameters (N : NType) (T : Elt) : CType := ⟨N.kind, T, maxDegree N⟩

/-- `constructorof` (`src/Node.jl:322-324`): wrapper with `D` fixed, `T` free. -/
def constructorOf (c : CType) : NType := ⟨c.kind, none, some c.deg⟩

/-- `node_factory_type` (`src/Node.jl:432-442`); `T1 = none` is `Undefined`. -/
def nodeFactoryType (N : NType) (T1 : Option Elt) (T2 : Elt) : Elt :=
  match T1, N.elt with
  | none, none => T2
  | none, some e => e
  | some t, none => t
  | some _, some e => e

/-- `has_max_degree` (`src/Node.jl:312-313`). -/
def hasMaxDegree (N : NType) : Bool := N.deg.isSome

/-- `convert(N1, tree::N2)` for fully specified `N1` (`src/base.jl:535-553`):
identity on equal types; otherwise an `ArgumentError` only when the target
degree is below the source degree and some node of the tree has a degree
above the target (`src/base.jl:541-543`). `md` is the largest node degree
in the tree (`any(t -> t.degree > D1, tree)` is `D1 < md`). Raising the
maximum degree always succeeds. -/
def convertFull (N1 src : CType) (md : Nat) : Jl CType :=
  if N1 = src then .ok src
  else if N1.deg < src.deg ∧ N1.deg < md then
    .error (.argumentError "Cannot convert: a node has degree above D1.")
  else .ok N1

/-- Result type of `convert(N1, tree)` (`src/base.jl:535-564`) on a tree
whose largest node degree is `md`. The second method fills `D` from the
source (`src/base.jl:554-558`); the third fills `T` from the source and keeps
`D` from `N1` when `N1` has one, else from the source (`src/base.jl:559-564`). -/
def convertType (N1 : NType) (src : CType) (md : Nat) : Jl CType :=
  match N1.elt, N1.deg with
  | some t, some d => convertFull ⟨N1.kind, t, d⟩ src md
  | some t, none => convertFull ⟨N1.kind, t, src.deg⟩ src md
  | none, d => convertFull ⟨N1.kind, src.elt, d.getD src.deg⟩ src md

/-- `promote_type(map(eltype, children)...)` for a nonempty list of children. -/
def promoteAll : List CType → Option Elt
  | [] => none
  | c :: cs => some (cs.foldl (fun e d => promoteElt e d.elt) c.elt)

/-- `max_degree(eltype(children))` for a nonempty children tuple
(`src/Node.jl:308-309,422`). Julia's tuple `eltype` is the
`promote_typejoin` of the child types, which keeps the maximum degree `D`
exactly when every child has the same `D`; otherwise `max_degree` of the
join falls back to `DEFAULT_MAX_DEGREE = 2` (`src/Node.jl:9`). -/
def childrenMaxDegree : List CType → Nat
  | [] => 2
  | c :: cs => if cs.all (fun d => d.deg == c.deg) then c.deg else 2

/-- Maximum degree of the node built by the branch constructor
(`src/Node.jl:419-423`): `N`'s when `has_max_degree(N)`, else the children's.
The empty-tuple case keeps `N`, whose `max_degree` is the default 2. -/
def ctorDegree (N : NType) (tys : List CType) : Nat :=
  match N.deg with
  | some d => d
  | none => childrenMaxDegree tys

/-- Result type of the branch constructor `N(T1; op, children)`
(`src/Node.jl:407-430`). `T1` is ignored. Each child is given with its
concrete type and its largest node degree. The new node's maximum degree is
`N`'s when `N` fixes one, else the children's (`src/Node.jl:419-423`). Each
child is converted to the parent's type when stored into the children tuple
(`src/Node.jl:235-254`, `src/Utils.jl:94-96`). Children are modelled as a
tuple; the `AbstractVector` branch of `src/Node.jl:412-413` gives the same
element type for a concretely typed vector. -/
def ctorBranchType (N : NType) (children : List (CType × Nat)) : Jl CType := do
  let tys := children.map Prod.fst
  let T ← match N.elt, promoteAll tys with
    | some e, _ => pure e
    | none, some e => pure e
    | none, none => throw (.methodError "promote_type() of no children")
  if definesEltype N ∧ tys.foldl (fun e d => promoteElt e d.elt) T ≠ T then
    throw (.assertionError "T === promote_type(T, map(eltype, children)...)")
  let D := ctorDegree N tys
  if tys.length > D then
    throw (.assertionError "D2 <= max_degree(NT)")
  let nt : CType := ⟨N.kind, T, D⟩
  let _ ← children.mapM (fun c => convertType nt.asN c.1 c.2)
  return nt

/-- Result type of the constant-leaf constructor `N(T1; val)` where the value
has runtime type `vt` (`src/Node.jl:385-394`). -/
def ctorValType (N : NType) (T1 : Option Elt) (vt : Elt) : CType :=
  withTypeParameters N (nodeFactoryType N T1 vt)

/-- Result type of the feature-leaf constructor `N(T1; feature)`
(`src/Node.jl:396-405`, default `Float32` from `src/Node.jl:8`). -/
def ctorFeatureType (N : NType) (T1 : Option Elt) : CType :=
  withTypeParameters N (nodeFactoryType N T1 .float32)

/-- Largest node degree in a tree (`maximum(t.degree for t in tree)`). -/
def maxNodeDeg {α : Type} : Tree α → Nat
  | .const _ | .feature _ => 0
  | .branch _ cs => (cs.map maxNodeDeg).foldr max cs.length

/-- Result type of `copy_node` on a tree of concrete type `c` whose constant
leaves hold values of the given runtime types (`src/base.jl:496-510`):
`leaf_copy` calls `constructorof(N)(T; val=copy_value(t.val::T))` or
`constructorof(N)(T; feature)` (the explicit `T` fixes the element type;
`copy_value` keeps the runtime type, `src/ValueInterface.jl:82`);
`branch_copy` calls `constructorof(N)(T; op, children)`, whose `T` the branch
constructor ignores. Plain `Node` only: no identity map conversion. -/
def copyType (c : CType) : Tree Elt → Jl CType
  | .const vt => .ok (ctorValType (constructorOf c) (some c.elt) vt)
  | .feature _ => .ok (ctorFeatureType (constructorOf c) (some c.elt))
  | .branch _ cs => do
    let ts ← copyForest c cs
    ctorBranchType (constructorOf c) ts
where
  copyForest (c : CType) : List (Tree Elt) → Jl (List (CType × Nat))
    | [] => .ok []
    | t :: ts => do
      let a ← copyType c t
      let as ← copyForest c ts
      return (a, maxNodeDeg t) :: as

/-- `promote_rule` for node types (`src/Node.jl:471-483`) followed by Julia's
`promote`: the promoted type has the promoted element type and the larger
maximum degree, and a rule covers every pair of node types. -/
def promoteNodes (a b : CType) : Jl CType :=
  if a = b then .ok a
  else .ok ⟨if a.kind = .graph ∨ b.kind = .graph then .graph else .node,
      promoteElt a.elt b.elt, max a.deg b.deg⟩

/-- Whether `a == b` (`src/base.jl:193-195`) returns normally at the type
level: it promotes both sides and then converts each to the promoted type.
`ma` and `mb` are the largest node degrees of the two trees. -/
def eqTypeOk (a b : CType) (ma mb : Nat) : Jl Unit := do
  let p ← promoteNodes a b
  let _ ← convertType p.asN a ma
  let _ ← convertType p.asN b mb
  return ()

/-- Decidable equality of Julia call results, used to settle concrete
counterexamples by `decide`. -/
scoped instance instDecEqJl {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (by injection e))
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-! ## Lemmas -/

/-- `promote_type(T, T) == T`. -/
theorem promoteElt_self (e : Elt) : promoteElt e e = e := by cases e <;> rfl

/-- Promoting a list of copies of one type gives that type. -/
theorem foldl_promote_same (e : Elt) :
    ∀ (l : List CType), (∀ d ∈ l, d.elt = e) → l.foldl (fun x d => promoteElt x d.elt) e = e := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons d l ih =>
    intro h
    simp only [List.foldl_cons, h d (by simp), promoteElt_self]
    exact ih (fun x hx => h x (by simp [hx]))

/-- A successful `mapM` from successful elementwise calls. -/
theorem mapM_ok {α β : Type} (f : α → Jl β) :
    ∀ l : List α, (∀ x ∈ l, ∃ r, f x = .ok r) → ∃ rs, l.mapM f = .ok rs
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨r, hr⟩ := h x (by simp)
    obtain ⟨rs, hrs⟩ := mapM_ok f xs (fun y hy => h y (by simp [hy]))
    exact ⟨r :: rs, by simp [List.mapM_cons, hr, hrs]; rfl⟩

/-- Conversion succeeds when it does not lower the maximum degree below a
node of the tree. -/
theorem convertFull_ok (N1 src : CType) (md : Nat) (h : src.deg ≤ N1.deg ∨ md ≤ N1.deg) :
    ∃ r, convertFull N1 src md = .ok r := by
  unfold convertFull
  by_cases he : N1 = src
  · exact ⟨src, by rw [if_pos he]⟩
  · have hd : ¬ (N1.deg < src.deg ∧ N1.deg < md) := by omega
    exact ⟨N1, by rw [if_neg he, if_neg hd]⟩

/-- The branch constructor through a type that leaves `T` free: with a
nonempty children list whose conversions to the new node type succeed, the
result has the promoted element type and the constructor's degree. -/
theorem ctorBranchType_noelt (k : Kind) (dopt : Option Nat) (c0 : CType × Nat)
    (cs : List (CType × Nat)) (D : Nat)
    (hD : ctorDegree ⟨k, none, dopt⟩ (c0.1 :: cs.map Prod.fst) = D)
    (hlen : cs.length + 1 ≤ D)
    (hconv : ∀ d ∈ c0 :: cs, d.1.deg ≤ D ∨ d.2 ≤ D) :
    ctorBranchType ⟨k, none, dopt⟩ (c0 :: cs) =
      .ok ⟨k, (cs.map Prod.fst).foldl (fun e d => promoteElt e d.elt) c0.1.elt, D⟩ := by
  obtain ⟨rs, hrs⟩ := mapM_ok
    (fun c : CType × Nat => convertType
      (⟨k, (cs.map Prod.fst).foldl (fun e d => promoteElt e d.elt) c0.1.elt, D⟩ : CType).asN c.1 c.2)
    (c0 :: cs) (fun d hd => convertFull_ok _ _ _ (hconv d hd))
  have hnle : ¬ (c0.1 :: cs.map Prod.fst).length > D := by simp; omega
  simp only [ctorBranchType, List.map_cons, promoteAll, definesEltype, Option.isSome_none,
    Bool.false_eq_true, false_and, ite_false, hD, hnle, pure_bind]
  rw [hrs]
  rfl

/-- `n ≥ 1` copies of one child type `N{T,D}` with node degrees `≤ D`, through
a constructor type `N{_,D}` or the bare wrapper `N`, give a node of type
`N{T,D}`. -/
theorem ctorBranchType_replicate (c : CType) (m n : Nat) (dopt : Option Nat)
    (hd : dopt = some c.deg ∨ dopt = none) (h1 : 1 ≤ n) (h2 : n ≤ c.deg) :
    ctorBranchType ⟨c.kind, none, dopt⟩ (List.replicate n (c, m)) = .ok c := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hD : ctorDegree ⟨c.kind, none, dopt⟩
      ((c, m).1 :: (List.replicate n (c, m)).map Prod.fst) = c.deg := by
    rcases hd with rfl | rfl
    · rfl
    · simp [ctorDegree, childrenMaxDegree]
  rw [List.replicate_succ, ctorBranchType_noelt c.kind dopt (c, m) _ c.deg hD
    (by simp; omega) (fun d hd => by
      rw [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Or.inl (Nat.le_refl _)
      · rw [(List.mem_replicate.mp hd).2]; exact Or.inl (Nat.le_refl _))]
  have : ((List.replicate n (c, m)).map Prod.fst).foldl (fun e d => promoteElt e d.elt) c.elt =
      c.elt := foldl_promote_same c.elt _ (fun d hd => by
        simp only [List.map_replicate, List.mem_replicate] at hd
        rw [hd.2])
  simp only [this]

/-! ## Properties -/

/-- Constructor types: leaves take `T` from the type, then the explicit `T1`,
then the value's runtime type (feature default `Float32`); branches whose
children share the parent's degree get the promoted element type and keep
that degree. -/
def ctor_type : Prop :=
  (∀ k vt, ctorValType ⟨k, none, none⟩ none vt = ⟨k, vt, 2⟩) ∧
  (∀ k t vt, ctorValType ⟨k, none, none⟩ (some t) vt = ⟨k, t, 2⟩) ∧
  (∀ k t D vt, ctorValType ⟨k, some t, some D⟩ none vt = ⟨k, t, D⟩) ∧
  (∀ k, ctorFeatureType ⟨k, none, none⟩ none = ⟨k, .float32, 2⟩) ∧
  (∀ k D (cs : List (CType × Nat)) (c : CType × Nat), c ∈ cs →
    (∀ d ∈ cs, d.1.kind = k ∧ d.1.deg = D ∧ d.2 ≤ D) → cs.length ≤ D →
    ∃ e, promoteAll (cs.map Prod.fst) = some e ∧
      ctorBranchType ⟨k, none, some D⟩ cs = .ok ⟨k, e, D⟩)

theorem ctor_type_holds : ctor_type := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k vt; rfl
  · intro k t vt; rfl
  · intro k t D vt; rfl
  · intro k; rfl
  · intro k D cs c hc hall hlen
    cases cs with
    | nil => simp at hc
    | cons c0 cs =>
      refine ⟨_, rfl, ?_⟩
      exact ctorBranchType_noelt k (some D) c0 cs D rfl (by simpa using hlen)
        (fun d hd => Or.inl (Nat.le_of_eq (hall d hd).2.1))

/-- Converting a node to its own unparameterised wrapper type (`convert(Node,
tree)`, also reached by `Node(tree)` at `src/base.jl:565-567`) succeeds and
keeps the tree's type. -/
def convert_unparam : Prop :=
  ∀ (c : CType) (md : Nat), 1 ≤ c.deg → md ≤ c.deg → convertType ⟨c.kind, none, none⟩ c md = .ok c

theorem convert_unparam_holds : convert_unparam := by
  intro c md _ _
  obtain ⟨k, e, d⟩ := c
  simp [convertType, convertFull]

/-- The branch constructor called through the bare wrapper (`Node(; op,
children)`) accepts children that all have one concrete type `N{T,D}` when
their number is at most `D`, producing a node of type `N{T,D}`. Each child is
given with its largest node degree `m ≤ D`. -/
def ctor_children_degree : Prop :=
  ∀ (c : CType) (n m : Nat), 1 ≤ n → n ≤ c.deg → m ≤ c.deg →
    ctorBranchType ⟨c.kind, none, none⟩ (List.replicate n (c, m)) = .ok c

theorem ctor_children_degree_holds : ctor_children_degree := by
  intro c n m h1 h2 _
  exact ctorBranchType_replicate c m n none (Or.inr rfl) h1 h2

/-- Runtime types of the constants of a tree, in traversal order. -/
def constTypes : Tree Elt → List Elt
  | .const vt => [vt]
  | .feature _ => []
  | .branch _ cs => go cs
where
  go : List (Tree Elt) → List Elt
    | [] => []
    | t :: ts => constTypes t ++ go ts

/-- `==` between two nodes returns a `Bool` (never throws) for any two
modelled node types; `ma` and `mb` are the largest node degrees of the two
trees. -/
def eq_no_throw : Prop :=
  ∀ (a b : CType) (ma mb : Nat), 1 ≤ a.deg → 1 ≤ b.deg → ma ≤ a.deg → mb ≤ b.deg →
    eqTypeOk a b ma mb = .ok ()

/-- `==` never throws at the type level: promotion only raises degrees. -/
theorem eqTypeOk_ok (a b : CType) (ma mb : Nat) : eqTypeOk a b ma mb = .ok () := by
  have hp : ∃ p : CType, promoteNodes a b = .ok p ∧ a.deg ≤ p.deg ∧ b.deg ≤ p.deg := by
    unfold promoteNodes
    by_cases h : a = b
    · subst h; exact ⟨a, by rw [if_pos rfl], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, by rw [if_neg h], Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  obtain ⟨p, hp, ha, hb⟩ := hp
  obtain ⟨r1, h1⟩ := convertFull_ok ⟨p.kind, p.elt, p.deg⟩ a ma (Or.inl ha)
  obtain ⟨r2, h2⟩ := convertFull_ok ⟨p.kind, p.elt, p.deg⟩ b mb (Or.inl hb)
  have e1 : convertType p.asN a ma = .ok r1 := h1
  have e2 : convertType p.asN b mb = .ok r2 := h2
  simp [eqTypeOk, hp, e1, e2, bind, Except.bind, pure, Except.pure]

theorem eq_no_throw_holds : eq_no_throw :=
  fun a b ma mb _ _ _ _ => eqTypeOk_ok a b ma mb

/-- Conversion across maximum degrees (Miles's rule for PR #238): converting
`N2{T2,D2}` to `N1{T1,D1}` succeeds exactly when the types are equal, the
degree is not lowered, or every node of the tree fits the target degree;
otherwise it throws. -/
def convert_degree : Prop :=
  ∀ (N1 src : CType) (md : Nat),
    (convertFull N1 src md = .ok N1 ↔ (N1 = src ∨ src.deg ≤ N1.deg ∨ md ≤ N1.deg)) ∧
    (¬ (N1 = src ∨ src.deg ≤ N1.deg ∨ md ≤ N1.deg) → ∃ e, convertFull N1 src md = .error e)

theorem convert_degree_holds : convert_degree := by
  intro N1 src md
  unfold convertFull
  by_cases he : N1 = src
  · subst he
    rw [if_pos rfl]
    exact ⟨⟨fun _ => Or.inl rfl, fun _ => rfl⟩, fun h => absurd (Or.inl rfl) h⟩
  · rw [if_neg he]
    by_cases hd : N1.deg < src.deg ∧ N1.deg < md
    · rw [if_pos hd]
      refine ⟨⟨fun h => (by cases h), fun h => ?_⟩, fun _ => ⟨_, rfl⟩⟩
      rcases h with h | h | h
      · exact absurd h he
      · omega
      · omega
    · rw [if_neg hd]
      have : src.deg ≤ N1.deg ∨ md ≤ N1.deg := by omega
      refine ⟨⟨fun _ => Or.inr this, fun _ => rfl⟩, fun h => absurd (Or.inr this) h⟩

/-- Companion of `ctor_children_degree` (implied by it since PR #234): with
children of the default degree 2, `Node(; op, children)` returns a node of the
children's type. -/
def ctor_children_degree_default : Prop :=
  ∀ (c : CType) (n m : Nat), 1 ≤ n → n ≤ c.deg → m ≤ c.deg → c.deg = 2 →
    ctorBranchType ⟨c.kind, none, none⟩ (List.replicate n (c, m)) = .ok c

theorem ctor_children_degree_default_holds : ctor_children_degree_default :=
  fun c n m h1 h2 h3 _ => ctor_children_degree_holds c n m h1 h2 h3

/-- Companion of `convert_unparam` (implied by it since PR #239): for trees of
the default degree 2, `convert(Node, tree)` succeeds and keeps the type. -/
def convert_unparam_default : Prop :=
  ∀ (c : CType) (md : Nat), c.deg = 2 → md ≤ c.deg → convertType ⟨c.kind, none, none⟩ c md = .ok c

theorem convert_unparam_default_holds : convert_unparam_default :=
  fun c md hd hm => convert_unparam_holds c md (by omega) hm

/-- Companion of `eq_no_throw` (implied by it since PR #238): `==` between two
nodes of the same maximum degree never throws. -/
def eq_no_throw_same_degree : Prop :=
  ∀ (a b : CType) (ma mb : Nat), a.deg = b.deg → ma ≤ a.deg → mb ≤ b.deg →
    eqTypeOk a b ma mb = .ok ()

theorem eq_no_throw_same_degree_holds : eq_no_throw_same_degree :=
  fun a b ma mb _ _ _ => eqTypeOk_ok a b ma mb

example : (1 : Nat) ≤ (⟨.node, .float64, 3⟩ : CType).deg ∧ (2 : Nat) ≤ (⟨.node, .float64, 3⟩ : CType).deg :=
  ⟨by decide, by decide⟩

end DynExpr.NodeBase
