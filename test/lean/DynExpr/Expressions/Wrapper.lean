import DynExpr.Model.Denote
import DynExpr.Model.NodeHeap
import DynExpr.Runtime.Value

namespace DynExpr.Expressions


/-- NamedTuple keys and values in insertion order, src/Expression.jl:32-52.
The value type is arbitrary, including operator enums, arrays and nested tuples. -/
structure Metadata (V : Type) where
  data : List (String × V)
  deriving DecidableEq

/-- AbstractExpression's required contents/metadata interface and concrete
Expression fields, src/Expression.jl:69,93-100,152-157. -/
structure Expression (T M : Type) where
  tree : Tree T
  metadata : M

/-- src/Expression.jl:216-218. -/
def get_contents (ex : Expression T M) := ex.tree
/-- src/Expression.jl:234-236. -/
def get_metadata (ex : Expression T M) := ex.metadata
/-- src/Expression.jl:267-272. -/
def get_tree (ex : Expression T M) := ex.tree
/-- src/Expression.jl:210-215. -/
def with_contents (ex : Expression T M) (tree : Tree T) : Expression T M :=
  ⟨tree, get_metadata ex⟩
/-- src/Expression.jl:231-233. -/
def with_metadata (ex : Expression T M) (metadata : M) : Expression T M :=
  ⟨get_contents ex, metadata⟩
/-- NamedTuple keyword merge, src/Expression.jl:226-229. Existing positions are
retained; a new key is appended, and a repeated key takes the new value. -/
def setField (key : String) (value : V) : List (String × V) → List (String × V)
  | [] => [(key, value)]
  | (k, v) :: rest => if k = key then (k, value) :: rest
    else (k, v) :: setField key value rest
/-- src/Expression.jl:226-229. -/
def mergeMetadata (old updates : Metadata V) : Metadata V :=
  ⟨updates.data.foldl (fun xs kv => setField kv.1 kv.2 xs) old.data⟩
/-- src/Expression.jl:279-280. Julia equality is passed explicitly because
numeric NaN equality and user-defined metadata equality are observable. -/
def equalExpression (eqTree : Tree T → Tree T → Bool) (eqMeta : M → M → Bool)
    (x y : Expression T M) : Bool := eqTree x.tree y.tree && eqMeta x.metadata y.metadata
/-- src/Expression.jl:276-278. -/
def hashExpression (hashTree : Tree T → Nat → Nat) (hashMeta : M → Nat → Nat)
    (ex : Expression T M) (seed : Nat) : Nat := hashTree ex.tree (hashMeta ex.metadata seed)

/-- Typed and generic operator enum selection, src/Expression.jl:251-265. -/
structure Settings (T : Type) where
  operators : Option (OpEnum T)
  variableNames : Option (List String)
  typed : Bool := true

/-- src/Expression.jl:251-254; an absent operators field is a property error. -/
def get_operators (ex : Expression T (Settings T)) (override : Option (OpEnum T)) : Jl (OpEnum T) :=
  match override with
  | some o => .ok o
  | none => match ex.metadata.operators with
    | some o => .ok o
    | none => .error (.errorException "metadata has no operators field")
/-- src/Expression.jl:256-265. -/
def get_variable_names (ex : Expression T (Settings T)) (override : Option (List String)) :=
  match override with
  | some names => some names
  | none => ex.metadata.variableNames
/-- src/Expression.jl:390-399. -/
def maxFeature : Tree T → Nat
  | .const _ => 0
  | .feature i => i
  | .branch _ cs => (cs.map maxFeature).foldr max 0
/-- src/Expression.jl:401-409. Enum kind is the resolved enum's kind, so an
explicit generic enum bypasses typed feature checks. -/
def validateInput (ex : Expression T (Settings T)) (matrix : Bool) (rows : Nat)
    (typed : Bool) (override : Option (OpEnum T)) : Jl Unit := do
  let _ ← get_operators ex override
  if typed then
    if !matrix then .error (.assertionError "X isa AbstractMatrix")
    else if maxFeature ex.tree ≤ rows then .ok ()
    else .error (.assertionError "max_feature(ex) <= size(X, 1)")
  else .ok ()
/-- src/Expression.jl:435-443,473-481,486-495,515-519. This exact forwarding
mirror is polymorphic over the tree evaluator, including its keyword options,
result buffers, completion flags and gradient mode. -/
def forwardEval (treeEval : Tree T → JMat T → OpEnum T → Jl R)
    (ex : Expression T (Settings T)) (X : JMat T) (typed : Bool)
    (override : Option (OpEnum T)) : Jl R := do
  validateInput ex true X.nrows typed override
  treeEval (get_tree ex) X (← get_operators ex override)
/-- src/Expression.jl:361-373. Rendering options other than names are captured
by the arbitrary tree renderer, preserving its full observable return value. -/
def forwardString (render : Tree T → OpEnum T → Option (List String) → Jl String)
    (ex : Expression T (Settings T)) (ops : Option (OpEnum T))
    (names : Option (List String)) : Jl String := do
  render (get_tree ex) (← get_operators ex ops) (get_variable_names ex names)
/-- src/Expression.jl:321-329. References and setter state are retained in the
callback; the wrapper forwards the identical tree and arguments. -/
def forwardConstants (get : Tree T → R) (ex : Expression T M) : R := get (get_tree ex)
def forwardSetConstants (set : Tree T → C → Refs → R) (ex : Expression T M)
    (constants : C) (refs : Refs) : R := set (get_tree ex) constants refs


/-- Component replacement changes exactly its selected component. -/
def componentsProperty : Prop := ∀ (T M : Type) (ex : Expression T M) t m,
  get_contents (with_contents ex t) = t ∧
  get_metadata (with_contents ex t) = ex.metadata ∧
  get_contents (with_metadata ex m) = ex.tree ∧
  get_metadata (with_metadata ex m) = m ∧ get_tree ex = get_contents ex
 theorem components_proven : componentsProperty := by intro T M ex t m; exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Independent NamedTuple field lookup specification, src/Expression.jl:35-39. -/
def fieldValue (key : String) : List (String × V) → Option V
  | [] => none
  | (name, value) :: rest => if name = key then some value else fieldValue key rest

private theorem field_set (fields : List (String × V)) (key query : String) (value : V) :
    fieldValue query (setField key value fields) =
      if query = key then some value else fieldValue query fields := by
  induction fields with
  | nil =>
    by_cases h : query = key
    · simp [fieldValue, setField, h]
    · simp [fieldValue, setField, h, Ne.symm h]
  | cons kv fields ih =>
    obtain ⟨name, old⟩ := kv
    by_cases hq : query = key
    · subst query
      by_cases hn : name = key <;> simp [fieldValue, setField, hn, ih]
    · by_cases hn : name = key
      · subst name
        simp [fieldValue, setField, hq, Ne.symm hq]
      · by_cases hname : name = query <;> simp [fieldValue, setField, hq, hn, hname, ih]

private theorem field_merge (old updates : List (String × V)) (query : String) :
    fieldValue query (updates.foldl (fun fields kv => setField kv.1 kv.2 fields) old) =
      updates.foldl (fun current kv => if kv.1 = query then some kv.2 else current)
        (fieldValue query old) := by
  induction updates generalizing old with
  | nil => rfl
  | cons kv updates ih =>
    obtain ⟨key, value⟩ := kv
    simp only [List.foldl_cons]
    rw [ih, field_set]
    simp only [eq_comm]

def keywordMergeProperty : Prop := ∀ (V : Type) (old updates : Metadata V) (query : String),
  fieldValue query (mergeMetadata old updates).data =
    updates.data.foldl (fun current kv => if kv.1 = query then some kv.2 else current)
      (fieldValue query old.data)
 theorem keywordMerge_proven : keywordMergeProperty := by
  intro V old updates query
  exact field_merge old.data updates.data query
example : mergeMetadata (⟨[("a", 1), ("b", 2)]⟩ : Metadata Nat)
    ⟨[("b", 3), ("c", 4)]⟩ = ⟨[("a", 1), ("b", 3), ("c", 4)]⟩ := rfl

def forwardingProperty : Prop := ∀ (ex : Expression JF (Settings JF))
  (X : JMat JF) (o : OpEnum JF)
  (eval : Tree JF → JMat JF → OpEnum JF → Jl (JVec JF × Bool)),
  maxFeature ex.tree ≤ X.nrows →
  forwardEval eval (with_metadata ex { ex.metadata with operators := some o }) X true none =
    eval ex.tree X o
 theorem forwarding_proven : forwardingProperty := by
  intro ex X o eval h
  simp [forwardEval, validateInput, get_operators, with_metadata, get_contents, get_tree, h,
    bind, Except.bind]
example : maxFeature (Tree.const (JF.fin 1)) ≤ (JMat.ofFn (T := JF) 0 0 (fun i => nomatch i)).nrows := by
  simp [maxFeature, JMat.ofFn]

def overrideProperty : Prop := ∀ (ex : Expression JF (Settings JF))
  (o : OpEnum JF) (names : List String)
  (render : Tree JF → OpEnum JF → Option (List String) → Jl String),
  get_operators ex (some o) = .ok o ∧ get_variable_names ex (some names) = some names ∧
  forwardString render ex (some o) (some names) = render ex.tree o (some names)
 theorem override_proven : overrideProperty := by intro ex o names render; exact ⟨rfl,rfl,rfl⟩

def validationProperty : Prop := ∀ (ex : Expression JF (Settings JF)) (o : OpEnum JF) rows,
  rows < maxFeature ex.tree → validateInput ex true rows true (some o) =
    .error (.assertionError "max_feature(ex) <= size(X, 1)")
 theorem validation_proven : validationProperty := by
  intro ex o rows h
  simp [validateInput, get_operators, Nat.not_le.mpr h, bind, Except.bind]
example : 0 < maxFeature (Tree.feature (T := JF) 1) := by simp [maxFeature]

def constantsProperty : Prop := ∀ (T M R C Refs : Type) (ex : Expression T M)
  (get : Tree T → R) (set : Tree T → C → Refs → R) cs refs,
  forwardConstants get ex = get ex.tree ∧ forwardSetConstants set ex cs refs = set ex.tree cs refs
 theorem constants_proven : constantsProperty := by intro T M R C Refs ex get set cs refs; exact ⟨rfl,rfl⟩

def equalityHashProperty : Prop := ∀ (T M : Type) (x y : Expression T M)
  (eqT : Tree T → Tree T → Bool) (eqM : M → M → Bool)
  (ht : Tree T → Nat → Nat) (hm : M → Nat → Nat) seed,
  equalExpression eqT eqM x y = (eqT x.tree y.tree && eqM x.metadata y.metadata) ∧
  hashExpression ht hm x seed = ht x.tree (hm x.metadata seed)
 theorem equalityHash_proven : equalityHashProperty := by
  intro T M x y eqT eqM ht hm seed
  exact ⟨rfl,rfl⟩


def gradientForwardingProperty : Prop := ∀ (ex : Expression JF (Settings JF))
  (X : JMat JF) (o : OpEnum JF)
  (eval : Tree JF → JMat JF → OpEnum JF → Jl (JVec JF × JMat JF × Bool)),
  maxFeature ex.tree ≤ X.nrows →
  forwardEval eval (with_metadata ex { ex.metadata with operators := some o }) X true none =
    eval ex.tree X o
 theorem gradientForwarding_proven : gradientForwardingProperty := by
  intro ex X o eval h
  simp [forwardEval, validateInput, get_operators, with_metadata, get_contents, get_tree, h,
    bind, Except.bind]
example : maxFeature (Tree.const (JF.fin 1)) ≤ (JMat.ofFn (T := JF) 0 0 (fun i => nomatch i)).nrows := by
  simp [maxFeature, JMat.ofFn]



/-- src/Expression.jl:435-443,473-481. Result buffer identities are forwarded
without cloning, so backend ownership contracts are unchanged by the wrapper. -/
def bufferIdentityProperty : Prop := ∀ (ex : Expression JF (Settings JF))
  (X : JMat JF) (o : OpEnum JF) (valueBuffer gradientBuffer : Addr),
  maxFeature ex.tree ≤ X.nrows →
  forwardEval (fun _ _ _ => .ok (valueBuffer, gradientBuffer))
    (with_metadata ex { ex.metadata with operators := some o }) X true none =
      .ok (valueBuffer, gradientBuffer)
 theorem bufferIdentity_proven : bufferIdentityProperty := by
  intro ex X o valueBuffer gradientBuffer h
  simp [forwardEval, validateInput, get_operators, with_metadata, get_contents, h,
    bind, Except.bind]
example : maxFeature (Tree.const (JF.fin 1)) ≤ (JMat.ofFn (T := JF) 0 0 (fun i => nomatch i)).nrows := by
  simp [maxFeature, JMat.ofFn]

end DynExpr.Expressions
