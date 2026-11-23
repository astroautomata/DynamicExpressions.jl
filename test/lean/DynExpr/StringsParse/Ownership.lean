import DynExpr.StringsParse.Properties

namespace DynExpr.StringsParse

/-- Mutable literal objects stored as node values (`src/Parse.jl:581-597`).
The separate array heap makes sharing of a constant's contents observable. -/
inductive ObjectValue where
  | scalar (v : Scalar)
  | array (address : Addr)
  deriving DecidableEq, Repr

structure ObjectState where
  nodes : Graph ObjectValue := Heap.empty
  arrays : Heap (List Scalar) := Heap.empty

/-- A leaf AST value; a prebuilt node carries its node family. -/
inductive ObjectLeaf where
  | node (family : String) (address : Addr)
  | value (value : ObjectValue)
  | symbol (name : String)
  | expression

/-- Families whose `preserve_sharing` is true (`src/Node.jl:74-90`). -/
def preservesSharing (family : String) : Bool := family == "GraphNode"

/-- The `tree_mapreduce` copy of `convert(N1, tree)` (`src/base.jl:535-552`):
children are converted left to right and each node gets a fresh cell after its
children; with `break_sharing=Val(!preserve_sharing(N1))` off, a repeated source
identity reuses its first copy. The memo maps source to copied identities. -/
def convertCells (share : Bool) : Nat → Addr → Graph ObjectValue × List (Addr × Addr) →
    Jl (Addr × Graph ObjectValue × List (Addr × Addr))
  | 0, _, _ => .error (.argumentError "cyclic graph or insufficient traversal depth")
  | fuel + 1, a, (g, memo) =>
      match (if share then memo.find? (fun p => p.1 == a) else none) with
      | some p => .ok (p.2, g, memo)
      | none => do
          let c ← g.read a
          let (children, g, memo) ← c.children.foldlM (fun acc child => do
            let r ← convertCells share fuel child (acc.2.1, acc.2.2)
            return (acc.1 ++ [r.1], r.2.1, r.2.2)) ([], g, memo)
          let (b, g) := g.alloc {c with children}
          return (b, g, (a, b) :: memo)

/-- `convert(node_type, ex)` for a prebuilt node (`src/Parse.jl:594-595`,
`src/base.jl:535-552`): the same family returns the object itself; another
family copies it. Traversal fuel is the number of allocated identities plus
one, enough for every acyclic reachable graph. Value-type conversion and the
max-degree check are not modelled, since families carry no parameters here. -/
def convertNodeObject (family target : String) (state : ObjectState) (a : Addr) :
    Jl (Addr × ObjectState) := do
  if family == target then return (a, state)
  let (b, nodes, _) ← convertCells (preservesSharing target) (state.nodes.next + 1) a (state.nodes, [])
  return (b, {state with nodes})

/-- The leaf parser allocates a node for literal/module values, retains the
literal object, and converts pre-built nodes to the requested family
(`src/Parse.jl:560-599`). Module bindings are explicit values. -/
def parseLeafObjects (cfg : ParseConfig) (globals : String → Option ObjectValue)
    (state : ObjectState) (leaf : ObjectLeaf) : Jl (Addr × ObjectState) := do
  match leaf with
  | .node family a => convertNodeObject family cfg.nodeType state a
  | .expression => throw (.argumentError "Cannot parse an expression as a value in another expression.")
  | .value value =>
      let (a, nodes) := Graph.ofTree state.nodes (.const value)
      return (a, {state with nodes})
  | .symbol name =>
      if let some i := variableIndex name cfg.names then
        let (a, nodes) := Graph.ofTree state.nodes (.feature i)
        return (a, {state with nodes})
      if let some value := globals name then
        let (a, nodes) := Graph.ofTree state.nodes (.const value)
        return (a, {state with nodes})
      throw (.argumentError "Variable not found in variable_names or eval_module")

/-- The module thunk's returned object is passed directly to the node
constructor (`src/Parse.jl:359-361,403-405`), without cloning its storage. -/
def parseModuleObject (state : ObjectState) (result : Jl ObjectValue) : Jl (Addr × ObjectState) := do
  let value ← result
  let (a, nodes) := Graph.ofTree state.nodes (.const value)
  return (a, {state with nodes})

/-- After parsing its arguments, evaluate_on returns the external function's
node directly (`src/Parse.jl:506-522`). Its callback can read or mutate the
explicit node and array heaps. -/
def parseExternalObject (enabled : Bool) (args : List Addr) (state : ObjectState)
    (callback : List Addr → ObjectState → Jl (Addr × ObjectState)) : Jl (Addr × ObjectState) :=
  if enabled then callback args state
  else .error (.argumentError "Unrecognized operator")

/-- Operator branch construction retains each recursively parsed child's
identity (`src/Parse.jl:433-448`), including repeated pre-built leaves. -/
def parseBranchObjects (cfg : ParseConfig) (state : ObjectState) (op : Nat)
    (leaves : List ObjectLeaf) : Jl (Addr × ObjectState) := do
  let (children, state) ← leaves.foldlM (fun (children, state) leaf => do
    let (a, state) ← parseLeafObjects cfg (fun _ => none) state leaf
    return (children ++ [a], state)) ([], state)
  let (a, nodes) := state.nodes.alloc ⟨children.length, false, none, 0, op, children⟩
  return (a, {state with nodes})

/-- Array-valued constant access through the node heap (`src/Parse.jl:581-597`). -/
def arrayReference (result : Jl (Addr × ObjectState)) : Option Addr := do
  let (root, state) ← result.toOption
  let c ← state.nodes.cells root
  match c.val with
  | some (.array a) => some a
  | _ => none

/-- Default rendering reads variable_names and copies its characters
(`src/Strings.jl:173-182`). The second component is the unchanged names heap. -/
def renderNames (cfg : RenderConfig) (names : Heap (List String)) (a : Addr)
    (t : Tree Scalar) : Jl (String × Heap (List String)) := do
  let ns ← names.read a
  let text ← stringTree {cfg with names := some ns} t
  return (text, names)

def ownedNode : Addr × Graph ObjectValue :=
  (Heap.empty : Graph ObjectValue).alloc ⟨0, false, none, 1, 0, []⟩
def ownedArray : Addr × Heap (List Scalar) :=
  (Heap.empty : Heap (List Scalar)).alloc [num 1, num 2]
def nodeState : ObjectState := {nodes := ownedNode.2}
def arrayState : ObjectState := {arrays := ownedArray.2}

example : (parseLeafObjects parseCfg (fun _ => none) nodeState (.node "Node" ownedNode.1)).toOption.map
  Prod.fst = some ownedNode.1 := rfl

def LiteralArrayExposed : Prop :=
  arrayReference (parseLeafObjects parseCfg (fun _ => none) arrayState (.value (.array ownedArray.1))) =
    some ownedArray.1
theorem literalArrayExposed : LiteralArrayExposed := by unfold LiteralArrayExposed; decide +kernel

def ModuleArrayExposed : Prop :=
  arrayReference (parseLeafObjects parseCfg (fun name => if name == "data" then some (.array ownedArray.1) else none)
    arrayState (.symbol "data")) = some ownedArray.1
theorem moduleArrayExposed : ModuleArrayExposed := by unfold ModuleArrayExposed; decide +kernel

def ModuleResultExposed : Prop :=
  arrayReference (parseModuleObject arrayState (.ok (.array ownedArray.1))) = some ownedArray.1
theorem moduleResultExposed : ModuleResultExposed := by unfold ModuleResultExposed; decide +kernel

def ExternalNodeExposed : Prop :=
  ((parseExternalObject true [ownedNode.1] nodeState
    (fun args s => .ok (args.headD 0, s))).toOption.map Prod.fst) = some ownedNode.1
theorem externalNodeExposed : ExternalNodeExposed := by unfold ExternalNodeExposed; decide +kernel

def NamesUnchanged : Prop := ∀ cfg names a t text result,
  cfg.fVariable = stringVariable → cfg.fConstant = stringConstant →
  renderNames cfg names a t = .ok (text, result) → result = names
theorem namesUnchanged : NamesUnchanged := by
  intro cfg names a t text result _ _ h
  unfold renderNames at h
  cases hn : names.read a with
  | error e =>
    rw [hn] at h
    change Except.error e = Except.ok (text, result) at h
    cases h
  | ok ns =>
    rw [hn] at h
    change ((fun out => (out, names)) <$> stringTree {cfg with names := some ns} t) =
      Except.ok (text, result) at h
    cases ht : stringTree {cfg with names := some ns} t with
    | error e =>
      rw [ht] at h
      change Except.error e = Except.ok (text, result) at h
      cases h
    | ok out =>
      rw [ht] at h
      change Except.ok (out, names) = Except.ok (text, result) at h
      exact (Prod.mk.inj (Except.ok.inj h)).2.symm

example : renderCfg.fVariable = stringVariable ∧ renderCfg.fConstant = stringConstant := ⟨rfl, rfl⟩

example : renderNames renderCfg
  ((Heap.empty : Heap (List String)).alloc ["alpha", "beta"]).2 0 (.feature 1) =
  .ok ("alpha", ((Heap.empty : Heap (List String)).alloc ["alpha", "beta"]).2) := by rfl


def PrintIOSink : Prop := ∀ cfg t io a before text result,
  io.read a = .ok before → printTree cfg t = .ok text →
  printTreeIO cfg t io a = .ok ((), result) → result.read a = .ok (before ++ text)
theorem printIOSink : PrintIOSink := by
  intro cfg t io a before text result hr hp h
  unfold printTreeIO at h
  rw [hr, hp] at h
  change ((fun out => ((), out)) <$> io.write a (before ++ text)) = .ok ((), result) at h
  cases hw : io.write a (before ++ text) with
  | error e =>
    rw [hw] at h
    change Except.error e = Except.ok ((), result) at h
    cases h
  | ok out =>
    rw [hw] at h
    change Except.ok ((), out) = Except.ok ((), result) at h
    have he := (Prod.mk.inj (Except.ok.inj h)).2
    subst result
    exact Heap.read_write_same io out a (before ++ text) hw

example : (printTreeIO renderCfg (.feature 1)
    ((Heap.empty : Heap String).alloc "prefix:").2 0).toOption.map
    (fun (_, io) => (io.read 0).toOption) = some (some "prefix:x1\n") := by decide +kernel

end DynExpr.StringsParse
