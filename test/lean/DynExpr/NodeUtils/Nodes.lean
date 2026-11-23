import DynExpr.Model.NodeHeap
import DynExpr.NodeUtils.Values

namespace DynExpr.NodeUtils
@[local simp] theorem bindOk (v : A) (f : A → Jl B) : (Except.ok v >>= f) = f v := rfl
@[local simp] theorem bindError (e : JlError) (f : A → Jl B) : (Except.error e >>= f) = .error e := rfl
@[local simp] theorem mapOk (v : A) (f : A → B) : f <$> (Except.ok v : Jl A) = .ok (f v) := rfl
@[local simp] theorem mapError (e : JlError) (f : A → B) : f <$> (Except.error e : Jl A) = .error e := rfl

/-- src/NodeUtils.jl:25-29 follows the child max reduction with sharing broken. -/
def countDepth : Tree T → Nat
  | .const _ | .feature _ => 1
  | .branch _ cs => 1 + (cs.map countDepth).foldr max 0

/-- src/NodeUtils.jl:99-108, left-to-right depth-first numeric constants. -/
def getConstants : Tree T → List T
  | .const v => [v]
  | .feature _ => []
  | .branch _ cs => cs.flatMap getConstants

/-- src/NodeUtils.jl:43-51 for plain Node (repeated addresses count repeatedly). -/
def countConstantNodes : Tree T → Nat
  | .const _ => 1
  | .feature _ => 0
  | .branch _ cs => (cs.map countConstantNodes).sum

/-- src/NodeUtils.jl:81-89, numeric constants each consume one scalar. -/
def countScalarConstants (t : Tree T) := countConstantNodes t

/-- src/NodeUtils.jl:58 and 65. -/
def hasConstants (t : Tree T) := !(getConstants t).isEmpty

def hasOperators (t : Tree T) := t.degree != 0

/-- src/NodeUtils.jl:73, every leaf is constant. -/
def isConstant : Tree T → Bool
  | .const _ => true
  | .feature _ => false
  | .branch _ cs => (cs.map isConstant).all id

/-- src/NodeUtils.jl:102-104 plus src/base.jl:96-108,127-155.
Fuel bounds finite acyclic traversal. GraphNode skips repeated identities;
plain Node includes each occurrence, including aliased constant leaves. -/
def constantRefs (g : Graph T) (sharing : Bool) : Nat → Addr → List Addr → Jl (List Addr × List Addr)
  | 0, _, _ => .error (.errorException "traversal fuel exhausted")
  | fuel + 1, a, seen => do
      if sharing && seen.contains a then return ([],seen)
      let c ← g.read a
      let seen := if sharing then a :: seen else seen
      if c.degree = 0 then
        return (if c.constant then [a] else [], seen)
      else
        c.children.foldlM (fun (out, visited) child => do
          let (rs, visited') ← constantRefs g sharing fuel child visited
          return (out ++ rs, visited')) ([], seen)

/-- src/NodeUtils.jl:107 numeric getter dereferences the constant refs. -/
def readValues (g : Graph T) : List Addr → Jl (List T)
  | [] => .ok []
  | a :: rs => do
      let c ← g.read a
      let v ← match c.val with | none => .error .undefRefError | some v => .ok v
      return v :: (← readValues g rs)

/-- src/NodeUtils.jl:99-116 numeric branch. -/
def getScalarConstants (g : Graph T) (sharing : Bool) (fuel : Nat) (root : Addr) :
    Jl (List T × List Addr) := do
  let (refs, _) ← constantRefs g sharing fuel root []
  return ((← readValues g refs), refs)

/-- src/NodeUtils.jl:129 mutates only the value field through each reference. -/
def setValue (g : Graph T) (a : Addr) (v : T) : Jl (Graph T) := do
  let c ← g.read a
  g.write a { c with val := some v }

/-- src/NodeUtils.jl:128-130, writes after eachindex has validated axes. -/
def setScalarConstantsLoop (g : Graph T) : List T → List Addr → Jl (Graph T)
  | [], [] => .ok g
  | v :: vs, a :: rs => do
      let h ← setValue g a v
      setScalarConstantsLoop h vs rs
  | _, _ => .error (.argumentError "DimensionMismatch")

/-- src/NodeUtils.jl:126-130: numeric eachindex checks matching axes before writes.
The tree argument itself is not used to validate the refs. -/
def setScalarConstants (g : Graph T) (vs : List T) (rs : List Addr) : Jl (Graph T) :=
  if vs.length = rs.length then setScalarConstantsLoop g vs rs
  else .error (.argumentError "DimensionMismatch")

/-- src/NodeUtils.jl:150-169, active structure of NodeIndex; branch value is zero. -/
inductive NodeIndex where
  | leaf (val : Nat)
  | branch (children : List NodeIndex)
  deriving Repr

mutual
  /-- src/NodeUtils.jl:186-202, UInt16 increment wraps and features keep zero. -/
  def indexConstants : Tree T → Nat → NodeIndex × Nat
    | .const _, i => (.leaf ((i + 1) % 65536), (i + 1) % 65536)
    | .feature _, i => (.leaf 0, i)
    | .branch _ cs, i =>
        let (ns,j) := indexForest cs i
        (.branch ns,j)
  def indexForest : List (Tree T) → Nat → List NodeIndex × Nat
    | [], i => ([],i)
    | c :: cs, i =>
        let (n,j) := indexConstants c i
        let (ns,k) := indexForest cs j
        (n :: ns,k)
end

def indexLeaves : NodeIndex → List Nat
  | .leaf n => [n]
  | .branch cs => cs.flatMap indexLeaves

/-- Canonical cell constructors allow executable alias counterexamples. -/
def constantCell (v : T) : Cell T := ⟨0,true,some v,0,0,[]⟩
def operatorCell (op : Nat) (cs : List Addr) : Cell T := ⟨cs.length,false,none,0,op,cs⟩

def DepthCorrect : Prop := ∀ t : Tree Nat, countDepth t = t.depth

theorem depthCorrect_proven : DepthCorrect := by
  intro t
  induction t using Tree.induction with
  | hc v => simp [countDepth, Tree.depth]
  | hf i => simp [countDepth, Tree.depth]
  | hb op cs ih =>
      simp only [countDepth, Tree.depth]
      congr 2
      apply List.map_congr_left
      exact ih

private theorem constantsLength (t : Tree T) : (getConstants t).length = countConstantNodes t := by
  induction t using Tree.induction with
  | hc v => simp [getConstants, countConstantNodes]
  | hf i => simp [getConstants, countConstantNodes]
  | hb op cs ih =>
      simp only [getConstants, countConstantNodes, List.length_flatMap]
      congr 1
      apply List.map_congr_left
      exact ih

def CountsAgree : Prop := ∀ t : Tree Nat,
  countScalarConstants t = (getConstants t).length ∧ countConstantNodes t = (getConstants t).length

theorem countsAgree_proven : CountsAgree := by
  intro t; exact ⟨(constantsLength t).symm, (constantsLength t).symm⟩

def PresenceCorrect : Prop := ∀ t : Tree Nat,
  (hasConstants t = true ↔ countConstantNodes t > 0) ∧ (hasOperators t = true ↔ t.degree ≠ 0)

theorem presenceCorrect_proven : PresenceCorrect := by
  intro t
  constructor
  · simp [hasConstants, ← constantsLength t, List.length_pos_iff]
  · simp [hasOperators]

private theorem heapExt (g h : Graph T) (hc : ∀ a, g.cells a = h.cells a) (hn : g.next = h.next) : g = h := by
  cases g; cases h
  simp_all only [Heap.mk.injEq]
  exact ⟨funext hc, trivial⟩

theorem setValueRestore (g : Graph T) (a : Addr) (c : Cell T) (v : T)
    (hc : g.cells a = some c) (hv : c.val = some v) : setValue g a v = .ok g := by
  have he : { c with val := some v } = c := by cases c; simp_all
  simp only [setValue, Heap.read, hc, bindOk, he]
  unfold Heap.write
  simp only [hc, reduceCtorEq, ↓reduceDIte]
  congr 1
  apply heapExt
  · intro b; dsimp; split <;> simp_all
  · rfl

private theorem restoreRefs (rs : List Addr) (g : Graph T) (vs : List T)
    (h : readValues g rs = .ok vs) :
    setScalarConstantsLoop g vs rs = .ok g ∧ vs.length = rs.length := by
  induction rs generalizing vs with
  | nil => simp [readValues] at h; subst vs; exact ⟨rfl,rfl⟩
  | cons a rs ih =>
      cases hc : g.cells a with
      | none => simp [readValues, Heap.read, hc] at h
      | some c =>
          cases hv : c.val with
          | none => simp [readValues, Heap.read, hc, hv] at h
          | some v =>
              cases hr : readValues g rs with
              | error e => simp [readValues, Heap.read, hc, hv, hr] at h
              | ok rest =>
                  simp [readValues, Heap.read, hc, hv, hr] at h
                  subst vs
                  obtain ⟨hw,hlen⟩ := ih rest hr
                  simp [setScalarConstantsLoop, setValueRestore g a c v hc hv, hw, hlen]

def ScalarGetterRestore : Prop := ∀ (g : Graph Nat) sharing fuel root vs rs,
  Graph.NoAlias g root → getScalarConstants g sharing fuel root = .ok (vs,rs) →
    setScalarConstants g vs rs = .ok g

theorem scalarGetterRestore_proven : ScalarGetterRestore := by
  intro g sharing fuel root vs rs _hno h
  unfold getScalarConstants at h
  cases ht : constantRefs g sharing fuel root [] with
  | error e => simp [ht] at h
  | ok p =>
      cases hv : readValues g p.1 with
      | error e => simp [ht,hv] at h
      | ok vals =>
          simp [ht,hv] at h
          obtain ⟨rfl,rfl⟩ := h
          obtain ⟨hw,hlen⟩ := restoreRefs _ _ _ hv
          simp [setScalarConstants, hw, hlen]

example : getScalarConstants ((Heap.empty.alloc (constantCell (1 : Nat))).2) false 1 0 =
  .ok ([1],[0]) := by rfl

/-- Legal GraphNode sharing: two edges refer to one constant object. -/
def aliasGraph : Graph Nat :=
  let h := (Heap.empty.alloc (constantCell 1)).2
  (h.alloc (operatorCell 1 [0,0])).2

/-- src/NodeUtils.jl:43-51,81-89: shared identities emit their numeric
constant contribution only on the first visit, using the same traversal policy
as filter_map in the getter. -/
def sharedConstantCount (g : Graph T) (fuel root : Nat) : Jl Nat :=
  (constantRefs g true fuel root []).map (fun result => result.1.length)

def SharedCountCorrect : Prop := ∀ (T : Type) (g : Graph T) fuel root values refs,
  Graph.Acyclic g root →
  getScalarConstants g true fuel root = .ok (values,refs) →
    sharedConstantCount g fuel root = .ok values.length ∧ values.length = refs.length

theorem sharedCountCorrect_proven : SharedCountCorrect := by
  intro T g fuel root values refs _ha hg
  unfold getScalarConstants at hg
  cases ht : constantRefs g true fuel root [] with
  | error e => simp [ht] at hg
  | ok p =>
      cases hv : readValues g p.1 with
      | error e => simp [ht,hv] at hg
      | ok vals =>
          simp [ht,hv] at hg
          obtain ⟨rfl,rfl⟩ := hg
          have hlen := (restoreRefs _ _ _ hv).2
          simp [sharedConstantCount, ht, hlen, Except.map]

example : getScalarConstants aliasGraph true 2 1 = .ok ([1],[0]) := rfl

example : Graph.Acyclic ((Heap.empty.alloc (constantCell (1 : Nat))).2) 0 :=
  (Graph.noAlias_ofTree Heap.empty (.const 1)).acyclic

example : Graph.NoAlias ((Heap.empty.alloc (constantCell (1 : Nat))).2) 0 := by
  exact Graph.noAlias_ofTree Heap.empty (.const 1)

end DynExpr.NodeUtils
