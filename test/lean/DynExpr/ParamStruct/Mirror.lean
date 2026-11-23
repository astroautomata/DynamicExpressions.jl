import DynExpr.Model.Denote
import DynExpr.Runtime.Value
import DynExpr.Runtime.Heap

namespace DynExpr.ParamStruct

deriving instance DecidableEq for Except

@[simp] theorem jl_bind_ok (v : T) (f : T → Jl U) :
    ((.ok v : Jl T) >>= f) = f v := rfl
@[simp] theorem jl_bind_error (e : JlError) (f : T → Jl U) :
    ((.error e : Jl T) >>= f) = .error e := rfl
@[simp] theorem jl_map_ok (v : T) (f : T → U) :
    f <$> (.ok v : Jl T) = .ok (f v) := rfl
@[simp] theorem jl_map_error (e : JlError) (f : T → U) :
    f <$> (.error e : Jl T) = .error e := rfl
@[simp] theorem jl_pure (v : T) : (pure v : Jl T) = .ok v := rfl

/-- Active scalar tags, src/ParametricExpression.jl:53-75. Inactive fields remain
available in `Leaf` because equality and leaf mutation read them. -/
inductive PVal where
  | constant (v : JF)
  | parameter (i : Nat)
  deriving DecidableEq, Repr
abbrev PTree := Tree PVal

/-- Raw degree-zero fields, src/ParametricExpression.jl:53-75. `none` is an
uninitialized field, not a fabricated feature index. -/
structure Leaf where
  constant : Bool
  val : Option JF
  feature : Option UInt16
  isParameter : Bool
  parameter : UInt16
  deriving DecidableEq, Repr

/-- Constructor defaults and ordinary feature constructor, src/ParametricExpression.jl:65-75. -/
def featureLeaf (i : UInt16) : Leaf := ⟨false, none, some i, false, 0⟩
/-- Constant constructor with unused feature unset, src/ParametricExpression.jl:127-129. -/
def constantLeaf (v : JF) : Leaf := ⟨true, some v, none, false, 0⟩
/-- Parameter construction through a zero constant, src/ParametricExpression.jl:133-137. -/
def parameterLeaf (i : UInt16) : Leaf := ⟨false, some (.fin 0), none, true, i⟩

def readField (x : Option T) : Jl T := match x with
  | some v => .ok v
  | none => .error (.undefinedBehavior "uninitialized scalar field")

/-- Leaf copying resets inactive fields, src/ParametricExpression.jl:127-139.
JF scalars are immutable, so `copy_value(t.val)` returns the same value. -/
def leafCopy (a : Leaf) : Jl Leaf := do
  if a.constant then return constantLeaf (← readField a.val)
  else if !a.isParameter then return featureLeaf (← readField a.feature)
  else return parameterLeaf a.parameter

/-- Element conversion only changes a constant value, src/ParametricExpression.jl:155-167. -/
def leafConvert (f : JF → JF) (a : Leaf) : Jl Leaf := do
  if a.constant then return constantLeaf (f (← readField a.val))
  else if a.isParameter then return parameterLeaf a.parameter
  else return featureLeaf (← readField a.feature)

/-- Writes only selected fields, retaining inactive data, src/ParametricExpression.jl:140-154. -/
def setLeaf (a b : Leaf) : Leaf :=
  if b.constant then { a with constant := true, val := b.val }
  else if !b.isParameter then
    { a with constant := false, isParameter := false, feature := b.feature }
  else { a with constant := false, isParameter := true, parameter := b.parameter }

/-- Comparison first requires equal constant flags, then compares the active
field; a feature only equals a non-parameter leaf (src/ParametricExpression.jl:179-190,
PR #244). `!b.is_parameter && ...` short-circuits before reading `b.feature`. -/
def leafEqual (a b : Leaf) : Jl Bool := do
  if a.constant != b.constant then return false
  if a.constant then
    let x ← readField a.val
    let y ← readField b.val
    return if x = .nan ∨ y = .nan then false else decide (x = y)
  else if a.isParameter then return b.isParameter && a.parameter == b.parameter
  else if b.isParameter then return false
  else return (← readField a.feature) == (← readField b.feature)

/-- Input tuple to Julia hash, src/ParametricExpression.jl:168-178. The actual
hash function is arbitrary on these keys; equal keys guarantee equal hashes. -/
def hashKey (a : Leaf) : Jl (String × (JF ⊕ UInt16)) := do
  if a.constant then return ("constant", .inl (← readField a.val))
  else if a.isParameter then return ("parameter", .inr a.parameter)
  else return ("feature", .inr (← readField a.feature))

/-- Leaf converter uses UInt16 addition, src/ParametricExpression.jl:305-331. -/
def convertTree (np : UInt16) : PTree → Tree JF
  | .const (.constant v) => .const v
  | .const (.parameter p) => .feature p
  | .feature i => .feature ((UInt16.ofNat i + np).toNat)
  | .branch op cs => .branch op (cs.map (convertTree np))

/-- Direct specification with separate feature and parameter bindings. -/
def denoteP (o : OpEnum JF) (x p : Nat → Option JF) : PTree → Option JF
  | .const (.constant v) => some v
  | .const (.parameter i) => p i
  | .feature i => x i
  | .branch op cs => do
      let f ← o.lookup cs.length op
      let vs ← cs.mapM (denoteP o x p)
      pure (f vs)

/-- Maximum maps every non-feature node to zero, src/ParametricExpression.jl:411-417.
Every real expression has at least one node, even when there are no features. -/
def maxFeature : PTree → Nat
  | .feature i => i
  | .const _ => 0
  | .branch _ cs => (cs.map maxFeature).foldr max 0

/-- Metadata and tree fields, src/ParametricExpression.jl:84-117. -/
structure PExpression where
  tree : PTree
  operators : OpEnum JF
  variableNames : Option (List String)
  parameters : JMat JF
  parameterNames : Option (List String)

/-- Julia integer conversion checks capacity; it does not wrap the parameter
row count, src/ParametricExpression.jl:322,410,464. -/
def checkedUInt16 (n : Nat) : Jl UInt16 :=
  if n < 65536 then .ok (UInt16.ofNat n)
  else .error (.userError "InexactError UInt16")

/-- Convert the expression after checking matrix row count,
src/ParametricExpression.jl:321-331. -/
def convertP (e : PExpression) : Jl (Tree JF) := do
  let np ← checkedUInt16 e.parameters.nrows
  pure (convertTree np e.tree)

/-- Names are the sole constructor assertion; parameter-index validity is not
checked, src/ParametricExpression.jl:98-117. Scalar promotion is represented by
`leafConvert` separately. -/
def constructP (e : PExpression) : Jl PExpression :=
  if e.parameterNames.any (fun ns => ns.length != e.parameters.nrows) then
    .error (.assertionError "parameter_names length")
  else .ok e

/-- Signed class indexing raises BoundsError at zero/negative entries,
src/ParametricExpression.jl:388-391. -/
def parameterAt (P : JMat JF) (i : Nat) (c : Int) : Jl JF :=
  if c < 1 then .error .boundsError else P.get? i c.toNat

/-- Validation order, src/ParametricExpression.jl:385-386. Since PR #246 the
upper-bound assertion short-circuits on an empty class vector. -/
def checkClasses (ncols nclasses : Nat) (classes : List Int) : Jl Unit :=
  if classes.length != ncols then .error (.assertionError "class length")
  else match classes with
    | [] => .ok ()
    | c :: cs => if cs.foldl max c > Int.ofNat nclasses then
        .error (.assertionError "class upper bound") else .ok ()

/-- Column-major matrix with a fixed row count. The comprehension and `vcat`
keep `size(parameters, 1) + size(X, 1)` rows even with zero columns. -/
def ofColumnsN (n : Nat) (xs : List (List JF)) : Option (JMat JF) :=
  if h : ∀ k : Fin xs.length, (xs[k.val]).length = n then
    some (JMat.ofFn n xs.length fun i j =>
      (xs[j.val])[i.val]'(by have hj := h j; simpa only [hj] using i.isLt))
  else none

/-- Gather each parameter class column and prepend its rows, then append the
input feature column, src/ParametricExpression.jl:387-392. -/
def augment (P X : JMat JF) (classes : List Int) : Jl (JMat JF) := do
  checkClasses X.ncols P.ncols classes
  let columns ← classes.zipIdx |>.mapM fun (c,j) => do
    let ps ← (List.range P.nrows).mapM (fun i => parameterAt P (i+1) c)
    let xs ← (List.range X.nrows).mapM (fun i => X.get? (i+1) (j+1))
    pure (ps ++ xs)
  match ofColumnsN (P.nrows + X.nrows) columns with
  | some Y => pure Y
  | none => .error (.argumentError "ragged augmentation")

/-- Wrapper delegates the converted tree and augmented matrix to the ordinary
backend, src/ParametricExpression.jl:378-397. The backend argument is the shared
ordinary evaluator, including its incomplete-result flag. -/
def evalP (backend : Tree JF → JMat JF → OpEnum JF → Jl (Array JF × Bool))
    (e : PExpression) (X : JMat JF) (classes : List Int)
    (override : Option (OpEnum JF) := none) : Jl (Array JF × Bool) := do
  let Y ← augment e.parameters X classes
  let t ← convertP e
  backend t Y (override.getD e.operators)

/-- Callable overload invalidates incomplete output, src/ParametricExpression.jl:368-377. -/
def callP (result : Jl (Array JF × Bool)) : Jl (Array JF) := do
  let (ys,ok) ← result
  pure (if ok then ys else Array.replicate ys.size .nan)

/-- Missing classes is an explicit error, src/ParametricExpression.jl:361-366. -/
def missingClasses : Jl (Array JF × Bool) :=
  .error (.errorException "must pass classes")

/-- Parameter names default to p1,..., prepended to x1,... or explicit names;
size assertion precedes rendering, src/ParametricExpression.jl:399-436.
Display names and units are ignored by this overload. -/
def stringNames (e : PExpression) (override : Option (List String) := none) : Jl (List String) := do
  let np16 ← checkedUInt16 e.parameters.nrows
  let np := np16.toNat
  let pn := e.parameterNames.getD ((List.range np).map fun i => "p" ++ toString (i+1))
  let vn := (override.or e.variableNames).getD
    ((List.range (maxFeature e.tree)).map fun i => "x" ++ toString (i+1))
  let names := pn ++ vn
  if names.length ≥ np + maxFeature e.tree then .ok names
  else .error (.assertionError "variable names length")

def stringP (render : Tree JF → OpEnum JF → List String → String) (e : PExpression) : Jl String := do
  let names ← stringNames e
  let t ← convertP e
  pure (render t e.operators names)

/-- Symbol parsing checks variables before parameters, src/ParametricExpression.jl:447-465. -/
def parseSymbol (s : String) (vn pn : List String) : Jl PTree :=
  match vn.idxOf? s with
  | some i => do
    let j ← checkedUInt16 (i+1)
    pure (.feature j.toNat)
  | none => match pn.idxOf? s with
    | some i => do
      let j ← checkedUInt16 (i+1)
      pure (.const (.parameter j.toNat))
    | none => .error (.assertionError "unknown symbol")

/-- Non-symbol nodes pass through; scalar inputs become constants;
expression inputs fail, src/ParametricExpression.jl:447,466-470. -/
inductive ParseInput where
  | expression | node (t : PTree) | scalar (v : JF)
def parseOther : ParseInput → Jl PTree
  | .expression => .error (.assertionError "expression leaf")
  | .node t => .ok t
  | .scalar v => .ok (.const (.constant v))

/-- Scalar parameter-array unpacking stops when either side ends,
src/ParametricExpression.jl:252-258; list order is matrix column-major order. -/
def setArray : List JF → List JF → List JF
  | old, [] => old
  | [], _ => []
  | _ :: old, v :: vs => v :: setArray old vs

/-- Mutable scalar-constant references and parameter data. `Heap` preserves
node identity, including aliased constants, src/ParametricExpression.jl:260-285. -/
structure ConstantState where
  heap : Heap JF
  refs : List Addr
  params : List JF

def getConstants (s : ConstantState) : Jl (List JF) := do
  let cs ← s.refs.mapM s.heap.read
  pure (cs ++ s.params)

/-- Constants use node references; remaining entries are passed to the
truncating parameter setter. Since PR #245 the supplied length must equal the
getter's count exactly, otherwise `DimensionMismatch` is thrown before any
write, src/ParametricExpression.jl:270-285. -/
def writeConstants (h : Heap JF) : List Addr → List JF → Jl (Heap JF)
  | [], [] => .ok h
  | a :: as, v :: vs => do writeConstants (← h.write a v) as vs
  | _, _ => .error .boundsError

def dimensionMismatch : JlError := .errorException "DimensionMismatch"

def setConstants (s : ConstantState) (vs : List JF) : Jl ConstantState :=
  if vs.length ≠ s.refs.length + s.params.length then .error dimensionMismatch
  else do
    let h ← writeConstants s.heap s.refs (vs.take s.refs.length)
    pure { s with heap := h, params := setArray s.params (vs.drop s.refs.length) }

/-- Gradient extraction concatenates static-constant derivatives with
column-major parameter derivatives, src/ParametricExpression.jl:286-303. -/
def extractGradient (treeGradient paramGradient : List JF) := treeGradient ++ paramGradient

/-- Matrix storage before/after a copy. `similar` leaves values uninitialized,
src/ParametricExpression.jl:477; shape is defined independently of values. -/
structure MatrixBuffer where
  nrows : Nat
  ncols : Nat
  values : Option (JMat JF)

def emptyBuffer (P : JMat JF) : MatrixBuffer := ⟨P.nrows,P.ncols,none⟩
def filledBuffer (P : JMat JF) : MatrixBuffer := ⟨P.nrows,P.ncols,some P⟩

/-- Preallocation reserves a distinct parameter matrix and tree node slots,
src/ParametricExpression.jl:472-493. Node storage is addressed, not pure-tree
replacement; parameter copies require the destination shape. -/
structure PContainer where
  slots : List Addr
  parameters : MatrixBuffer

def allocateP (allocTree : PTree → Option Nat → List Addr)
    (e : PExpression) (n : Option Nat := none) : PContainer :=
  ⟨allocTree e.tree n, emptyBuffer e.parameters⟩

def copyIntoP (copyTree : List Addr → PTree → Jl PTree)
    (dest : PContainer) (src : PExpression) : Jl PExpression := do
  let t ← copyTree dest.slots src.tree
  if dest.parameters.nrows != src.parameters.nrows ||
      dest.parameters.ncols != src.parameters.ncols then
    .error (.argumentError "broadcast dimensions")
  else pure { src with tree := t, parameters := src.parameters }

/-- Named tuple member order and structure function, src/StructuredExpression.jl:76-110. -/
structure SExpression where
  trees : List (String × PExpression)
  structureFn : List (String × PExpression) → PTree
  operators : OpEnum JF
  variableNames : Option (List String)

/-- Both constructors obtain types/default metadata from the first member,
src/StructuredExpression.jl:92-111; empty tuples fail at first(). -/
def constructS (trees : List (String × PExpression))
    (f : List (String × PExpression) → PTree)
    (o : Option (OpEnum JF) := none) (vn : Option (List String) := none) : Jl SExpression :=
  match trees with
  | [] => .error (.argumentError "empty first")
  | (_,e) :: _ => .ok ⟨trees, f, o.getD e.operators, vn.or e.variableNames⟩

/-- get_tree invokes the supplied function on the actual named members,
src/StructuredExpression.jl:133-135. -/
def getTreeS (s : SExpression) : PTree := s.structureFn s.trees

/-- Copies each member with the supplied sharing policy and retains the
structure function, src/StructuredExpression.jl:113-126. -/
def copyS (copyMember : Bool → PExpression → PExpression) (s : SExpression)
    (breakSharing : Bool := false) : SExpression :=
  { s with trees := s.trees.map fun (k, e) => (k, copyMember breakSharing e) }

/-- Flatten in named member order, src/StructuredExpression.jl:153-161. -/
def flattenS (members : List (List JF)) : List JF := members.flatten

/-- Memberwise slicing by each member's getter count `r.n`,
src/StructuredExpression.jl:168-175. Leaf-state updates use the reference heap. -/
def setMembers : List ConstantState → List JF → Jl (List ConstantState)
  | [], _ => .ok []
  | s :: ss, vs => do
      let old ← getConstants s
      if vs.length < old.length then .error .boundsError
      else
        let t ← setConstants s (vs.take old.length)
        let ts ← setMembers ss (vs.drop old.length)
        pure (t :: ts)

/-- Since PR #245 the total length must equal `sum(r -> r.n, refs)` before any
member is set, src/StructuredExpression.jl:162-177. -/
def setS (states : List ConstantState) (vs : List JF) : Jl (List ConstantState) := do
  let olds ← states.mapM getConstants
  if vs.length ≠ (olds.map List.length).sum then .error dimensionMismatch
  else setMembers states vs

/-- Memberwise preallocation and copy, preserving named order and outer
metadata, src/StructuredExpression.jl:179-189. -/
def allocateS (allocate : PExpression → Option Nat → PContainer)
    (s : SExpression) (n : Option Nat := none) : List (String × PContainer) :=
  s.trees.map fun (k,e) => (k,allocate e n)

def copyIntoS (copyMember : PContainer → PExpression → Jl PExpression)
    (dest : List (String × PContainer)) (src : SExpression) : Jl SExpression := do
  if dest.length != src.trees.length then .error (.argumentError "tuple map lengths")
  else
    let ts ← (dest.zip src.trees).mapM fun ((_,d),(k,e)) => do
      pure (k, ← copyMember d e)
    pure { src with trees := ts }

end DynExpr.ParamStruct
