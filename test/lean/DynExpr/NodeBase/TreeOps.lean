import DynExpr.Model.Tree
import DynExpr.NodeBase.Types

/-!
Traversals, equality and hashing of plain `Node` trees (`src/base.jl`).
`Node` declares `preserve_sharing = false` (`src/Node.jl:344`), so
`tree_mapreduce` never consults an identity map and these functions are
modelled on the pure `Tree`.
-/

namespace DynExpr.NodeBase
open DynExpr

variable {T R B G : Type}

/-- Number of children visited by the `@nif` dispatch on degree `d`
(`src/base.jl:137-148`): degrees above `D` fall through to the last branch. -/
def nifDeg (D d : Nat) : Nat := if d ≤ D then d else D

/-- Every branch has at most `D` children (degree bound of `src/Node.jl:407-419`). -/
def DegLe (D : Nat) : Tree T → Prop
  | .const _ | .feature _ => True
  | .branch _ cs => cs.length ≤ D ∧ ∀ c ∈ cs, DegLe D c

/-- Depth-first traversal order of `tree_mapreduce`: `f_branch` runs on a
parent before its children are visited left to right (`src/base.jl:132-148`). -/
def preorder : Tree T → List (Tree T)
  | .const v => [.const v]
  | .feature i => [.feature i]
  | .branch o cs => .branch o cs :: preorderF cs
where
  preorderF : List (Tree T) → List (Tree T)
    | [] => []
    | c :: cs => preorder c ++ preorderF cs

section mapreduce
variable {m : Type → Type} [Monad m]

mutual
  /-- `call_mapreducer` without an identity map (`src/base.jl:123-158`),
  the path taken by `tree_mapreduce` on `Node` (`src/base.jl:96-109`). -/
  def tmrT (D : Nat) (fLeaf : Tree T → m R) (fBranch : Tree T → m B)
      (op : B → List R → m R) : Tree T → m R
    | .const v => fLeaf (.const v)
    | .feature i => fLeaf (.feature i)
    | .branch o cs =>
      if cs.length = 0 then fLeaf (.branch o cs)
      else do
        let b ← fBranch (.branch o cs)
        let rs ← tmrF D fLeaf fBranch op (nifDeg D cs.length) cs
        op b rs
  /-- The `@ncall` over the first `k` children (`src/base.jl:140-146`). -/
  def tmrF (D : Nat) (fLeaf : Tree T → m R) (fBranch : Tree T → m B)
      (op : B → List R → m R) : Nat → List (Tree T) → m (List R)
    | 0, _ => pure []
    | _ + 1, [] => pure []
    | k + 1, c :: cs => do
      let r ← tmrT D fLeaf fBranch op c
      let rs ← tmrF D fLeaf fBranch op k cs
      pure (r :: rs)
end

end mapreduce

/-- Specification: the simple recursive fold described in the docstring of
`tree_mapreduce` (`src/base.jl:29-76`). -/
def foldSpec (fLeaf : Tree T → R) (fBranch : Tree T → B) (op : B → List R → R) :
    Tree T → R
  | .const v => fLeaf (.const v)
  | .feature i => fLeaf (.feature i)
  | .branch o cs =>
    if cs.length = 0 then fLeaf (.branch o cs)
    else op (fBranch (.branch o cs)) (foldSpecF fLeaf fBranch op cs)
where
  foldSpecF (fLeaf : Tree T → R) (fBranch : Tree T → B) (op : B → List R → R) :
      List (Tree T) → List R
    | [] => []
    | c :: cs => foldSpec fLeaf fBranch op c :: foldSpecF fLeaf fBranch op cs

/-- `count_nodes` on a `Node` (`src/base.jl:271-280`). -/
def countNodesT (D : Nat) (t : Tree T) : Nat :=
  Id.run (tmrT D (fun _ => pure 1) (fun _ => pure 1) (fun b rs => pure (b + rs.sum)) t)

/-- `count(f, tree; init)` on a `Node` (`src/base.jl:389-400`). -/
def countT (D : Nat) (f : Tree T → Bool) (init : Nat) (t : Tree T) : Nat :=
  Id.run (tmrT D (fun t => pure (if f t then 1 else 0)) (fun t => pure (if f t then 1 else 0))
    (fun b rs => pure (b + rs.sum)) t) + init

/-- `sum(f, tree)` on a `Node` (`src/base.jl:410-418,433-448`): `mapreduce(f, +)`
with `+` applied to the parent's value and all child results. -/
def sumT (D : Nat) (f : Tree T → Int) (t : Tree T) : Int :=
  Id.run (tmrT D (fun t => pure (f t)) (fun t => pure (f t)) (fun b rs => pure (b + rs.sum)) t)

mutual
  /-- `any(f, tree)` with early exit (`src/base.jl:177-191`). -/
  def anyT (D : Nat) (f : Tree T → Bool) : Tree T → Bool
    | .const v => f (.const v)
    | .feature i => f (.feature i)
    | .branch o cs =>
      if cs.length = 0 then f (.branch o cs)
      else f (.branch o cs) || anyF D f (nifDeg D cs.length) cs
  /-- The `@nany` over the first `k` children (`src/base.jl:186`). -/
  def anyF (D : Nat) (f : Tree T → Bool) : Nat → List (Tree T) → Bool
    | 0, _ => false
    | _ + 1, [] => false
    | k + 1, c :: cs => anyT D f c || anyF D f k cs
end

/-- `foreach(f, tree)` (`src/base.jl:287-298`): `f` runs at every leaf and
branch through `tree_mapreduce` with the reducer `Returns(nothing)`. -/
def foreachT {σ : Type} (D : Nat) (f : Tree T → StateT σ Jl Unit) (t : Tree T) :
    StateT σ Jl Unit := do
  let _ ← tmrT D (fun x => f x) (fun x => f x) (fun (_ : Unit) (_ : List Unit) => pure ()) t
  pure ()

/-- One `foreach` callback of `filter_map!` (`src/base.jl:333-338`). The state
is the `Ref` pointer and the destination vector (modelled as a list); the
unchecked write `@inbounds destination[pointer.x += 1]` is undefined
behaviour out of range. -/
def fmStep (ff : Tree T → Bool) (mf : Tree T → G) (t : Tree T) :
    StateT (Nat × List G) Jl Unit :=
  if ff t then do
    let s ← get
    let p := s.1 + 1
    if p ≤ s.2.length then set (p, s.2.set (p - 1) (mf t))
    else throw (.undefinedBehavior "@inbounds destination[pointer] out of range")
  else pure ()

/-- `filter_map!` (`src/base.jl:325-340`), returning the final destination. -/
def filterMapBangT (D : Nat) (ff : Tree T → Bool) (mf : Tree T → G) (dest : List G)
    (t : Tree T) : Jl (List G) :=
  ((foreachT D (fmStep ff mf) t).run (0, dest)).map (·.2.2)

/-- `filter_map` (`src/base.jl:308-318`): the destination is
`Array{GT}(undef, count(filter_fnc, tree))`; `none` is an unset slot. -/
def filterMapT (D : Nat) (ff : Tree T → Bool) (mf : Tree T → G) (t : Tree T) :
    Jl (List (Option G)) :=
  filterMapBangT D ff (fun x => some (mf x)) (List.replicate (countT D ff 0 t) none) t

/-- `collect(tree)` (`src/base.jl:347-360`): `filter(_ -> true, tree)`. -/
def collectT (D : Nat) (t : Tree T) : Jl (List (Option (Tree T))) :=
  filterMapT D (fun _ => true) id t

/-- `length(tree)` (`src/base.jl:457-459`). -/
def lengthT (D : Nat) (t : Tree T) : Nat := countNodesT D t

/-- Constant values of a tree, in depth-first order. -/
def constVals : Tree T → List T
  | .const v => [v]
  | .feature _ => []
  | .branch _ cs => go cs
where
  go : List (Tree T) → List T
    | [] => []
    | t :: ts => constVals t ++ go ts

/-! ## Equality and hashing -/

/-- Fields of a degree-zero node read by `leaf_equal`/`leaf_hash`:
`(constant, val, feature)`. A childless `branch` is not representable; it is
read as `Graph.branchCell` stores it (non-constant, feature 0). -/
def leafView : Tree T → Bool × Option T × Nat
  | .const v => (true, some v, 0)
  | .feature i => (false, none, i)
  | .branch _ _ => (false, none, 0)

/-- `leaf_equal` (`src/base.jl:250-260`) with the element `==` given by `veq`. -/
def leafEq (veq : T → T → Bool) (a b : Tree T) : Bool :=
  let (ca, va, fa) := leafView a
  let (cb, vb, fb) := leafView b
  if ca != cb then false
  else if ca then
    match va, vb with
    | some x, some y => veq x y
    | _, _ => false
  else fa == fb

mutual
  /-- `inner_is_equal` without identity maps (`src/base.jl:196-245`), the
  path of `==` on `Node`. Degree mismatch is false; degree zero uses
  `leaf_equal`; branches compare `op` and then children with `@nall`. -/
  def eqT (D : Nat) (veq : T → T → Bool) : Tree T → Tree T → Bool
    | .branch o cs, .branch o' cs' =>
      if cs.length ≠ cs'.length then false
      else if cs.length = 0 then true
      else o == o' && eqF D veq (nifDeg D cs.length) cs cs'
    | .branch o cs, .const y =>
      if cs.length ≠ 0 then false else leafEq veq (.branch o cs) (.const y)
    | .branch o cs, .feature j =>
      if cs.length ≠ 0 then false else leafEq veq (.branch o cs) (.feature j)
    | .const x, .branch o cs =>
      if 0 ≠ cs.length then false else leafEq veq (.const x) (.branch o cs)
    | .feature i, .branch o cs =>
      if 0 ≠ cs.length then false else leafEq veq (.feature i) (.branch o cs)
    | .const x, .const y => leafEq veq (.const x) (.const y)
    | .const x, .feature j => leafEq veq (.const x) (.feature j)
    | .feature i, .const y => leafEq veq (.feature i) (.const y)
    | .feature i, .feature j => leafEq veq (.feature i) (.feature j)
  /-- `@nall` over the first `k` child pairs (`src/base.jl:231-233`). -/
  def eqF (D : Nat) (veq : T → T → Bool) : Nat → List (Tree T) → List (Tree T) → Bool
    | 0, _, _ => true
    | _ + 1, [], _ => true
    | _ + 1, _ :: _, [] => true
    | k + 1, a :: as, b :: bs => eqT D veq a b && eqF D veq k as bs
end

/-- The value Julia hashes at each node (`src/base.jl:467-486`): leaves hash
`(0, val)` or `(1, feature)`, branches hash `(degree + 1, op, children)`. The
leaf value enters only through its own hash `hv val`. -/
inductive HKey where
  | leafC (h : Nat)
  | leafF (f : Nat)
  | branch (deg op : Nat) (cs : List HKey)
  deriving Repr

/-- `leaf_hash` (`src/base.jl:481-483`). -/
def leafHash (hv : T → Nat) (t : Tree T) : HKey :=
  match leafView t with
  | (true, some v, _) => .leafC (hv v)
  | (true, none, _) => .leafC 0
  | (false, _, f) => .leafF f

/-- Operator index stored in a node. -/
def opOf : Tree T → Nat
  | .branch o _ => o
  | _ => 0

/-- `hash(tree, h)` on a `Node` (`src/base.jl:467-480`): `tree_mapreduce` with
`leaf_hash`, `identity` on branches and `branch_hash` as the reducer. -/
def hkeyT (D : Nat) (hv : T → Nat) (t : Tree T) : HKey :=
  Id.run (tmrT D (fun t => pure (leafHash hv t)) (fun t => pure t)
    (fun p cs => pure (.branch (p.degree + 1) (opOf p) cs)) t)

/-- Julia `Float64` values with both zeros, for `==`, `isequal` and `hash`
(Base semantics: `0.0 == -0.0` but `!isequal(0.0, -0.0)`; `NaN != NaN` but
`isequal(NaN, NaN)`). Other values are represented by an integer code. -/
inductive SF where
  | posZero
  | negZero
  | nan
  | other (x : Int)
  deriving DecidableEq, Repr

/-- Julia `==` on `Float64`. -/
def SF.jeq : SF → SF → Bool
  | .posZero, .posZero | .posZero, .negZero | .negZero, .posZero | .negZero, .negZero => true
  | .other x, .other y => x == y
  | _, _ => false

/-- Julia `isequal` on `Float64`. -/
def SF.isequal (x y : SF) : Bool := x == y

/-! ## Properties -/

/-- Forest step of `tree_mapreduce_fold`. -/
private theorem tmrF_spec (D : Nat) (fLeaf : Tree T → R) (fBranch : Tree T → B)
    (op : B → List R → R) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, tmrT (m := Id) D (fun t => pure (fLeaf t)) (fun t => pure (fBranch t))
      (fun b rs => pure (op b rs)) c = foldSpec fLeaf fBranch op c) :
    tmrF (m := Id) D (fun t => pure (fLeaf t)) (fun t => pure (fBranch t))
      (fun b rs => pure (op b rs)) cs.length cs = foldSpec.foldSpecF fLeaf fBranch op cs := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [List.length_cons, tmrF, foldSpec.foldSpecF]
    rw [ih c (by simp), ihc (fun x hx => ih x (by simp [hx]))]
    rfl

/-- On plain `Node` trees with degrees at most `D`, `tree_mapreduce` equals
the simple recursive fold. -/
def tree_mapreduce_fold : Prop :=
  ∀ (T R B : Type) (D : Nat) (fLeaf : Tree T → R) (fBranch : Tree T → B)
    (op : B → List R → R) (t : Tree T), DegLe D t →
    tmrT (m := Id) D (fun t => pure (fLeaf t)) (fun t => pure (fBranch t))
      (fun b rs => pure (op b rs)) t = foldSpec fLeaf fBranch op t

theorem tree_mapreduce_fold_holds : tree_mapreduce_fold := by
  intro T R B D fLeaf fBranch op t
  induction t using Tree.induction with
  | hc v => intro _; rfl
  | hf i => intro _; rfl
  | hb o cs ih =>
    intro hd
    simp only [DegLe] at hd
    have hk : nifDeg D cs.length = cs.length := by simp [nifDeg, hd.1]
    simp only [tmrT, foldSpec, hk]
    split
    · rfl
    · rw [tmrF_spec D fLeaf fBranch op cs (fun c hc => ih c hc (hd.2 c hc))]
      rfl

example : DegLe 2 (Tree.branch 1 [Tree.const (1 : Nat), Tree.feature 1]) := by
  simp [DegLe]

/-- Forest form of the node count. -/
private theorem foldSpecF_size (cs : List (Tree T))
    (ih : ∀ c ∈ cs, foldSpec (fun _ => 1) (fun _ => 1) (fun b rs => b + rs.sum) c = c.size) :
    (foldSpec.foldSpecF (fun _ => 1) (fun _ => 1) (fun b rs => b + rs.sum) cs).sum =
      (cs.map Tree.size).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [foldSpec.foldSpecF, List.sum_cons, List.map_cons]
    rw [ih c (by simp), ihc (fun x hx => ih x (by simp [hx]))]

/-- Specification fold of the count. -/
private theorem foldSpec_size (t : Tree T) :
    foldSpec (fun _ => 1) (fun _ => 1) (fun b rs => b + rs.sum) t = t.size := by
  induction t using Tree.induction with
  | hc v => simp [foldSpec, Tree.size]
  | hf i => simp [foldSpec, Tree.size]
  | hb o cs ih =>
    simp only [foldSpec, Tree.size_branch]
    split
    · next h => simp [List.length_eq_zero_iff.mp h]
    · rw [foldSpecF_size cs ih]

/-- `count_nodes` and `length` on a plain `Node` equal the number of nodes of
the unfolded tree. -/
def count_nodes_tree : Prop :=
  ∀ (T : Type) (D : Nat) (t : Tree T), DegLe D t →
    countNodesT D t = t.size ∧ lengthT D t = t.size

theorem count_nodes_tree_holds : count_nodes_tree := by
  intro T D t hd
  have h : countNodesT D t = t.size := by
    unfold countNodesT
    rw [tree_mapreduce_fold_holds T Nat Nat D (fun _ => 1) (fun _ => 1)
      (fun b rs => b + rs.sum) t hd]
    exact foldSpec_size t
  exact ⟨h, h⟩


/-! ### Traversal order: `foreach`, `filter_map!`, `count`, `sum`, `any` -/

/-- Run a callback on each node of a list, in order. -/
def runAll {σ : Type} (f : Tree T → StateT σ Jl Unit) : List (Tree T) → StateT σ Jl Unit
  | [] => pure ()
  | x :: xs => do f x; runAll f xs

private theorem runAll_append {σ : Type} (f : Tree T → StateT σ Jl Unit) (l₁ l₂ : List (Tree T)) :
    runAll f (l₁ ++ l₂) = (do runAll f l₁; runAll f l₂) := by
  induction l₁ with
  | nil => simp [runAll]
  | cons x xs ih => simp [runAll, ih, bind_assoc]

/-- Forest step of `tmr_forM`. -/
private theorem tmrF_forM {σ : Type} (D : Nat) (f : Tree T → StateT σ Jl Unit)
    (cs : List (Tree T))
    (ih : ∀ c ∈ cs, tmrT D f f (fun (_ : Unit) (_ : List Unit) => pure ()) c = runAll f (preorder c)) :
    (do let _ ← tmrF D f f (fun (_ : Unit) (_ : List Unit) => pure ()) cs.length cs; pure ()) =
      runAll f (preorder.preorderF cs) := by
  induction cs with
  | nil => simp [tmrF, preorder.preorderF, runAll]
  | cons c cs ihc =>
    simp only [List.length_cons, tmrF, preorder.preorderF, runAll_append, bind_assoc,
      pure_bind]
    rw [ih c (by simp), ← ihc (fun x hx => ih x (by simp [hx]))]

/-- `tree_mapreduce` with a `Unit`-valued callback runs it on the nodes in
`preorder` (`src/base.jl:123-158,287-298`). -/
theorem tmr_forM {σ : Type} (D : Nat) (f : Tree T → StateT σ Jl Unit) (t : Tree T)
    (hd : DegLe D t) :
    tmrT D f f (fun (_ : Unit) (_ : List Unit) => pure ()) t = runAll f (preorder t) := by
  induction t using Tree.induction with
  | hc v => simp [tmrT, preorder, runAll]
  | hf i => simp [tmrT, preorder, runAll]
  | hb o cs ih =>
    simp only [DegLe] at hd
    have hk : nifDeg D cs.length = cs.length := by simp [nifDeg, hd.1]
    simp only [tmrT, preorder, hk, runAll]
    split
    · next h =>
      rw [List.length_eq_zero_iff.mp h]
      simp [preorder.preorderF, runAll]
    · rw [← tmrF_forM D f cs (fun c hc => ih c hc (hd.2 c hc))]

/-- Sequential unchecked writes `destination[p+1], destination[p+2], ...`. -/
def writeFrom : List G → Nat → List G → List G
  | d, _, [] => d
  | d, p, x :: xs => writeFrom (d.set p x) (p + 1) xs

private theorem writeFrom_eq (xs : List G) :
    ∀ (d : List G) (p : Nat), p + xs.length ≤ d.length →
      writeFrom d p xs = d.take p ++ xs ++ d.drop (p + xs.length) := by
  induction xs with
  | nil => intro d p _; simp [writeFrom]
  | cons x xs ih =>
    intro d p h
    simp only [List.length_cons] at h
    have hp : p < d.length := by omega
    simp only [writeFrom, List.length_cons]
    rw [ih (d.set p x) (p + 1) (by simp; omega)]
    have ha : (d.set p x).take (p+1) = d.take p ++ [x] := by
      rw [List.take_set, List.take_add_one, List.getElem?_eq_getElem hp, Option.toList_some,
        List.set_append_right _ _ (by simp; omega)]
      simp [Nat.min_eq_left (Nat.le_of_lt hp)]
    rw [ha, List.drop_set_of_lt (by omega)]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- Running the `filter_map!` callbacks over a list of nodes. -/
private theorem forM_fmStep (ff : Tree T → Bool) (mf : Tree T → G) (xs : List (Tree T)) :
    ∀ (p : Nat) (d : List G), p + (xs.filter ff).length ≤ d.length →
      (runAll (fmStep ff mf) xs).run (p, d) =
        .ok ((), (p + (xs.filter ff).length, writeFrom d p ((xs.filter ff).map mf))) := by
  induction xs with
  | nil => intro p d _; rfl
  | cons x xs ih =>
    intro p d h
    by_cases hx : ff x = true
    · simp only [List.filter_cons, hx, ite_true, List.length_cons] at h ⊢
      have hp : p + 1 ≤ d.length := by omega
      have hstep : (fmStep ff mf x).run (p, d) = .ok ((), (p + 1, d.set p (mf x))) := by
        unfold fmStep
        rw [ite_eq_left hx]
        simp [hp]
        rfl
      simp only [runAll, StateT.run_bind, hstep]
      show (runAll (fmStep ff mf) xs).run (p + 1, d.set p (mf x)) = _
      rw [ih (p + 1) (d.set p (mf x)) (by simp; omega)]
      simp only [List.map_cons, writeFrom]
      congr 3
      omega
    · simp only [List.filter_cons, hx, Bool.false_eq_true, ite_false] at h ⊢
      have hstep : (fmStep ff mf x).run (p, d) = .ok ((), (p, d)) := by
        unfold fmStep
        rw [ite_eq_right hx]
        rfl
      simp only [runAll, StateT.run_bind, hstep]
      exact ih p d h

/-- Forest form of the count specification. -/
private theorem foldSpecF_count (f : Tree T → Bool) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, foldSpec (fun t => if f t then 1 else 0) (fun t => if f t then 1 else 0)
      (fun b rs => b + rs.sum) c = ((preorder c).filter f).length) :
    (foldSpec.foldSpecF (fun t => if f t then 1 else 0) (fun t => if f t then 1 else 0)
      (fun b rs => b + rs.sum) cs).sum = ((preorder.preorderF cs).filter f).length := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [foldSpec.foldSpecF, List.sum_cons, preorder.preorderF, List.filter_append,
      List.length_append]
    rw [ih c (by simp), ihc (fun x hx => ih x (by simp [hx]))]

private theorem foldSpec_count (f : Tree T → Bool) (t : Tree T) :
    foldSpec (fun t => if f t then 1 else 0) (fun t => if f t then 1 else 0)
      (fun b rs => b + rs.sum) t = ((preorder t).filter f).length := by
  induction t using Tree.induction with
  | hc v => by_cases h : f (.const v) <;> simp [foldSpec, preorder, h]
  | hf i => by_cases h : f (.feature i) <;> simp [foldSpec, preorder, h]
  | hb o cs ih =>
    simp only [foldSpec, preorder, List.filter_cons]
    split
    · next h0 =>
      rw [List.length_eq_zero_iff.mp h0]
      by_cases h : f (.branch o []) <;> simp [preorder.preorderF, h]
    · rw [foldSpecF_count f cs ih]
      by_cases h : f (.branch o cs) <;> simp [h] <;> omega

private theorem foldSpecF_sum (f : Tree T → Int) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, foldSpec (fun t => f t) (fun t => f t) (fun b rs => b + rs.sum) c =
      ((preorder c).map f).sum) :
    (foldSpec.foldSpecF (fun t => f t) (fun t => f t) (fun b rs => b + rs.sum) cs).sum =
      ((preorder.preorderF cs).map f).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [foldSpec.foldSpecF, List.sum_cons, preorder.preorderF, List.map_append,
      List.sum_append]
    rw [ih c (by simp), ihc (fun x hx => ih x (by simp [hx]))]

private theorem foldSpec_sum (f : Tree T → Int) (t : Tree T) :
    foldSpec (fun t => f t) (fun t => f t) (fun b rs => b + rs.sum) t =
      ((preorder t).map f).sum := by
  induction t using Tree.induction with
  | hc v => simp [foldSpec, preorder]
  | hf i => simp [foldSpec, preorder]
  | hb o cs ih =>
    simp only [foldSpec, preorder, List.map_cons, List.sum_cons]
    split
    · next h0 =>
      rw [List.length_eq_zero_iff.mp h0]
      simp [preorder.preorderF]
    · rw [foldSpecF_sum f cs ih]

private theorem anyF_spec (D : Nat) (f : Tree T → Bool) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, anyT D f c = (preorder c).any f) :
    anyF D f cs.length cs = (preorder.preorderF cs).any f := by
  induction cs with
  | nil => rfl
  | cons c cs ihc =>
    simp only [List.length_cons, anyF, preorder.preorderF, List.any_append]
    rw [ih c (by simp), ihc (fun x hx => ih x (by simp [hx]))]

private theorem anyT_spec (D : Nat) (f : Tree T → Bool) (t : Tree T) (hd : DegLe D t) :
    anyT D f t = (preorder t).any f := by
  induction t using Tree.induction with
  | hc v => simp [anyT, preorder]
  | hf i => simp [anyT, preorder]
  | hb o cs ih =>
    simp only [DegLe] at hd
    have hk : nifDeg D cs.length = cs.length := by simp [nifDeg, hd.1]
    simp only [anyT, preorder, hk, List.any_cons]
    split
    · next h0 =>
      rw [List.length_eq_zero_iff.mp h0]
      simp [preorder.preorderF]
    · rw [anyF_spec D f cs (fun c hc => ih c hc (hd.2 c hc))]

/-- `filter_map!` writes `map_fnc` of exactly the nodes satisfying
`filter_fnc`, in `preorder`, into the first slots of the destination and
leaves the rest unchanged; `filter_map` returns exactly those values;
`collect` returns the nodes in `preorder`; `count`, `sum` and `any` agree with
the corresponding operations on the `preorder` list. -/
def traversal_tree : Prop :=
  ∀ (T G : Type) (D : Nat) (t : Tree T), DegLe D t →
    (∀ (ff : Tree T → Bool) (mf : Tree T → G) (dest : List G),
      ((preorder t).filter ff).length ≤ dest.length →
      filterMapBangT D ff mf dest t =
        .ok (((preorder t).filter ff).map mf ++ dest.drop ((preorder t).filter ff).length)) ∧
    (∀ (ff : Tree T → Bool) (mf : Tree T → G),
      filterMapT D ff mf t = .ok (((preorder t).filter ff).map (fun x => some (mf x)))) ∧
    collectT D t = .ok ((preorder t).map some) ∧
    (∀ (f : Tree T → Bool) (init : Nat), countT D f init t = ((preorder t).filter f).length + init) ∧
    (∀ (f : Tree T → Int), sumT D f t = ((preorder t).map f).sum) ∧
    (∀ (f : Tree T → Bool), anyT D f t = (preorder t).any f)

theorem traversal_tree_holds : traversal_tree := by
  intro T G D t hd
  have hbang : ∀ {G : Type} (ff : Tree T → Bool) (mf : Tree T → G) (dest : List G),
      ((preorder t).filter ff).length ≤ dest.length →
      filterMapBangT D ff mf dest t =
        .ok (((preorder t).filter ff).map mf ++ dest.drop ((preorder t).filter ff).length) := by
    intro G ff mf dest h
    unfold filterMapBangT foreachT
    rw [tmr_forM D (fmStep ff mf) t hd]
    have hrun := forM_fmStep ff mf (preorder t) 0 dest (by simpa using h)
    have hw := writeFrom_eq (((preorder t).filter ff).map mf) dest 0 (by simpa using h)
    simp only [StateT.run_bind, hrun]
    show Except.map _ (Except.ok ((), _)) = _
    simp only [Except.map, hw, List.take_zero, List.nil_append, Nat.zero_add, List.length_map]
  have hcount : ∀ (f : Tree T → Bool) (init : Nat),
      countT D f init t = ((preorder t).filter f).length + init := by
    intro f init
    unfold countT
    rw [tree_mapreduce_fold_holds T Nat Nat D _ _ (fun b rs => b + rs.sum) t hd]
    rw [foldSpec_count f t]
    rfl
  have hfm : ∀ {G : Type} (ff : Tree T → Bool) (mf : Tree T → G),
      filterMapT D ff mf t = .ok (((preorder t).filter ff).map (fun x => some (mf x))) := by
    intro G ff mf
    unfold filterMapT
    rw [hbang ff (fun x => some (mf x)) _ (by simp [hcount])]
    simp [hcount]
  refine ⟨fun ff mf dest h => hbang ff mf dest h, fun ff mf => hfm ff mf, ?_, hcount, ?_, ?_⟩
  · unfold collectT
    rw [hfm]
    congr 1
    rw [List.filter_eq_self.mpr (by simp)]
    rfl
  · intro f
    unfold sumT
    rw [tree_mapreduce_fold_holds T Int Int D _ _ (fun b rs => b + rs.sum) t hd]
    exact foldSpec_sum f t
  · intro f
    exact anyT_spec D f t hd

/-! ### Equality and hashing -/

private theorem eqF_spec (D : Nat) (veq : T → T → Bool) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, ∀ b : Tree T, b.Representable → DegLe D b → (eqT D veq c b = true ↔ c = b)) :
    ∀ cs' : List (Tree T), cs.length = cs'.length → (∀ b ∈ cs', b.Representable ∧ DegLe D b) →
      (eqF D veq cs.length cs cs' = true ↔ cs = cs') := by
  induction cs with
  | nil => intro cs' hl _; cases cs' <;> simp_all [eqF]
  | cons c cs ihc =>
    intro cs' hl hb
    cases cs' with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hb0 := hb b (by simp)
      simp only [List.length_cons, eqF, Bool.and_eq_true, List.cons.injEq]
      rw [ih c (by simp) b hb0.1 hb0.2,
        ihc (fun x hx => ih x (by simp [hx])) bs hl (fun x hx => hb x (by simp [hx]))]

/-- `==` on plain `Node` trees is structural equality (hence an equivalence)
when the element `==` is (no NaN-like values), for representable trees with
degrees at most `D`. -/
def eq_tree : Prop :=
  ∀ (T : Type) (D : Nat) (veq : T → T → Bool), (∀ x y, veq x y = true ↔ x = y) →
    ∀ a b : Tree T, a.Representable → b.Representable → DegLe D a → DegLe D b →
      (eqT D veq a b = true ↔ a = b)

theorem eq_tree_holds : eq_tree := by
  intro T D veq hveq a
  induction a using Tree.induction with
  | hc x =>
    intro b _ hbr _ _
    cases b with
    | const y => simp [eqT, leafEq, leafView, hveq]
    | feature j => simp [eqT, leafEq, leafView]
    | branch o cs =>
      simp only [Tree.Representable] at hbr
      simp [eqT, show 0 ≠ cs.length by omega]
  | hf i =>
    intro b _ hbr _ _
    cases b with
    | const y => simp [eqT, leafEq, leafView]
    | feature j => simp [eqT, leafEq, leafView]
    | branch o cs =>
      simp only [Tree.Representable] at hbr
      simp [eqT, show 0 ≠ cs.length by omega]
  | hb o cs ih =>
    intro b har hbr had hbd
    simp only [Tree.Representable] at har
    simp only [DegLe] at had
    cases b with
    | const y => simp [eqT, show cs.length ≠ 0 by omega]
    | feature j => simp [eqT, show cs.length ≠ 0 by omega]
    | branch o' cs' =>
      simp only [Tree.Representable] at hbr
      simp only [DegLe] at hbd
      by_cases hl : cs.length = cs'.length
      · have hk : nifDeg D cs.length = cs.length := by simp [nifDeg, had.1]
        have he : eqT D veq (.branch o cs) (.branch o' cs') =
            (o == o' && eqF D veq cs.length cs cs') := by
          simp only [eqT]
          rw [ite_eq_right (by simpa using hl), ite_eq_right (by omega), hk]
        rw [he, Bool.and_eq_true, beq_iff_eq, Tree.branch.injEq]
        rw [eqF_spec D veq cs (fun c hc b hb hbd' =>
          ih c hc b (har.2 c hc) hb (had.2 c hc) hbd') cs' hl
          (fun x hx => ⟨hbr.2 x hx, hbd.2 x hx⟩)]
      · have hne : cs ≠ cs' := fun h => hl (h ▸ rfl)
        have hf : eqT D veq (.branch o cs) (.branch o' cs') = false := by
          simp only [eqT]
          exact ite_eq_left hl
        rw [hf]
        simp only [Bool.false_eq_true, false_iff, Tree.branch.injEq, not_and]
        exact fun _ => hne

/-- Two well-formed `Node` trees whose constants agree under `isequal` have equal
hashes, for every element hash consistent with `isequal` (Julia's hash contract),
with `Float64` elements. Like Julia's own floats (`0.0 == -0.0` but
`hash(0.0) != hash(-0.0)`), `==`-equal trees need not hash equally. -/
def hash_eq : Prop :=
  ∀ (hv : SF → Nat), (∀ x y, SF.isequal x y = true → hv x = hv y) →
    ∀ (D : Nat) (a b : Tree SF), a.Representable → b.Representable → DegLe D a → DegLe D b →
      eqT D SF.isequal a b = true → hkeyT D hv a = hkeyT D hv b

theorem hash_eq_holds : hash_eq := by
  intro hv _ D a b har hbr had hbd h
  have hveq : ∀ x y, SF.isequal x y = true ↔ x = y := by
    intro x y; simp [SF.isequal]
  rw [(eq_tree_holds SF D SF.isequal hveq a b har hbr had hbd).1 h]

private theorem constVals_go_mem {c : Tree T} {cs : List (Tree T)} (hc : c ∈ cs) {v : T}
    (hv : v ∈ constVals c) : v ∈ constVals.go cs := by
  induction cs with
  | nil => simp at hc
  | cons d ds ih =>
    simp only [constVals.go, List.mem_append]
    rcases List.mem_cons.mp hc with rfl | h
    · exact Or.inl hv
    · exact Or.inr (ih h)

/-- Well-formedness and a constant predicate, for `eqT_sound_on`. -/
private def GoodT (D : Nat) (P : T → Prop) (t : Tree T) : Prop :=
  t.Representable ∧ DegLe D t ∧ ∀ v ∈ constVals t, P v

private theorem eqF_sound_on (D : Nat) (veq : T → T → Bool) (P : T → Prop) (cs : List (Tree T))
    (ih : ∀ c ∈ cs, ∀ b : Tree T, GoodT D P b → eqT D veq c b = true → c = b) :
    ∀ cs' : List (Tree T), cs.length = cs'.length → (∀ b ∈ cs', GoodT D P b) →
      eqF D veq cs.length cs cs' = true → cs = cs' := by
  induction cs with
  | nil => intro cs' hl _ _; cases cs' <;> simp_all
  | cons c cs ihc =>
    intro cs' hl hb he
    cases cs' with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.length_cons, eqF, Bool.and_eq_true] at he
      rw [ih c (by simp) b (hb b (by simp)) he.1,
        ihc (fun x hx => ih x (by simp [hx])) bs hl (fun x hx => hb x (by simp [hx])) he.2]

/-- Soundness of `==` when the element `==` is equality on the constants that
occur. -/
private theorem eqT_sound_on (D : Nat) (veq : T → T → Bool) (P : T → Prop)
    (hP : ∀ x y, P x → P y → veq x y = true → x = y) :
    ∀ a b : Tree T, GoodT D P a → GoodT D P b → eqT D veq a b = true → a = b := by
  intro a
  induction a using Tree.induction with
  | hc x =>
    intro b ha hb h
    cases b with
    | const y =>
      simp only [eqT, leafEq, leafView] at h
      simp at h
      rw [hP x y (ha.2.2 x (by simp [constVals])) (hb.2.2 y (by simp [constVals])) h]
    | feature j => simp [eqT, leafEq, leafView] at h
    | branch o cs =>
      have := hb.1
      simp only [Tree.Representable] at this
      simp [eqT, show 0 ≠ cs.length by omega] at h
  | hf i =>
    intro b ha hb h
    cases b with
    | const y => simp [eqT, leafEq, leafView] at h
    | feature j => simp [eqT, leafEq, leafView] at h; rw [h]
    | branch o cs =>
      have := hb.1
      simp only [Tree.Representable] at this
      simp [eqT, show 0 ≠ cs.length by omega] at h
  | hb o cs ih =>
    intro b ha hb h
    obtain ⟨har, had, hav⟩ := ha
    simp only [Tree.Representable] at har
    simp only [DegLe] at had
    cases b with
    | const y => simp [eqT, show cs.length ≠ 0 by omega] at h
    | feature j => simp [eqT, show cs.length ≠ 0 by omega] at h
    | branch o' cs' =>
      obtain ⟨hbr, hbd, hbv⟩ := hb
      simp only [Tree.Representable] at hbr
      simp only [DegLe] at hbd
      by_cases hl : cs.length = cs'.length
      · have hk : nifDeg D cs.length = cs.length := by simp [nifDeg, had.1]
        have he : eqT D veq (.branch o cs) (.branch o' cs') =
            (o == o' && eqF D veq cs.length cs cs') := by
          simp only [eqT]
          rw [ite_eq_right (by simpa using hl), ite_eq_right (by omega), hk]
        rw [he, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, eqF_sound_on D veq P cs (fun c hc b hgb hcb =>
          ih c hc b ⟨har.2 c hc, had.2 c hc, fun v hv => hav v (by
            simp only [constVals]; exact constVals_go_mem hc hv)⟩ hgb hcb) cs' hl
          (fun x hx => ⟨hbr.2 x hx, hbd.2 x hx, fun v hv => hbv v (by
            simp only [constVals]; exact constVals_go_mem hx hv)⟩) h.2]
      · have hf : eqT D veq (.branch o cs) (.branch o' cs') = false := by
          simp only [eqT]
          exact ite_eq_left hl
        rw [hf] at h
        exact absurd h (by simp)

/-- Companion of `hash_eq`: when no constant is negative zero (the only
`Float64` value that is `==` to a value it is not `isequal` to, apart from NaN
which is `==` to nothing), `==`-equal trees have equal hashes. -/
def hash_eq_no_negzero : Prop :=
  ∀ (hv : SF → Nat), (∀ x y, SF.isequal x y = true → hv x = hv y) →
    ∀ (D : Nat) (a b : Tree SF), a.Representable → b.Representable → DegLe D a → DegLe D b →
      (∀ v ∈ constVals a ++ constVals b, v ≠ .negZero) →
      eqT D SF.jeq a b = true → hkeyT D hv a = hkeyT D hv b

theorem hash_eq_no_negzero_holds : hash_eq_no_negzero := by
  intro hv _ D a b har hbr had hbd hnz h
  have hP : ∀ x y : SF, x ≠ .negZero → y ≠ .negZero → SF.jeq x y = true → x = y := by
    intro x y hx hy hxy
    cases x <;> cases y <;> simp_all [SF.jeq]
  have := eqT_sound_on D SF.jeq (fun v => v ≠ .negZero) hP a b
    ⟨har, had, fun v hv => hnz v (by simp [hv])⟩ ⟨hbr, hbd, fun v hv => hnz v (by simp [hv])⟩ h
  rw [this]

example : (Tree.const SF.posZero).Representable ∧ DegLe 2 (Tree.const SF.posZero) ∧
    (∀ v ∈ constVals (Tree.const SF.posZero) ++ constVals (Tree.const SF.posZero), v ≠ .negZero) := by
  simp [Tree.Representable, DegLe, constVals]

/-- With an element `==` that is equality, `==`-equal `Node` trees have equal
hashes. -/
def hash_eq_lawful : Prop :=
  ∀ (T : Type) (D : Nat) (veq : T → T → Bool) (hv : T → Nat), (∀ x y, veq x y = true ↔ x = y) →
    ∀ a b : Tree T, a.Representable → b.Representable → DegLe D a → DegLe D b →
      eqT D veq a b = true → hkeyT D hv a = hkeyT D hv b

theorem hash_eq_lawful_holds : hash_eq_lawful := by
  intro T D veq hv hveq a b har hbr had hbd h
  rw [(eq_tree_holds T D veq hveq a b har hbr had hbd).1 h]

example : (∀ x y : Nat, (x == y) = true ↔ x = y) := by intro x y; simp

end DynExpr.NodeBase
