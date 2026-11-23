import DynExpr.Arena.Simulation

namespace DynExpr.Arena

/-- Worklist of nodes visited by the root-first traversal without early exit. -/
def preorderEntries (s : Store T) : Nat → Int32 → Jl (List (Int32 × Entry T))
  | 0, _ => .error (.undefinedBehavior "arena cycle")
  | n + 1, i => do
    let e ← loadEntry s i
    let cs ← e.active
    let visits ← cs.mapM (preorderEntries s n)
    return (i, e) :: visits.flatten

/-- Worklist of all nodes in the compact storage traversal. -/
def storageEntries (s : Store T) : Jl (List (Int32 × Entry T)) :=
  (List.range s.nodes.size).mapM (storageItem s)

private theorem any_mapM {f : A → Jl B} {g : A → Jl Bool} {p : B → Bool}
    {xs : List A} {ys : List B} (h : xs.mapM f = .ok ys)
    (agree : ∀ x y, f x = .ok y → g x = .ok (p y)) :
    xs.anyM g = .ok (ys.any p) := by
  induction xs generalizing ys with
  | nil =>
    have h' : ([] : List B) = ys := Except.ok.inj h
    subst ys
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error err => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases hs : xs.mapM f with
      | error err => simp [hx, hs, bind, Except.bind] at h
      | ok ys' =>
        simp [hx, hs, bind, Except.bind, pure, Except.pure] at h
        subst ys
        cases hp : p y <;> simp [List.anyM, agree x y hx, bind, Except.bind, pure, Except.pure, hp, ih hs]

private theorem preorder_any {s : Store T} {n : Nat} {i : Int32}
    {xs : List (Int32 × Entry T)} (h : preorderEntries s n i = .ok xs)
    (p : Int32 → Entry T → Bool) :
    preorder s (fun j e => .ok (p j e)) n i = .ok (xs.any (fun (j,e) => p j e)) := by
  induction n generalizing i xs with
  | zero => simp [preorderEntries] at h
  | succ n ih =>
    rw [preorderEntries] at h
    rw [preorder]
    cases he : loadEntry s i with
    | error err => simp [he, bind, Except.bind] at h
    | ok e =>
      cases hc : e.active with
      | error err => simp [he, hc, bind, Except.bind] at h
      | ok cs =>
        cases hv : cs.mapM (preorderEntries s n) with
        | error err => simp [he, hc, hv, bind, Except.bind] at h
        | ok visits =>
          simp [he, hc, hv, bind, Except.bind, pure, Except.pure] at h
          subst xs
          have ha := any_mapM hv (fun _ _ hx => ih hx)
          cases hp : p i e <;> simp [hc, bind, Except.bind, pure, Except.pure,
            hp, ha, List.any_flatten]

/-- Storage layout cannot change the Boolean answer for pure predicates, if the
compact flag describes exactly the reachable tree. The permutation hypothesis
expresses that invariant on individual entries rather than on query results. -/
def any_pure : Prop := ∀ (s : Store Nat) (i : Int32) (p : Int32 → Entry Nat → Bool)
    (xs : List (Int32 × Entry Nat)),
  preorderEntries s s.nodes.size i = .ok xs →
  (compactRoot s i = true → ∃ ys, storageEntries s = .ok ys ∧ ys.Perm xs) →
  anyNode s i (fun j e => .ok (p j e)) = .ok (xs.any (fun (j,e) => p j e))

private theorem storage_any {s : Store T} {ys : List (Int32 × Entry T)}
    (hy : storageEntries s = .ok ys) (p : Int32 → Entry T → Bool) :
    (List.range s.nodes.size).anyM (fun k => do
      let (j, e) ← storageItem s k
      Except.ok (p j e)) = .ok (ys.any (fun (j,e) => p j e)) := by
  apply any_mapM hy
  rintro k ⟨j, e⟩ hk
  simp only [hk, bind, Except.bind]

theorem any_pure_holds : any_pure := by
  intro s i p xs hx hw
  cases h : compactRoot s i with
  | false => simpa [anyNode, h] using preorder_any hx p
  | true =>
    obtain ⟨ys, hy, hp⟩ := hw h
    rw [anyNode, h, ← hp.any_eq]
    exact storage_any hy p

example : ∃ (s : Store Nat) (i : Int32) (xs : List (Int32 × Entry Nat)),
  preorderEntries s s.nodes.size i = .ok xs ∧ storageEntries s = .ok xs :=
  ⟨{ nodes := #[some ⟨2, #[], 0, 0, 0, true⟩] }, 1, [(1, ⟨2, #[], 0, 0, 0, true⟩)], rfl, rfl⟩

end DynExpr.Arena
