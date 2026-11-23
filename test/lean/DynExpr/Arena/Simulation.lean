import DynExpr.Arena.Traversal

namespace DynExpr.Arena

/-- The plain Node reduction, with no identity memo and with callbacks depending
only on documented node data. `465d0ec1:src/base.jl:123-158`. -/
def plainFold (leaf : Tree T → Jl R) (branch : Nat → Nat → Jl B)
    (op : B → List R → Jl R) : Tree T → Jl R
  | .const x => leaf (.const x)
  | .feature i => leaf (.feature i)
  | .branch k cs => do
    let b ← branch k cs.length
    let rs ← cs.attach.mapM fun t => plainFold leaf branch op t.val
    op b rs
termination_by t => sizeOf t

decreasing_by
  have h := List.sizeOf_lt_of_mem t.property
  simp only [Tree.branch.sizeOf_spec]
  omega
def unfoldView (s : Store T) (id fuel : Nat) (i : Int32) : Jl (Tree T) :=
  entryMapReduce s id (fun _ e => .ok e.leaf) (fun _ e => .ok e.op.toNat)
    (fun op cs => .ok (.branch op cs)) fuel i

private theorem mapM_sim {F : α → Jl β} {G : α → Jl γ} {H : β → Jl γ}
    {xs : List α} {ys : List β}
    (each : ∀ x y, F x = .ok y → G x = H y) (h : xs.mapM F = .ok ys) :
    xs.mapM G = ys.mapM H ∧ xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h
    subst ys
    exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : F x with
    | error e => simp [hx, Bind.bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM F with
      | error e => simp [hx, hxs, Bind.bind, Except.bind] at h
      | ok ys' =>
        simp [hx, hxs, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst ys
        obtain ⟨he, hl⟩ := ih hxs
        simp [List.mapM_cons, each x y hx, he, hl]

private theorem fold_sim {s : Store T} {id fuel : Nat} {i : Int32} {t : Tree T}
    (h : unfoldView s id fuel i = .ok t) (leaf : Tree T → Jl R)
    (branch : Nat → Nat → Jl B) (op : B → List R → Jl R) :
    entryMapReduce s id (fun _ e => leaf e.leaf) (fun _ e => branch e.op.toNat e.degree.toNat)
      op fuel i = plainFold leaf branch op t := by
  induction fuel generalizing i t with
  | zero => simp [unfoldView, entryMapReduce] at h
  | succ n ih =>
    rw [unfoldView, entryMapReduce] at h
    rw [entryMapReduce]
    cases he : loadEntry s i with
    | error e => simp [he, Bind.bind, Except.bind] at h
    | ok e =>
      by_cases hd : e.degree = 0
      · simp [he, hd, Bind.bind, Except.bind] at h
        subst t
        cases hc : e.constant <;>
          simp [hd, Entry.leaf, hc, plainFold, Bind.bind, Except.bind]
        all_goals split <;> rfl
      · cases hs : e.active with
        | error err => simp [he, hd, hs, Bind.bind, Except.bind] at h
        | ok slots =>
          have hlen : slots.length = e.degree.toNat := by
            unfold Entry.active at hs
            split at hs
            · rename_i hh
              simp only [Except.ok.injEq] at hs
              subst slots
              simp [List.length_take, Nat.min_eq_left, hh]
            · contradiction
          change (do
            let e' ← loadEntry s i
            if e'.degree == 0 then pure e'.leaf else do
              let _ := e'.op.toNat
              let cs ← e'.active
              let children ← cs.mapM (unfoldView s id n)
              pure (.branch e'.op.toNat children)) = .ok t at h
          cases ht : slots.mapM (unfoldView s id n) with
          | error err => simp [he, hd, hs, ht, Bind.bind, Except.bind] at h
          | ok ts =>
            simp [he, hd, hs, ht, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
            subst t
            obtain ⟨hm, hn⟩ := mapM_sim (G := entryMapReduce s id
                (fun _ e => leaf e.leaf) (fun _ e => branch e.op.toNat e.degree.toNat) op n)
              (H := plainFold leaf branch op) (fun _ _ hc => ih hc) ht
            rw [plainFold]
            simp [hd, hs, ← hn, hlen, Bind.bind, Except.bind, hm]

/-- On well-formed reachable trees, numeric reduction commutes with conversion,
including callback failures. The callbacks observe leaf payload or branch op and degree. -/
def mapreduce_simulation : Prop := ∀ (s : Store Nat) (p : Handle) (t : Tree Nat)
    (leaf : Tree Nat → Jl Nat) (branch : Nat → Nat → Jl Nat) (combine : Nat → List Nat → Jl Nat),
  toTree s p = .ok t →
  entryMapReduce s p.arena (fun _ e => leaf e.leaf) (fun _ e => branch e.op.toNat e.degree.toNat)
    combine s.nodes.size p.idx = plainFold leaf branch combine t

theorem mapreduce_simulation_holds : mapreduce_simulation := by
  intro s p t leaf branch combine h
  exact fold_sim h leaf branch combine

example : ∃ (s : Store Nat) (p : Handle), toTree s p = .ok (.const 5) :=
  ⟨{ nodes := #[some ⟨5, #[], 0, 0, 0, true⟩] }, ⟨0, 1⟩, rfl⟩

/-- Node and ArenaNode hash the same shape, operators and leaf payloads, regardless
of arena layout. The same Julia hash implementation is used in both cases. -/
def hash_simulation : Prop := ∀ (s : Store Nat) (p : Handle) (t : Tree Nat)
    (mix : HashKey Nat → UInt64 → UInt64) (seed : UInt64),
  toTree s p = .ok t →
  hashTree mix seed s p =
    plainFold (fun x => .ok (mix (match x with
      | .const v => .const v
      | .feature i => .feature (UInt16.ofNat i)
      | .branch k _ => .branch 0 (UInt8.ofNat k) []) seed))
      (fun k d => .ok (d, UInt8.ofNat k))
      (fun (d, k) hs => .ok (mix (.branch ((d : Int) + 1) k hs) seed)) t

theorem hash_simulation_holds : hash_simulation := by
  intro s p t mix seed h
  let f : Tree Nat → Jl UInt64 := fun x => .ok (mix (match x with
    | .const v => .const v
    | .feature i => .feature (UInt16.ofNat i)
    | .branch k _ => .branch 0 (UInt8.ofNat k) []) seed)
  let g : Nat → Nat → Jl (Nat × UInt8) := fun k d => .ok (d, UInt8.ofNat k)
  let c : (Nat × UInt8) → List UInt64 → Jl UInt64 :=
    fun (d, k) hs => .ok (mix (.branch ((d : Int) + 1) k hs) seed)
  change hashTree mix seed s p = plainFold f g c t
  rw [← fold_sim h f g c]
  unfold hashTree
  congr 1
  · funext _ e
    cases hc : e.constant <;> simp [f, Entry.leaf, hc]
  · funext _ e
    simp [g]

end DynExpr.Arena
