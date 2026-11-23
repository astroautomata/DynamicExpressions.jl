import DynExpr.Arena.Traversal

namespace DynExpr.Arena

/-- On the bulk-copy path, storage (and therefore every active child index) is
preserved and the new vector reserves edit headroom. -/
def compact_copy : Prop := ∀ (s : Store Nat) (p : Handle) (d : Nat) (bs : Bool),
  compactRoot s p.idx = true → ∃ dest,
    copyNode s d p.idx bs = .ok (dest, p.idx) ∧
    compactRoot dest p.idx = true ∧ dest.nodes = s.nodes ∧
    dest.capacity = s.nodes.size + d + 1

theorem compact_copy_holds : compact_copy := by
  intro s p d bs h
  have hroot : p.idx.toInt = (s.nodes.size : Int) := by
    simp [compactRoot] at h
    exact h.2
  have hn : s.nodes.size ≤ editHeadroom s.nodes.size d := by
    unfold editHeadroom
    omega
  refine ⟨copyEntries { capacity := editHeadroom s.nodes.size d } s, ?_, ?_, rfl, ?_⟩
  · simp [copyNode, h, pure, Except.pure]
  · simp [compactRoot, copyEntries, hroot]
  · simp only [copyEntries, reserve, Store.capacity, if_pos hn]
    rfl

/-- Every successful preallocation copy returns a compact-marked store and
reports the number of entries in that store. -/
def copy_into_metadata : Prop := ∀ (s dest dest' : Store Nat) (d : Nat) (i j : Int32)
    (same : Bool) (n : Nat),
  copyInto dest s d i same = .ok (dest', j, n) → dest'.compact = true ∧ n = dest'.nodes.size

theorem copy_into_metadata_holds : copy_into_metadata := by
  intro s dest dest' d i j same n h
  unfold copyInto at h
  cases hs : same <;> cases hc : compactRoot s i
  · simp [hs, hc, pure, Except.pure, bind, Except.bind] at h
    cases ha : appendSubtree { dest with nodes := #[] } s d i with
    | error err => simp [ha] at h
    | ok result =>
      obtain ⟨out, idx⟩ := result
      simp [ha] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  · simp [hs, hc, pure, Except.pure, bind, Except.bind] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · simp [hs, hc, pure, Except.pure, bind, Except.bind] at h
    cases hs' : copyNode s d i with
    | error err => simp [hs'] at h
    | ok result =>
      obtain ⟨src, idx⟩ := result
      simp only [hs'] at h
      cases hroot : compactRoot src idx
      · simp [hroot] at h
        cases ha : appendSubtree { dest with nodes := #[] } src d idx with
        | error err => simp [ha] at h
        | ok result =>
          obtain ⟨out, idx⟩ := result
          simp [ha] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl⟩
      · simp [hroot] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
  · simp [hs, hc, pure, Except.pure] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [compactRoot] at hc
    exact ⟨hc.1, rfl⟩

example : ∃ (s : Store Nat), compactRoot s 1 = true ∧
    copyInto s s 2 1 true = .ok (s, 1, 1) :=
  ⟨{ nodes := #[some ⟨1, zeros 2, 0, 0, 0, true⟩] }, rfl, rfl⟩

end DynExpr.Arena
