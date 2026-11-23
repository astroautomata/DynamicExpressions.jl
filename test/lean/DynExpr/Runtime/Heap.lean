import DynExpr.Runtime.Errors
import Lean.Elab.Tactic.Omega

namespace DynExpr

/-- Object identities for mutable nodes in src/Node.jl:74-86. -/
abbrev Addr := Nat

/-- Heap of mutable objects from src/Node.jl:74-86. Every address at or
above `next` is unallocated; cells below `next` may also be absent. -/
structure Heap (α : Type) where
  cells : Nat → Option α
  next : Nat
  fresh : ∀ a, next ≤ a → cells a = none

namespace Heap

/-- Initial state before allocations by constructors in src/Node.jl:86. -/
def empty : Heap α where
  cells := fun _ => none
  next := 0
  fresh := by intros; rfl

/-- Allocate a new mutable object, modelling `new` in src/Node.jl:86.
Existing object identities and contents remain unchanged. -/
def alloc (h : Heap α) (value : α) : Addr × Heap α :=
  (h.next, {
    cells := fun a => if a = h.next then some value else h.cells a
    next := h.next + 1
    fresh := by
      intro a ha
      have hne : a ≠ h.next := by omega
      have hle : h.next ≤ a := by omega
      simp [hne, h.fresh a hle]
  })

/-- Read a mutable object referenced by src/Node.jl:214. Missing
references fail as in src/Utils.jl:67. -/
def read (h : Heap α) (a : Addr) : Jl α :=
  match h.cells a with
  | none => .error .undefRefError
  | some value => .ok value

/-- Replace an allocated object, modelling mutation in src/Node.jl:472-488.
A missing object raises the reference error of src/Utils.jl:67. -/
def write (h : Heap α) (a : Addr) (value : α) : Jl (Heap α) :=
  if ha : h.cells a = none then .error .undefRefError
  else .ok {
    cells := fun b => if b = a then some value else h.cells b
    next := h.next
    fresh := by
      intro b hb
      have hne : b ≠ a := by
        intro hba
        subst b
        exact ha (h.fresh a hb)
      simp [hne, h.fresh b hb]
  }

/-- Every newly allocated address was absent, src/Node.jl:86. -/
theorem alloc_fresh (h : Heap α) (value : α) :
    h.cells (alloc h value).1 = none := by
  exact h.fresh h.next (Nat.le_refl _)

/-- Reading the newly allocated object returns its contents, src/Node.jl:86,214. -/
theorem read_alloc_same (h : Heap α) (value : α) :
    read (alloc h value).2 (alloc h value).1 = .ok value := by
  simp [alloc, read]

/-- Allocation preserves reads through all other identities, src/Node.jl:86,214. -/
theorem read_alloc_other (h : Heap α) (value : α) (b : Addr)
    (hne : b ≠ (alloc h value).1) :
    read (alloc h value).2 b = read h b := by
  have hb : b ≠ h.next := hne
  simp [alloc, read, hb]

/-- A successful write is visible through the same identity,
src/Node.jl:214,472-488. -/
theorem read_write_same (h h' : Heap α) (a : Addr) (value : α)
    (hw : write h a value = .ok h') : read h' a = .ok value := by
  unfold write at hw
  split at hw
  · cases hw
  · cases hw
    simp [read]

/-- A successful write preserves reads through other identities,
src/Node.jl:214,472-488. -/
theorem read_write_other (h h' : Heap α) (a b : Addr) (value : α)
    (hw : write h a value = .ok h') (hne : b ≠ a) :
    read h' b = read h b := by
  unfold write at hw
  split at hw
  · cases hw
  · cases hw
    simp [read, hne]

/-- Missing references fail on reading, src/Utils.jl:67. -/
theorem read_missing (h : Heap α) (a : Addr) (ha : h.cells a = none) :
    read h a = .error .undefRefError := by
  simp [read, ha]

/-- Missing references fail on writing, src/Utils.jl:67. -/
theorem write_missing (h : Heap α) (a : Addr) (value : α)
    (ha : h.cells a = none) :
    write h a value = .error .undefRefError := by
  simp [write, ha]

end Heap
end DynExpr
