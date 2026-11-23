import DynExpr.NoAlias.Ctor

/-!
Composition of node construction steps (`src/Node.jl:350-430`): building
several subtrees one after another from pairwise disjoint input trees yields
pairwise disjoint alias-free results, so a constructor applied to them yields
an alias-free tree. Used by the generated operators, the parser and the
expression operators.
-/

namespace DynExpr.NoAlias
open DynExpr Graph NodeBase

variable {T : Type}

/-- Input trees are pairwise disjoint across two lists. -/
def CrossDisj (g : Graph T) (l l' : List Addr) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l', Disjoint g a b

theorem closed_reach {g : Graph T} {a x : Addr} (h : Closed g a) (hx : Reachable g a x) :
    Closed g x := fun z hz => h z (reach_trans hx hz)

theorem reach_ext {g g' : SGraph T} {a x : Addr} (he : Ext g g') (hc : Closed g.view a) :
    Reachable g'.view a x ↔ Reachable g.view a x := reach_transfer (sameKidsOn_ext he hc)

theorem trees_ext {g g' : SGraph T} {l : List Addr} (he : Ext g g') (h : Trees g.view l) :
    Trees g'.view l := fun b hb =>
  ⟨noAlias_transfer (sameKidsOn_ext he (h b hb).2) (h b hb).1,
   closed_transfer (sameKidsOn_ext he (h b hb).2) (h b hb).2⟩

theorem pairDisj_ext {g g' : SGraph T} {l : List Addr} (he : Ext g g') (ht : Trees g.view l)
    (h : PairDisj g.view l) : PairDisj g'.view l :=
  ⟨h.1, fun b hb b' hb' hne => disjoint_transfer (sameKidsOn_ext he (ht b hb).2)
    (sameKidsOn_ext he (ht b' hb').2) (h.2 b hb b' hb' hne)⟩

theorem built_mono {g g' : SGraph T} {ins ins' : List Addr} {r : Addr}
    (hsub : ∀ a ∈ ins, a ∈ ins') (h : Built g g' ins r) : Built g g' ins' r :=
  ⟨h.ext, h.noAlias, h.closed, fun x hx => by
    rcases h.reach x hx with h1 | ⟨a, ha, hax⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a, hsub a ha, hax⟩⟩

/-- Returning an existing input tree unchanged (e.g. `parse_leaf` passing a
pre-built node through, `src/Parse.jl:602-603`). -/
theorem built_input {g : SGraph T} {a : Addr} (h : Trees g.view [a]) : Built g g [a] a :=
  ⟨ext_refl g, (h a (by simp)).1, (h a (by simp)).2, fun x hx => Or.inr ⟨a, by simp, hx⟩⟩

/-- Invariant of a left-to-right sequence of builds started at `g0`: the
results so far are alias-free, closed and pairwise disjoint, and consist of
new objects and objects of the inputs consumed so far. -/
structure Inv (g0 h : SGraph T) (ins rs : List Addr) : Prop where
  ext : Ext g0 h
  trees : Trees h.view rs
  disj : PairDisj h.view rs
  within : ∀ r ∈ rs, ∀ x, Reachable h.view r x → g0.next ≤ x ∨ ∃ a ∈ ins, Reachable g0.view a x

theorem inv_nil (g0 : SGraph T) : Inv g0 g0 [] [] :=
  ⟨ext_refl g0, trees_nil _, pairDisj_nil _, fun _ h => absurd h List.not_mem_nil⟩

theorem inv_step {g0 h h' : SGraph T} {ins ins' rs : List Addr} {r : Addr}
    (hi : Inv g0 h ins rs) (hb : Built h h' ins' r) (ht : Trees g0.view ins')
    (hcross : CrossDisj g0.view ins ins') : Inv g0 h' (ins ++ ins') (rs ++ [r]) := by
  have he' := hb.ext
  -- inputs of the new step read the same in `h` as in `g0`
  have hin : ∀ b ∈ ins', ∀ x, Reachable h.view b x → Reachable g0.view b x ∧ x < g0.next := by
    intro b hb' x hx
    have hx0 := (reach_ext hi.ext (ht b hb').2).mp hx
    exact ⟨hx0, closed_lt (ht b hb').2 hx0⟩
  -- the new result consists of objects at or above `h.next` and old input objects
  have hr : ∀ x, Reachable h'.view r x → h.next ≤ x ∨ ∃ b ∈ ins', Reachable g0.view b x ∧ x < g0.next := by
    intro x hx
    rcases hb.reach x hx with h1 | ⟨b, hb', hbx⟩
    · exact Or.inl h1
    · exact Or.inr ⟨b, hb', hin b hb' x hbx⟩
  have hold : ∀ r' ∈ rs, ∀ x, Reachable h'.view r' x ↔ Reachable h.view r' x :=
    fun r' hr' x => reach_ext he' (hi.trees r' hr').2
  have hdis : ∀ r' ∈ rs, Disjoint h'.view r' r := by
    intro r' hr' x h1 h2
    have h1' := (hold r' hr' x).mp h1
    have hlt := closed_lt (hi.trees r' hr').2 h1'
    rcases hr x h2 with h3 | ⟨b, hb', hbx, hx0⟩
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt h3)
    · rcases hi.within r' hr' x h1' with h4 | ⟨a, ha, hax⟩
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hx0 h4)
      · exact hcross a ha b hb' x hax hbx
  refine ⟨ext_trans hi.ext he', ?_, ?_, ?_⟩
  · intro b hb'
    rcases List.mem_append.mp hb' with hm | hm
    · exact trees_ext he' hi.trees b hm
    · simp at hm; subst hm; exact ⟨hb.noAlias, hb.closed⟩
  · refine ⟨?_, ?_⟩
    · refine List.nodup_append.mpr ⟨hi.disj.1, (by simp), ?_⟩
      intro a ha b hbm hab
      simp at hbm; subst hbm; subst hab
      exact disjoint_ne (hdis a ha) rfl
    · intro a ha b hbm hne
      rcases List.mem_append.mp ha with ha1 | ha2 <;> rcases List.mem_append.mp hbm with hb1 | hb2
      · exact (pairDisj_ext he' hi.trees hi.disj).2 a ha1 b hb1 hne
      · have : b = r := by simpa using hb2
        rw [this]; exact hdis a ha1
      · have : a = r := by simpa using ha2
        rw [this]; exact disjoint_symm (hdis b hb1)
      · have h1 : a = r := by simpa using ha2
        have h2 : b = r := by simpa using hb2
        exact absurd (h1.trans h2.symm) hne
  · intro r' hr' x hx
    rcases List.mem_append.mp hr' with hm | hm
    · rcases hi.within r' hm x ((hold r' hm x).mp hx) with h1 | ⟨a, ha, hax⟩
      · exact Or.inl h1
      · exact Or.inr ⟨a, List.mem_append_left _ ha, hax⟩
    · simp at hm; subst hm
      rcases hr x hx with h1 | ⟨b, hb', hbx, _⟩
      · exact Or.inl (Nat.le_trans hi.ext.1 h1)
      · exact Or.inr ⟨b, List.mem_append_right _ hb', hbx⟩

/-- A final build over the sequence results is a build over all inputs. -/
theorem built_of_inv {g0 h h' : SGraph T} {ins rs : List Addr} {n : Addr}
    (hi : Inv g0 h ins rs) (hb : Built h h' rs n) : Built g0 h' ins n := by
  refine ⟨ext_trans hi.ext hb.ext, hb.noAlias, hb.closed, fun x hx => ?_⟩
  rcases hb.reach x hx with h1 | ⟨r, hr, hrx⟩
  · exact Or.inl (Nat.le_trans hi.ext.1 h1)
  · exact hi.within r hr x hrx

/-- A constructor over the sequence results. -/
theorem built_ctor_inv {g0 h h' : SGraph T} {ins rs : List Addr} {n : Addr} {D : Nat}
    {hasD : Bool} {kw : Kw T} (hi : Inv g0 h ins rs) (hk : ctorKids kw = rs)
    (hc : ctor h D hasD kw = .ok (n, h')) : Built g0 h' ins n := by
  have := (ctor_built (hk ▸ hi.trees) (hk ▸ hi.disj) hc).2
  rw [hk] at this
  exact built_of_inv hi this

/-- Inputs of a list are trees and pairwise disjoint; splitting helpers. -/
theorem trees_append {g : Graph T} {l l' : List Addr} :
    Trees g (l ++ l') ↔ Trees g l ∧ Trees g l' := by
  constructor
  · intro h; exact ⟨fun b hb => h b (List.mem_append_left _ hb), fun b hb => h b (List.mem_append_right _ hb)⟩
  · intro ⟨h1, h2⟩ b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact h1 b hb
    · exact h2 b hb

theorem pairDisj_append {g : Graph T} {l l' : List Addr} (h : PairDisj g (l ++ l')) :
    PairDisj g l ∧ PairDisj g l' ∧ CrossDisj g l l' := by
  obtain ⟨hnd, hd⟩ := h
  obtain ⟨hnd1, hnd2, hne⟩ := List.nodup_append.mp hnd
  refine ⟨⟨hnd1, fun a ha b hb => hd a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)⟩,
    ⟨hnd2, fun a ha b hb => hd a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)⟩, ?_⟩
  intro a ha b hb
  exact hd a (List.mem_append_left _ ha) b (List.mem_append_right _ hb) (hne a ha b hb)

end DynExpr.NoAlias
