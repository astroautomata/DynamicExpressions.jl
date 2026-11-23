import DynExpr.StringsParse.Roundtrip.Main

/-! Float32 constants print exactly like Float64 constants
(`src/Strings.jl:81-93` with the `realText` mirror), so a tree renders as its
Float64 demotion. -/

namespace DynExpr.StringsParse.Roundtrip

/-- The Float64 scalar of the same value as a Float32 scalar. -/
def demoteScalar : Scalar → Scalar
  | .float32 v => .real v
  | v => v

/-- Replace every Float32 constant by the Float64 constant of the same value. -/
def demote : Tree Scalar → Tree Scalar
  | .const v => .const (demoteScalar v)
  | .feature k => .feature k
  | .branch idx cs => .branch idx (cs.map demote)

theorem rawForest_demote (cfg : RenderConfig) :
    ∀ cs : List (Tree Scalar), (∀ c ∈ cs, rawTree cfg (demote c) = rawTree cfg c) →
      rawForest cfg (cs.map demote) = rawForest cfg cs := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    simp only [List.map_cons, rawForest, h c (by simp), ih (fun d hd => h d (by simp [hd]))]

theorem rawTree_demote (ops : Operators) (names : List String) (t : Tree Scalar) :
    rawTree (rcfg ops names) (demote t) = rawTree (rcfg ops names) t := by
  induction t using Tree.induction with
  | hc v =>
    simp only [demote, rawTree]
    cases v <;> rfl
  | hf k => simp only [demote]
  | hb idx cs ih =>
    simp only [demote, rawTree, List.length_map, rawForest_demote _ cs ih]

theorem stringTree_demote (ops : Operators) (names : List String) (t : Tree Scalar) :
    stringTree (rcfg ops names) (demote t) = stringTree (rcfg ops names) t := by
  have := rawTree_demote ops names t
  simp only [rcfg] at this
  unfold stringTree
  simp only [rcfg, resolveNames, bind, Except.bind, this]

theorem wf_demote {D : Nat} {nops : Nat → Nat} {nf : Nat} (t : Tree Scalar) (h : t.WF D nops nf) :
    (demote t).WF D nops nf := by
  induction t using Tree.induction with
  | hc v => simp [demote, Tree.WF]
  | hf k => simpa [demote] using h
  | hb idx cs ih =>
    simp only [Tree.WF] at h
    simp only [demote, Tree.WF, List.length_map]
    refine ⟨h.1, h.2.1, ?_⟩
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact ih d hd (h.2.2 d hd)

end DynExpr.StringsParse.Roundtrip
