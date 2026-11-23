import DynExpr.StringsParse.Roundtrip.Render
import DynExpr.StringsParse.Roundtrip.Normalize

/-! Assembly of the character-level serialization roundtrip. -/

namespace DynExpr.StringsParse.Roundtrip

open DynExpr.StringsParse.General

set_option maxHeartbeats 400000

theorem surfaceDepth_pos (s : Surface) : 1 ≤ surfaceDepth s := by
  cases s <;> simp [surfaceDepth]

theorem depth_le {ops : Operators} {names : List String} (t : Tree Scalar)
    (ha : Admissible ops names t) :
    surfaceDepth (toSurf ops names (expect ops t)) ≤ surfaceDepth (surf ops names t) := by
  induction t using Tree.induction with
  | hc v =>
    match v with
    | .complex (.fin r) (.fin i) => simp [expect, toSurf, surf, surfaceDepth]
    | .real _ => simp [expect, toSurf, surf]
    | .float32 _ => simp [expect, toSurf, surf]
    | .complex .nan _ => simp [expect, toSurf, surf]
    | .complex .posInf _ => simp [expect, toSurf, surf]
    | .complex .negInf _ => simp [expect, toSurf, surf]
    | .complex (.fin _) .nan => simp [expect, toSurf, surf]
    | .complex (.fin _) .posInf => simp [expect, toSurf, surf]
    | .complex (.fin _) .negInf => simp [expect, toSurf, surf]
  | hf k => simp [expect, toSurf, surf]
  | hb idx cs ih =>
    simp only [Admissible] at ha
    match cs, ih, ha with
    | [c], ih, ha =>
      have hc := ih c (by simp) (ha c (by simp))
      obtain ⟨l1, l2⟩ := surf_literal (ops := ops) (names := names) c (ha c (by simp))
      simp only [expect, surf]
      unfold unaryFold
      split
      · rename_i v hv
        have hs := l2 v hv
        simp only [hs]
        split <;> (try split) <;> simp_all [toSurf, surfaceDepth, argsDepth]
      · rename_i hnot
        split
        · split
          · rename_i w hw'
            obtain ⟨x, rfl, hx⟩ := l1 w hw'
            exact absurd hx (hnot x)
          · simp only [toSurf, surfaceDepth, argsDepth] at *; omega
        · simp only [toSurf, surfaceDepth, argsDepth] at *; omega
    | [a, b], ih, ha' =>
      have ha := ih a (by simp) (ha' a (by simp))
      have hb := ih b (by simp) (ha' b (by simp))
      have pa := surfaceDepth_pos (surf ops names a)
      have pb := surfaceDepth_pos (surf ops names b)
      simp only [expect, surf]
      unfold binaryFold
      split
      · repeat' split
        all_goals simp only [toSurf, surfaceDepth, argsDepth] at *; omega
      · repeat' split
        all_goals simp only [toSurf, surfaceDepth, argsDepth] at *; omega
      · simp only [toSurf, surfaceDepth, argsDepth] at *; omega
    | [], _, _ => simp [expect, toSurf, surf]
    | _ :: _ :: _ :: _, _, _ => simp [expect, toSurf, surf]

/-- The full roundtrip: rendering succeeds and reparsing, in any requested node
family, gives the expected tree of the rotated tree, for arbitrary operator
semantics. -/
theorem roundtripRotT {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (tag : String) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) :
    ∃ text, stringTree (rcfg ops names) t = .ok text ∧
      parseString (pcfgT ops names tag) text = .ok ⟨tag, expect ops (rotT ops t)⟩ := by
  obtain ⟨⟨s, s', hraw, hstrip, _, _, _, _, hlex⟩⟩ := renderFacts hops hn t hw ha
  have hwr := rotT_wf ops t hw
  have har := rotT_admissible ops names t ha
  refine ⟨s', ?_, ?_⟩
  · simp only [stringTree, resolveNames, bind, Except.bind, pure, Except.pure]
    show (do let x ← rawTree (rcfg ops names) t; stripBrackets x) = _
    rw [hraw]
    exact hstrip
  · have hl := hlex [] [] (by intro x hx; simp at hx) lexOK_nil
    simp only [List.append_nil] at hl
    have hlexed : lex (s'.length + 1) s'.toList = bare ops names t :=
      hl _ (by rw [String.length_toList]; omega)
    have hfuel : (bare ops names t).length ≤ s'.length + 1 := by
      rw [← hlexed]; exact lex_length _ _
    have hmeta : metaParse s' = .ok (surf ops names (rotT ops t)) := by
      unfold metaParse
      rw [hlexed]
      exact (parse_toks hops hn t hw ha).1 _ hfuel
    unfold parseString
    rw [hmeta]
    show parseExpression (pcfgT ops names tag) (surf ops names (rotT ops t)) = _
    unfold parseExpression
    have hnorm : normalize (pcfgT ops names tag).names (surf ops names (rotT ops t)) =
        toSurf ops names (expect ops (rotT ops t)) := normalize_surf hn _ hwr har
    rw [hnorm]
    have htv : TableValid (pcfgT ops names tag).operators := by
      intro os hos; exact (hops.2 os hos).1
    exact grammarSuccess.1 (pcfgT ops names tag) _ ⟨tag, expect ops (rotT ops t)⟩ _ htv
      (toSurf_grammarT hops hn tag _ (expect_wf _ hwr))
      (by have := depth_le (ops := ops) (names := names) _ har; omega)

/-- Without unary `+` power bases the reparsed tree is the expected tree. -/
theorem roundtripT {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (tag : String) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) (hp : NoPlusBase ops t) :
    ∃ text, stringTree (rcfg ops names) t = .ok text ∧
      parseString (pcfgT ops names tag) text = .ok ⟨tag, expect ops t⟩ := by
  obtain ⟨text, hs, hparse⟩ := roundtripRotT hops hn tag t hw ha
  rw [rotT_id ops t hp] at hparse
  exact ⟨text, hs, hparse⟩

theorem roundtrip {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) (hp : NoPlusBase ops t) :
    ∃ text, stringTree (rcfg ops names) t = .ok text ∧
      parseString (pcfg ops names) text = .ok ⟨"Node", expect ops t⟩ :=
  roundtripT hops hn "Node" t hw ha hp

/-- Fold-free trees reparse to themselves. -/
theorem expect_foldFree {ops : Operators} (t : Tree Scalar) (h : FoldFree ops t) :
    expect ops t = t := by
  induction t using Tree.induction with
  | hc v =>
    match v, h with
    | .complex _ _, h => simp [FoldFree] at h
    | .real _, _ => rfl
    | .float32 _, _ => rfl
  | hf k => rfl
  | hb idx cs ih =>
    simp only [FoldFree] at h
    match cs, ih, h with
    | [c], ih, h =>
      have hc := ih c (by simp) (h.2 c (by simp))
      simp only [expect, hc]
      unfold unaryFold
      split
      · rename_i _ v
        by_cases hm : ["-", "+"].contains (opName ops 1 idx) = true
        · exact absurd rfl (h.1 _ rfl hm _)
        · have h1 : (opName ops 1 idx == "-") = false := by
            cases hq : (opName ops 1 idx == "-")
            · rfl
            · exfalso; apply hm; simp at hq; simp [hq]
          have h2 : (opName ops 1 idx == "+") = false := by
            cases hq : (opName ops 1 idx == "+")
            · rfl
            · exfalso; apply hm; simp at hq; simp [hq]
          simp [h1, h2]
      · rfl
    | [a, b], ih, h =>
      have ha := ih a (by simp) (h.2 a (by simp))
      have hb := ih b (by simp) (h.2 b (by simp))
      have hfb := h.2 b (by simp)
      have hfa := h.2 a (by simp)
      simp only [expect, ha, hb]
      unfold binaryFold
      split
      · simp [FoldFree] at hfb
      · simp [FoldFree] at hfa
      · rfl
    | [], _, _ => rfl
    | _ :: _ :: _ :: _, _, _ => rfl

theorem lookup_eq (ops : Operators) {d idx : Nat} (hd : d ≠ 0) (hi : idx ≠ 0) :
    ops.enum.lookup d idx = ((table ops d)[idx - 1]?).map NamedOp.apply := by
  unfold OpEnum.lookup Operators.enum table
  simp only [hd, hi, or_self, ↓reduceIte, List.getElem?_map]
  cases ops[d - 1]? <;> simp

theorem lookup_unary {ops : Operators} {idx : Nat} (hi : 1 ≤ idx) (hl : idx ≤ (table ops 1).length) :
    ops.enum.lookup 1 idx = some ((table ops 1)[idx - 1]'(by omega)).apply := by
  rw [lookup_eq ops (by decide) (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem lookup_binary {ops : Operators} {idx : Nat} (hi : 1 ≤ idx) (hl : idx ≤ (table ops 2).length) :
    ops.enum.lookup 2 idx = some ((table ops 2)[idx - 1]'(by omega)).apply := by
  rw [lookup_eq ops (by decide) (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

/-- Constants of expected trees are finite. -/
def FiniteConsts : Tree Scalar → Prop
  | .const (.real (.fin _)) => True
  | .const (.complex (.fin _) (.fin _)) => True
  | .const _ => False
  | .feature _ => True
  | .branch _ cs => ∀ c ∈ cs, FiniteConsts c

/-- Under the standard meaning of the folded operators, the expected tree
denotes the same value as the original tree. -/
theorem expect_denote {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hstd : StdFold ops) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (ha : Admissible ops names t) (x : Nat → Option Scalar) :
    (expect ops t).denote ops.enum x = t.denote ops.enum x := by
  induction t using Tree.induction with
  | hc v => rfl
  | hf k => rfl
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have ha' := ha
    simp only [Admissible] at ha'
    match cs, hl1, hl2, hi2, ih, hcs, ha' with
    | [c], _, _, hi2, ih, hcs, ha' =>
      simp only [List.length_singleton] at hi2
      have hc := ih c (by simp) (hcs c (by simp)) (ha' c (by simp))
      have hl := table_len (ops := ops) (d := 1) (by decide) hi2
      have hlk := lookup_unary hi1 hl
      have hmem : (table ops 1)[idx - 1]'(by omega) ∈ ops[0]?.getD [] := by
        have := List.getElem_mem (l := table ops 1) (n := idx - 1) (by omega)
        simpa [table] using this
      have hname : opName ops 1 idx = ((table ops 1)[idx - 1]'(by omega)).name := opName_eq hi1 hl
      generalize ((table ops 1)[idx - 1]'(by omega)) = op at hlk hmem hname
      simp only [expect]
      unfold unaryFold
      split
      · rename_i v hv
        have hfin := expect_const_finite c (ha' c (by simp)) _ hv
        obtain ⟨q, rfl⟩ : ∃ q, v = .fin q := by
          rcases hfin with ⟨q, hq⟩ | ⟨_, _, hq⟩
          · cases hq; exact ⟨q, rfl⟩
          · cases hq
        have hcd : c.denote ops.enum x = some (.real (.fin q)) := by rw [← hc, hv]; simp [Tree.denote]
        have htd : (Tree.branch idx [c]).denote ops.enum x = some (op.apply [.real (.fin q)]) := by
          simp [Tree.denote, hlk, hcd]
        split
        · rename_i hm
          rw [htd, (hstd.1 op hmem (by rw [← hname]; simpa using hm) q)]
          simp only [Tree.denote] <;> rfl
        · split
          · rename_i _ hp
            rw [htd, (hstd.2.1 op hmem (by rw [← hname]; simpa using hp) q)]
            simp only [Tree.denote] <;> rfl
          · rw [htd]
            simp [Tree.denote, hlk]
      · simp only [Tree.denote, List.mapM_cons, List.mapM_nil, hc, List.length_cons, List.length_nil]
    | [a, b], _, _, hi2, ih, hcs, ha' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      have hia := ih a (by simp) (hcs a (by simp)) (ha' a (by simp))
      have hib := ih b (by simp) (hcs b (by simp)) (ha' b (by simp))
      have hl := table_len (ops := ops) (d := 2) (by decide) hi2
      have hlk := lookup_binary hi1 hl
      have hmem : (table ops 2)[idx - 1]'(by omega) ∈ ops[1]?.getD [] := by
        have := List.getElem_mem (l := table ops 2) (n := idx - 1) (by omega)
        simpa [table] using this
      have hname : opName ops 2 idx = ((table ops 2)[idx - 1]'(by omega)).name := opName_eq hi1 hl
      generalize ((table ops 2)[idx - 1]'(by omega)) = op at hlk hmem hname
      have htd : ∀ va vb, a.denote ops.enum x = some va → b.denote ops.enum x = some vb →
          (Tree.branch idx [a, b]).denote ops.enum x = some (op.apply [va, vb]) := by
        intro va vb h1 h2
        simp [Tree.denote, hlk, h1, h2]
      have hfa := expect_const_finite a (ha' a (by simp))
      have hfb := expect_const_finite b (ha' b (by simp))
      simp only [expect]
      unfold binaryFold
      split
      next y z hy hz =>
        obtain ⟨q, rfl⟩ : ∃ q, y = .fin q := by
          rcases hfa _ hy with ⟨q, hq⟩ | ⟨_, _, hq⟩
          · cases hq; exact ⟨q, rfl⟩
          · cases hq
        obtain ⟨w, rfl⟩ : ∃ w, z = .fin w := by
          rcases hfb _ hz with ⟨_, hq⟩ | ⟨_, w, hq⟩
          · cases hq
          · cases hq; exact ⟨w, rfl⟩
        have h1 : a.denote ops.enum x = some (.real (.fin q)) := by rw [← hia, hy]; simp [Tree.denote]
        have h2 : b.denote ops.enum x = some (.complex (.fin 0) (.fin w)) := by rw [← hib, hz]; simp [Tree.denote]
        rw [htd _ _ h1 h2]
        split
        · rename_i hp
          rw [(hstd.2.2.1 op hmem (by rw [← hname]; simpa using hp) q w).1]; simp only [Tree.denote] <;> rfl
        · split
          · rename_i _ hm
            rw [hstd.2.2.2.1 op hmem (by rw [← hname]; simpa using hm) q w]; simp only [Tree.denote] <;> rfl
          · split
            · rename_i _ _ hs
              rw [(hstd.2.2.2.2 op hmem (by rw [← hname]; simpa using hs) q w).1]; simp only [Tree.denote] <;> rfl
            · simp [Tree.denote, hlk, h1, h2]
      next y z hy hz =>
        obtain ⟨w, rfl⟩ : ∃ w, y = .fin w := by
          rcases hfa _ hy with ⟨_, hq⟩ | ⟨_, w, hq⟩
          · cases hq
          · cases hq; exact ⟨w, rfl⟩
        obtain ⟨q, rfl⟩ : ∃ q, z = .fin q := by
          rcases hfb _ hz with ⟨q, hq⟩ | ⟨_, _, hq⟩
          · cases hq; exact ⟨q, rfl⟩
          · cases hq
        have h1 : a.denote ops.enum x = some (.complex (.fin 0) (.fin w)) := by rw [← hia, hy]; simp [Tree.denote]
        have h2 : b.denote ops.enum x = some (.real (.fin q)) := by rw [← hib, hz]; simp [Tree.denote]
        rw [htd _ _ h1 h2]
        split
        · rename_i hp
          rw [(hstd.2.2.1 op hmem (by rw [← hname]; simpa using hp) w q).2]; simp only [Tree.denote] <;> rfl
        · split
          · rename_i _ hs
            rw [(hstd.2.2.2.2 op hmem (by rw [← hname]; simpa using hs) w q).2]; simp only [Tree.denote] <;> rfl
          · simp [Tree.denote, hlk, h1, h2]
      next =>
        simp only [Tree.denote, List.mapM_cons, List.mapM_nil, hia, hib, List.length_cons,
          List.length_nil]
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

/-- When unary `+` operators are the identity, rotation preserves the value. -/
theorem rotT_denote {ops : Operators} {names : List String} (hplus : PlusIdentity ops)
    (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length) (x : Nat → Option Scalar) :
    (rotT ops t).denote ops.enum x = t.denote ops.enum x := by
  have hbin : ∀ idx (a1 b1 a2 b2 : Tree Scalar), a1.denote ops.enum x = a2.denote ops.enum x →
      b1.denote ops.enum x = b2.denote ops.enum x →
      (Tree.branch idx [a1, b1]).denote ops.enum x = (Tree.branch idx [a2, b2]).denote ops.enum x := by
    intro idx a1 b1 a2 b2 h1 h2
    simp only [Tree.denote, List.mapM_cons, List.mapM_nil, h1, h2, List.length_cons, List.length_nil]
  induction t using Tree.induction with
  | hc v => rfl
  | hf k => rfl
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, _, hcs⟩ := hw'
    match cs, hl1, hl2, ih, hcs with
    | [c], _, _, ih, hcs =>
      rw [rotT_unary]
      simp only [Tree.denote, List.mapM_cons, List.mapM_nil, ih c (by simp) (hcs c (by simp)),
        List.length_cons, List.length_nil]
    | [a, b], _, _, ih, hcs =>
      by_cases hr : opName ops 2 idx = "^" ∧ PlusLed ops a = true
      · obtain ⟨pidx, c, rfl, hp⟩ := plusLed_shape hr.2
        rw [rotT_plus ops hr.1 hp]
        have hwa := hcs (.branch pidx [c]) (by simp)
        have hia := ih (.branch pidx [c]) (by simp) hwa
        rw [rotT_unary] at hia
        have hib := ih b (by simp) (hcs b (by simp))
        simp only [Tree.WF] at hwa
        obtain ⟨_, ⟨hp1, hp2, _⟩, _⟩ := hwa
        simp only [List.length_singleton] at hp2
        have hl := table_len (ops := ops) (d := 1) (by decide) hp2
        have hlk := lookup_unary hp1 hl
        have hmem : (table ops 1)[pidx - 1]'(by omega) ∈ ops[0]?.getD [] := by
          have := List.getElem_mem (l := table ops 1) (n := pidx - 1) (by omega)
          simpa [table] using this
        have hname : opName ops 1 pidx = ((table ops 1)[pidx - 1]'(by omega)).name :=
          opName_eq hp1 hl
        generalize ((table ops 1)[pidx - 1]'(by omega)) = op at hlk hmem hname
        have hid : ∀ v, op.apply [v] = v := hplus op hmem (by rw [← hname]; exact hp)
        have hun : ∀ y : Tree Scalar,
            (Tree.branch pidx [y]).denote ops.enum x = y.denote ops.enum x := by
          intro y
          simp only [Tree.denote, List.mapM_cons, List.mapM_nil, List.length_singleton, hlk]
          cases y.denote ops.enum x <;> simp [hid]
        rw [hun, hun] at hia
        rw [hun]
        exact hbin idx _ _ _ _ (hia.trans (hun c).symm) hib
      · rw [rotT_pair ops hr]
        exact hbin idx _ _ _ _ (ih a (by simp) (hcs a (by simp))) (ih b (by simp) (hcs b (by simp)))
    | [], h, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _ => simp at h

end DynExpr.StringsParse.Roundtrip
