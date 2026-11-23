import DynExpr.StringsParse.Roundtrip.Domain
import DynExpr.StringsParse.GeneralParse

/-! Package-parser half of the roundtrip: imaginary-unit normalization and the
grammar of the normalized syntax (`src/Parse.jl:219-599`). -/

namespace DynExpr.StringsParse.Roundtrip

open DynExpr.StringsParse.General

set_option maxHeartbeats 400000

/-! ## Table lookups -/

theorem find_zipIdx_key {β : Type} (key : β → String) (P : β → Bool) :
    ∀ (l : List β) (n j : Nat) (hj : j < l.length), (l.map key).Nodup →
      (∀ b ∈ l, P b = (key b == key l[j])) →
      (l.zipIdx n).find? (fun p => P p.1) = some (l[j], n + j) := by
  intro l
  induction l with
  | nil => intro n j hj; simp at hj
  | cons a l ih =>
    intro n j hj hnd hP
    have hnd' : (l.map key).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hnotin : key a ∉ l.map key := (List.nodup_cons.mp (by simpa using hnd)).1
    cases j with
    | zero =>
      have : P a = true := by rw [hP a (by simp)]; simp
      simp [List.zipIdx_cons, this]
    | succ j =>
      have hj' : j < l.length := by simpa using hj
      have hPa : P a = false := by
        rw [hP a (by simp)]
        simp only [List.getElem_cons_succ, beq_eq_false_iff_ne, ne_eq]
        intro h
        apply hnotin
        rw [h]
        exact List.mem_map.mpr ⟨l[j], List.getElem_mem hj', rfl⟩
      have hP' : ∀ b ∈ l, P b = (key b == key l[j]) := by
        intro b hb
        have := hP b (by simp [hb])
        simpa using this
      rw [List.zipIdx_cons, List.find?_cons]
      simp only [hPa]
      rw [ih (n + 1) j hj' hnd' hP']
      simp only [Option.some.injEq, Prod.mk.injEq, List.getElem_cons_succ, true_and]
      omega

/-- The table of a one-based degree. -/
def table (ops : Operators) (d : Nat) : List NamedOp := ops[d - 1]?.getD []

theorem cleanOps_table {ops : Operators} (h : CleanOps ops) (d : Nat) :
    (table ops d).length ≤ 255 ∧ ((table ops d).map NamedOp.name).Nodup ∧
      ∀ op ∈ table ops d, opNameOK op.name = true ∧ op.display = op.name ∧
        op.identity = op.name ∧ op.alias = op.name := by
  unfold table
  cases hd : ops[d - 1]? with
  | none => simp
  | some os =>
    have hm : os ∈ ops := List.mem_of_getElem? hd
    simpa using h.2 os hm

theorem opName_eq {ops : Operators} {d idx : Nat} (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    opName ops d idx = ((table ops d)[idx - 1]'(by omega)).name := by
  unfold opName
  have : (table ops d)[idx - 1]? = some ((table ops d)[idx - 1]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  unfold table at this
  simp only [this, Option.map_some, Option.getD_some]
  rfl

theorem findOpIndex_clean {ops : Operators} (h : CleanOps ops) {d idx : Nat}
    (hd : 0 < d) (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    findOpIndex ops (opName ops d idx) d = some idx := by
  obtain ⟨_, hnd, hall⟩ := cleanOps_table h d
  have hf := find_zipIdx_key NamedOp.name
    (fun op => op.identity == opName ops d idx || op.alias == opName ops d idx)
    (table ops d) 0 (idx - 1) (by omega) hnd (by
      intro b hb
      obtain ⟨_, _, hid, hal⟩ := hall b hb
      rw [hid, hal, opName_eq hi hl]
      simp)
  unfold findOpIndex
  have hz : d ≠ 0 := by omega
  unfold table at hf
  simp only [hz, ↓reduceIte, hf]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  omega

theorem filter_label (l : List NamedOp) (a d : Nat) :
    (l.map (fun op => (op.identity, a))).filter (fun p => p.2 == d) =
      if a = d then l.map (fun op => (op.identity, a)) else [] := by
  induction l with
  | nil => split <;> rfl
  | cons x l ih =>
    simp only [List.map_cons, List.filter_cons, ih]
    by_cases h : a = d <;> simp [h]

theorem filter_unique (key : NamedOp → String) (l : List NamedOp) (op : NamedOp) (hm : op ∈ l)
    (hnd : (l.map key).Nodup) :
    l.filter (fun o => key o == key op) = [op] := by
  induction l with
  | nil => simp at hm
  | cons x l ih =>
    have hnd' : (l.map key).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
    have hx : key x ∉ l.map key := (List.nodup_cons.mp (by simpa using hnd)).1
    rcases List.mem_cons.mp hm with rfl | hm'
    · have hnone : l.filter (fun o => key o == key op) = [] := by
        rw [List.filter_eq_nil_iff]
        intro o ho
        simp only [beq_iff_eq]
        intro heq
        exact hx (heq ▸ List.mem_map.mpr ⟨o, ho, rfl⟩)
      simp [hnone]
    · have hne : (key x == key op) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro heq
        exact hx (heq ▸ List.mem_map.mpr ⟨op, hm', rfl⟩)
      simp only [List.filter_cons, hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hm' hnd'

/-- An operator whose `_find_operator_by_name` spelling is unique in its degree
table resolves to its own identity at that degree (`src/Parse.jl:304-345`). -/
theorem findOperatorByName_mem {ops : Operators} {d : Nat} {op : NamedOp} (hd1 : 1 ≤ d)
    (hm : op ∈ table ops d) (hnd : ((table ops d).map NamedOp.parseName).Nodup) :
    findOperatorByName ops op.parseName d = .ok op.identity := by
  -- Only the table of arity `d` contributes labels equal to `d`.
  have key : ∀ (rest : List (List NamedOp)) (k : Nat),
      ((rest.zipIdx k).flatMap (fun (x : List NamedOp × Nat) =>
        (x.1.filter (fun o => o.parseName == op.parseName)).map (fun o => (o.identity, x.2 + 1)))).filter
          (fun p => p.2 == d) =
        (rest.zipIdx k).flatMap (fun (x : List NamedOp × Nat) =>
          if x.2 + 1 = d then
            (x.1.filter (fun o => o.parseName == op.parseName)).map (fun o => (o.identity, x.2 + 1))
          else []) := by
    intro rest
    induction rest with
    | nil => intro k; rfl
    | cons x rest ih =>
      intro k
      simp only [List.zipIdx_cons, List.flatMap_cons, List.filter_append, ih, filter_label]
  unfold findOperatorByName
  have hops : ∃ os, ops[d - 1]? = some os := by
    unfold table at hm
    cases hx : ops[d - 1]? with
    | none => rw [hx] at hm; simp at hm
    | some os => exact ⟨os, rfl⟩
  obtain ⟨os, hos⟩ := hops
  have htab : table ops d = os := by simp [table, hos]
  have hsplit : ops = ops.take (d - 1) ++ os :: ops.drop d := by
    have hlt : d - 1 < ops.length := (List.getElem?_eq_some_iff.mp hos).1
    have hget : ops[d - 1] = os := (List.getElem?_eq_some_iff.mp hos).2
    conv => lhs; rw [← List.take_append_drop (d - 1) ops]
    congr 1
    rw [List.drop_eq_getElem_cons hlt, hget, show d - 1 + 1 = d by omega]
  have hfilter : ((ops.zipIdx).flatMap (fun (x : List NamedOp × Nat) =>
        (x.1.filter (fun o => o.parseName == op.parseName)).map (fun o => (o.identity, x.2 + 1)))).filter
          (fun p => p.2 == d) = [(op.identity, d)] := by
    rw [key ops 0]
    rw [hsplit, List.zipIdx_append, List.flatMap_append, List.zipIdx_cons, List.flatMap_cons]
    have hlen' : (ops.take (d - 1)).length = d - 1 := by
      simp only [List.length_take]
      have hlt : d - 1 < ops.length := (List.getElem?_eq_some_iff.mp hos).1
      omega
    have htake : ∀ x ∈ (ops.take (d - 1)).zipIdx 0, x.2 + 1 ≠ d := by
      intro x hx
      have := List.snd_lt_of_mem_zipIdx hx
      rw [hlen'] at this
      omega
    have hdrop : ∀ x ∈ (ops.drop d).zipIdx (0 + (ops.take (d - 1)).length + 1), x.2 + 1 ≠ d := by
      intro x hx
      have := List.le_snd_of_mem_zipIdx hx
      rw [hlen'] at this
      omega
    rw [List.flatMap_eq_nil_iff.mpr (fun x hx => by simp [htake x hx]),
      List.flatMap_eq_nil_iff.mpr (fun x hx => by simp [hdrop x hx])]
    simp only [hlen', List.nil_append, List.append_nil, Nat.zero_add]
    have hd' : d - 1 + 1 = d := by omega
    simp only [hd', ↓reduceIte]
    rw [← htab, filter_unique NamedOp.parseName (table ops d) op hm hnd]
    simp
  simp only [hfilter]
  have hne : ((ops.zipIdx).flatMap (fun (x : List NamedOp × Nat) =>
      (x.1.filter (fun o => o.parseName == op.parseName)).map
        (fun o => (o.identity, x.2 + 1)))).isEmpty = false := by
    cases hz : ((ops.zipIdx).flatMap (fun (x : List NamedOp × Nat) =>
      (x.1.filter (fun o => o.parseName == op.parseName)).map (fun o => (o.identity, x.2 + 1)))) with
    | nil => rw [hz] at hfilter; simp at hfilter
    | cons _ _ => rfl
  simp only [hne, Bool.false_eq_true, ↓reduceIte]

/-- Clean operators are matched by their plain name, whether or not they are
broadcast callables, because their display equals that name. -/
theorem parseName_clean {op : NamedOp} (h : op.display = op.name) : op.parseName = op.name := by
  unfold NamedOp.parseName
  split
  · exact h
  · rfl

theorem findOperatorByName_clean {ops : Operators} (h : CleanOps ops) {d idx : Nat}
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    findOperatorByName ops (opName ops d idx) d = .ok (opName ops d idx) := by
  obtain ⟨_, hnd, hall⟩ := cleanOps_table h d
  have hm := List.getElem_mem (l := table ops d) (n := idx - 1) (by omega)
  have hname : opName ops d idx = ((table ops d)[idx - 1]'(by omega)).name := opName_eq hi hl
  generalize ((table ops d)[idx - 1]'(by omega)) = op at hm hname
  have hpn : ∀ o ∈ table ops d, o.parseName = o.name := fun o ho => parseName_clean (hall o ho).2.1
  have hnd' : ((table ops d).map NamedOp.parseName).Nodup := by
    rw [List.map_congr_left hpn]; exact hnd
  have hfound := findOperatorByName_mem hd1 hm hnd'
  rw [hpn op hm, (hall op hm).2.2.1] at hfound
  rw [hname]
  exact hfound

theorem resolved_clean {ops : Operators} (names : List String) (h : CleanOps ops) {d idx : Nat}
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2) (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    Resolved (pcfg ops names) (opName ops d idx) (opName ops d idx) d := by
  unfold Resolved
  split
  · rename_i id hb
    have hb' : (if ["+", "-", "*", "/", "^", "sin", "cos", "exp"].contains (opName ops d idx)
        then some (opName ops d idx) else none) = some id := hb
    split at hb'
    · cases hb'; rfl
    · cases hb'
  · exact findOperatorByName_clean h hd1 hd2 hi hl

theorem variableIndex_clean {names : List String} (hn : CleanNames names) {k : Nat}
    (h1 : 1 ≤ k) (h2 : k ≤ names.length) :
    variableIndex (names[k - 1]?.getD "") (some names) = some k := by
  have hj : k - 1 < names.length := by omega
  have hf := find_zipIdx_key id (fun s => s == names[k - 1]) names 0 (k - 1) hj
    (by simpa using hn.2.1) (by intro b _; rfl)
  unfold variableIndex
  rw [List.getElem?_eq_getElem hj, Option.getD_some]
  simp only [Option.bind_eq_bind, Option.bind_some, hf, Option.pure_def, Option.some.injEq]
  omega

/-! ## Grammar of expected trees -/

theorem nops_table (ops : Operators) (d : Nat) (hd : d ≠ 0) :
    ops.enum.nops d = (table ops d).length := by
  unfold OpEnum.nops Operators.enum table
  simp only [hd, ↓reduceIte, List.getElem?_map]
  cases ops[d - 1]? <;> simp

/-- Parser configuration requesting the node family `tag`. -/
def pcfgT (ops : Operators) (names : List String) (tag : String) : ParseConfig :=
  {operators := ops, names := some names, nodeType := tag}

/-- Every well-formed tree's surface syntax parses to that tree, in any
requested node family. -/
theorem toSurf_grammarT {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (tag : String) (u : Tree Scalar) (hw : u.WF 2 ops.enum.nops names.length) :
    ParseGrammar (pcfgT ops names tag) (toSurf ops names u) ⟨tag, u⟩ := by
  induction u using Tree.induction with
  | hc v => exact ParseGrammar.literal v
  | hf k =>
    simp only [Tree.WF] at hw
    exact ParseGrammar.symbol _ k (variableIndex_clean hn hw.1 hw.2.1)
  | hb idx cs ih =>
    simp only [Tree.WF] at hw
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw
    match cs, hl1, hl2, hi2, ih, hcs with
    | [c], _, _, hi2, ih, hcs =>
      have hl : idx ≤ (table ops 1).length := by
        rw [← nops_table ops 1 (by decide)]; exact hi2
      exact ParseGrammar.exact (opName ops 1 idx) (opName ops 1 idx) [toSurf ops names c]
        [⟨tag, c⟩] idx (resolved_clean names hops (by decide) (by decide) hi1 hl) rfl
        (findOpIndex_clean hops (by decide) hi1 hl)
        (.cons (ih c (by simp) (hcs c (by simp))) .nil)
    | [a, b], _, _, hi2, ih, hcs =>
      have hl : idx ≤ (table ops 2).length := by
        rw [← nops_table ops 2 (by decide)]; exact hi2
      exact ParseGrammar.exact (opName ops 2 idx) (opName ops 2 idx)
        [toSurf ops names a, toSurf ops names b]
        [⟨tag, a⟩, ⟨tag, b⟩] idx (resolved_clean names hops (by decide) (by decide) hi1 hl) rfl
        (findOpIndex_clean hops (by decide) hi1 hl)
        (.cons (ih a (by simp) (hcs a (by simp))) (.cons (ih b (by simp) (hcs b (by simp))) .nil))
    | [], h, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _ => simp at h

theorem toSurf_grammar {ops : Operators} {names : List String} (hops : CleanOps ops)
    (hn : CleanNames names) (u : Tree Scalar) (hw : u.WF 2 ops.enum.nops names.length) :
    ParseGrammar (pcfg ops names) (toSurf ops names u) ⟨"Node", u⟩ :=
  toSurf_grammarT hops hn "Node" u hw

theorem wf_branch1 {D : Nat} {nops : Nat → Nat} {nf idx : Nat} {c : Tree Scalar} (hD : 1 ≤ D)
    (hidx : 1 ≤ idx ∧ idx ≤ nops 1 ∧ idx ≤ 255) (hc : c.WF D nops nf) :
    (Tree.branch idx [c]).WF D nops nf := by
  simp only [Tree.WF]
  refine ⟨by simp; omega, hidx, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx; exact hc

theorem wf_branch2 {D : Nat} {nops : Nat → Nat} {nf idx : Nat} {a b : Tree Scalar} (hD : 2 ≤ D)
    (hidx : 1 ≤ idx ∧ idx ≤ nops 2 ∧ idx ≤ 255) (ha : a.WF D nops nf) (hb : b.WF D nops nf) :
    (Tree.branch idx [a, b]).WF D nops nf := by
  simp only [Tree.WF]
  refine ⟨by simp; omega, hidx, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> assumption

theorem wf_const {D : Nat} {nops : Nat → Nat} {nf : Nat} (v : Scalar) :
    (Tree.const v).WF D nops nf := by simp [Tree.WF]

/-- Expected trees stay well formed. -/
theorem expect_wf {ops : Operators} {names : List String} (t : Tree Scalar)
    (hw : t.WF 2 ops.enum.nops names.length) : (expect ops t).WF 2 ops.enum.nops names.length := by
  induction t using Tree.induction with
  | hc v => exact wf_const v
  | hf k => simpa [expect] using hw
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, hl3⟩, hidx, hcs⟩ := hw'
    match cs, hl1, hl2, ih, hcs, hidx with
    | [c], _, _, ih, hcs, hidx =>
      have hc := ih c (by simp) (hcs c (by simp))
      simp only [expect]
      unfold unaryFold
      split
      · split
        · exact wf_const _
        · split
          · exact wf_const _
          · exact wf_branch1 (by decide) hidx (wf_const _)
      · exact wf_branch1 (by decide) hidx hc
    | [a, b], _, _, ih, hcs, hidx =>
      have ha := ih a (by simp) (hcs a (by simp))
      have hb := ih b (by simp) (hcs b (by simp))
      simp only [expect]
      unfold binaryFold
      split
      · repeat' split
        all_goals first
          | exact wf_const _
          | exact wf_branch2 (by decide) hidx (wf_const _) (wf_const _)
      · repeat' split
        all_goals first
          | exact wf_const _
          | exact wf_branch2 (by decide) hidx (wf_const _) (wf_const _)
      · exact wf_branch2 (by decide) hidx ha hb
    | [], h, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _ => simp at h

end DynExpr.StringsParse.Roundtrip
