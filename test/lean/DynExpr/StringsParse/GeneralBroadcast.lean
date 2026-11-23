import DynExpr.StringsParse.GeneralRoundtrip
import DynExpr.StringsParse.GeneralDomain

/-! Reparsing of printed broadcast calls (`src/Strings.jl:53-133`,
`src/Parse.jl:298-421`). `string_tree` prints an identifier-named broadcast
callable `f.` applied to its operands as `f.(a, b)`. `Meta.parse` reads this as
`Expr(:., :f, Expr(:tuple, a, b))`, which PR #230 rewrites into a call of the
symbol `f.` (`src/Parse.jl:389-394`) and resolves by the operators'
`get_op_name` spellings (`src/Parse.jl:309`). -/

namespace DynExpr.StringsParse.General

open DynExpr.StringsParse.Roundtrip

set_option maxHeartbeats 400000

/-- Operator tables of broadcast callables of plainly named functions, which
`_get_op_name` spells `f.` (`src/Strings.jl:53-66`), with names unique per
degree (`src/Parse.jl:325-342` rejects ambiguous matches). -/
def BroadcastOps (ops : Operators) : Prop :=
  ∀ os ∈ ops, (os.map NamedOp.name).Nodup ∧
    ∀ op ∈ os, plainName op.name = true ∧ op.broadcast = true ∧ op.display = broadcastName op.name

/-- Constants whose finite parts are terminating decimals (Q21); complex
constants require `im` to be undeclared (`src/Parse.jl:220-250`). -/
def BroadcastConsts (names : List String) : Tree Scalar → Prop
  | .const v => ConstOK v ∧ (∀ r i, v = .complex r i → names.contains "im" = false)
  | .feature _ => True
  | .branch _ cs => ∀ c ∈ cs, BroadcastConsts names c

/-- Every well-formed tree whose operators are broadcast callables of plainly
named functions has reparsable printed text: the printed `f.(args...)` dot calls
resolve since PR #230, src/Strings.jl:46-133 and src/Parse.jl:298-421. -/
def BroadcastRoundtrip : Prop := ∀ ops names t,
  CleanNames names → names.contains "NaN" = false → names.contains "Inf" = false →
  t.WF 2 ops.enum.nops names.length → BroadcastOps ops → BroadcastConsts names t →
  (renderParse ops names t).isSome = true

/-! ## Strings -/

theorem toList_dot : ".".toList = ['.'] := by decide
theorem singleton_dot : String.singleton '.' = "." := by decide

theorem append_dot_inj {a b : String} (h : a ++ "." = b ++ ".") : a = b := by
  have h1 := congrArg String.toList h
  rw [String.toList_append, String.toList_append, toList_dot] at h1
  have h2 : a.toList = b.toList := by
    first | exact List.append_cancel_right h1 | simpa using h1
  have h3 := congrArg String.ofList h2
  rwa [String.ofList_toList, String.ofList_toList] at h3

theorem nodup_map_dot {l : List String} (h : l.Nodup) : (l.map (fun s => s ++ ".")).Nodup := by
  first
    | exact List.Pairwise.map _ (fun a b hab heq => hab (append_dot_inj heq)) h
    | exact List.Nodup.map (fun a b heq => append_dot_inj heq) h

theorem broadcastName_plain {n : String} (hp : plainName n = true) : broadcastName n = n ++ "." := by
  obtain ⟨_, c, cs, hl, hal, _⟩ := ident_facts hp
  have hc : (['+', '-', '*', '/', '^'].contains c) = false := by
    cases hcx : (['+', '-', '*', '/', '^'].contains c)
    · rfl
    · exfalso
      rcases (by simpa using hcx : c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '/' ∨ c = '^') with
        h | h | h | h | h <;> (subst h; exact absurd hal (by decide))
  unfold broadcastName
  rw [hl]
  simp only [List.headD_cons, hc, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- The default `Core.eval(EmptyModule, head)` functions never end in `.`, so
a rewritten dot-call head falls through to `_find_operator_by_name`
(`src/Parse.jl:402-409`). -/
theorem dot_not_builtin (n : String) :
    ["+", "-", "*", "/", "^", "sin", "cos", "exp"].contains (n ++ ".") = false := by
  have hl : (n ++ ".").toList.getLast? = some '.' := by
    rw [String.toList_append, toList_dot, getLast?_snoc]
  have hall : ∀ s ∈ ["+", "-", "*", "/", "^", "sin", "cos", "exp"],
      s.toList.getLast? ≠ some '.' := by decide
  cases h : ["+", "-", "*", "/", "^", "sin", "cos", "exp"].contains (n ++ ".")
  · rfl
  · exfalso
    have hm : (n ++ ".") ∈ ["+", "-", "*", "/", "^", "sin", "cos", "exp"] := by
      first | exact List.mem_of_elem_eq_true h | simpa using h
    exact hall _ hm hl

/-! ## Operator tables -/

theorem bcast_table {ops : Operators} (h : BroadcastOps ops) (d : Nat) :
    ((table ops d).map NamedOp.name).Nodup ∧
      ∀ op ∈ table ops d, plainName op.name = true ∧ op.broadcast = true ∧
        op.display = broadcastName op.name := by
  unfold table
  cases hd : ops[d - 1]? with
  | none => simp
  | some os =>
    have hm : os ∈ ops := List.mem_of_getElem? hd
    simpa using h os hm

theorem parseName_bcast {op : NamedOp}
    (h : plainName op.name = true ∧ op.broadcast = true ∧ op.display = broadcastName op.name) :
    op.parseName = op.name ++ "." := by
  unfold NamedOp.parseName
  rw [if_pos h.2.1, h.2.2, broadcastName_plain h.1]

theorem bcast_nodup {ops : Operators} (hops : BroadcastOps ops) (d : Nat) :
    ((table ops d).map NamedOp.parseName).Nodup := by
  obtain ⟨hnd, hall⟩ := bcast_table hops d
  have hpn : ∀ o ∈ table ops d, o.parseName = o.name ++ "." := fun o ho => parseName_bcast (hall o ho)
  rw [List.map_congr_left hpn]
  have e : (table ops d).map (fun o => o.name ++ ".") =
      ((table ops d).map NamedOp.name).map (fun s => s ++ ".") := by
    rw [List.map_map]
    all_goals rfl
  rw [e]
  exact nodup_map_dot hnd

theorem opName_plain {ops : Operators} (hops : BroadcastOps ops) {d idx : Nat} (hi : 1 ≤ idx)
    (hl : idx ≤ (table ops d).length) : plainName (opName ops d idx) = true := by
  rw [opName_eq hi hl]
  exact ((bcast_table hops d).2 _ (List.getElem_mem (l := table ops d) (n := idx - 1) (by omega))).1

theorem dispatch_bcast {ops : Operators} (hops : BroadcastOps ops) {d idx : Nat} (hd : 0 < d)
    (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    dispatchOpName (some ops) d idx false = .ok (opName ops d idx ++ ".") := by
  have hget : (ops[d - 1]?.getD [])[idx - 1]? = some ((table ops d)[idx - 1]'(by omega)) :=
    List.getElem?_eq_getElem (l := table ops d) (by omega)
  rw [General.dispatchNames ops _ d idx false hd (by omega) hget]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [opName_eq hi hl]
  have hall := (bcast_table hops d).2 _ (List.getElem_mem (l := table ops d) (n := idx - 1) (by omega))
  rw [hall.2.2, broadcastName_plain hall.1]

theorem find_zipIdx_some (P : NamedOp → Bool) (op : NamedOp) (hP : P op = true) :
    ∀ (l : List NamedOp) (n : Nat), op ∈ l → ∃ q, (l.zipIdx n).find? (fun p => P p.1) = some q := by
  intro l
  induction l with
  | nil => intro n h; simp at h
  | cons x l ih =>
    intro n h
    cases hx : P x with
    | true => exact ⟨(x, n), by simp [List.zipIdx_cons, List.find?_cons, hx]⟩
    | false =>
      rcases List.mem_cons.mp h with rfl | h'
      · rw [hP] at hx; cases hx
      · obtain ⟨q, hq⟩ := ih (n + 1) h'
        exact ⟨q, by simp [List.zipIdx_cons, List.find?_cons, hx, hq]⟩

/-- Some identity-or-alias match exists for every table member
(`src/Parse.jl:433-440`). -/
theorem findOpIndex_some {ops : Operators} {d : Nat} {op : NamedOp} (hd : d ≠ 0)
    (hm : op ∈ table ops d) : ∃ j, findOpIndex ops op.identity d = some j := by
  obtain ⟨q, hq⟩ := find_zipIdx_some (fun o => o.identity == op.identity || o.alias == op.identity) op
    (by simp) (table ops d) 0 hm
  unfold table at hq
  refine ⟨q.2 + 1, ?_⟩
  unfold findOpIndex
  simp only [hd, ↓reduceIte]
  rw [hq]
  all_goals rfl

theorem resolved_dot {ops : Operators} {names : List String} {n identity : String} {d : Nat}
    (hf : findOperatorByName ops (n ++ ".") d = .ok identity) :
    Resolved (parser ops names) (n ++ ".") identity d := by
  unfold Resolved
  split
  · rename_i id hb
    have hb' : (if ["+", "-", "*", "/", "^", "sin", "cos", "exp"].contains (n ++ ".")
        then some (n ++ ".") else none) = some id := hb
    rw [dot_not_builtin] at hb'
    simp at hb'
  · exact hf

/-- The rewritten head `f.` of a printed broadcast call resolves to its
operator, which has an exact-arity index. -/
theorem bLookup {ops : Operators} (hops : BroadcastOps ops) (names : List String) {d idx : Nat}
    (hd : 1 ≤ d) (hi : 1 ≤ idx) (hl : idx ≤ (table ops d).length) :
    ∃ identity, Resolved (parser ops names) (opName ops d idx ++ ".") identity d ∧
      ∃ j, findOpIndex ops identity d = some j := by
  have hm := List.getElem_mem (l := table ops d) (n := idx - 1) (by omega)
  have hname : opName ops d idx = ((table ops d)[idx - 1]'(by omega)).name := opName_eq hi hl
  generalize ((table ops d)[idx - 1]'(by omega)) = op at hm hname
  have hfind := findOperatorByName_mem hd hm (bcast_nodup hops d)
  rw [parseName_bcast ((bcast_table hops d).2 op hm), ← hname] at hfind
  exact ⟨op.identity, resolved_dot hfind, findOpIndex_some (by omega) hm⟩

/-! ## Printed text and tokens -/

/-- Rendered text with its outer pair stripped. -/
def btext (ops : Operators) (names : List String) : Tree Scalar → String
  | .const v => scalarText v
  | .feature k => names[k - 1]?.getD ""
  | .branch idx [c] => opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")"
  | .branch idx [a, b] =>
      opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++ btext ops names b ++ ")"
  | .branch _ _ => ""

/-- Tokens of `btext`. -/
def btoks (ops : Operators) (names : List String) : Tree Scalar → List String
  | .const v => toksC v
  | .feature k => [names[k - 1]?.getD ""]
  | .branch idx [c] => opName ops 1 idx :: "." :: "(" :: (btoks ops names c ++ [")"])
  | .branch idx [a, b] =>
      opName ops 2 idx :: "." :: "(" :: (btoks ops names a ++ "," :: btoks ops names b ++ [")"])
  | .branch _ _ => []

/-- Syntax that `Meta.parse` returns for `btext`: dot calls for operators. -/
def bsurf (ops : Operators) (names : List String) : Tree Scalar → Surface
  | .const v => surfC v
  | .feature k => .symbol (names[k - 1]?.getD "")
  | .branch idx [c] => .dotCall (opName ops 1 idx) [bsurf ops names c]
  | .branch idx [a, b] => .dotCall (opName ops 2 idx) [bsurf ops names a, bsurf ops names b]
  | .branch _ _ => .unsupported ""

/-! ## Rendering and lexing -/

theorem strip_const (v : Scalar) (hv : ConstOK v) :
    stripBrackets (stringConstant v) = .ok (scalarText v) := by
  cases v with
  | real w =>
    obtain ⟨hne, hh⟩ := realText_facts w hv
    exact strip_plain hne hh
  | float32 w =>
    obtain ⟨hne, hh⟩ := realText_facts w hv
    exact strip_plain hne hh
  | complex r i =>
    have hwrap : ("(" ++ scalarText (.complex r i) ++ ")").toList =
        '(' :: (scalarText (.complex r i)).toList ++ [')'] := by
      simp [String.toList_append, toList_lp, toList_rp]
    show stripBrackets ("(" ++ scalarText (.complex r i) ++ ")") = _
    rw [strip_wrapped hwrap, String.ofList_toList]

theorem lexOK_dot {r ts} (h : LexOK r ts) : LexOK ('.' :: r) ("." :: ts) :=
  lexOK_step (fun f rest => by
    rw [lex_punct (by decide) (by decide) (by decide) (by decide) (by decide), singleton_dot]) h

theorem lexOK_Rb (w : JF) (hw : FinOK w) {r : List Char} {ts : List String} (hb : Bd r)
    (h : LexOK r ts) : LexOK ((realText w).toList ++ r) (toksR w ++ ts) := by
  have hi := bd_ident hb
  cases w with
  | fin q => exact lexOK_real hw (bd_num hb) h
  | nan => simpa [realText, toksR] using lexOK_ident (s := "NaN") (by decide) hi h
  | posInf => simpa [realText, toksR] using lexOK_ident (s := "Inf") (by decide) hi h
  | negInf =>
    have := lexOK_minus (lexOK_ident (s := "Inf") (by decide) hi h)
    have hl : (realText .negInf).toList = '-' :: "Inf".toList := by decide
    rw [hl]
    simpa [toksR] using this

theorem lexOK_Ib (w : JF) (hw : FinOK w) {r : List Char} {ts : List String} (hb : Bd r)
    (h : LexOK r ts) : LexOK ((imagText w).toList ++ r) (toksI w ++ ts) := by
  have him : LexOK ("im".toList ++ r) ("im" :: ts) :=
    lexOK_ident (s := "im") (by decide) (bd_ident hb) h
  have hstar : LexOK ("*".toList ++ ("im".toList ++ r)) ("*" :: "im" :: ts) :=
    lexOK_infix (n := "*") (by decide) him
  cases w with
  | fin q =>
    have hmag : 0 ≤ imagMag q := by
      unfold imagMag; split
      · exact neg_nonneg_of ‹_›
      · exact num_nonneg ‹_›
    have := lexOK_dec hmag (r := "im".toList ++ r)
      (by intro x hx; simp [toList_im] at hx; subst hx; decide) him
    simpa [imagText, toksI, String.toList_append] using this
  | nan =>
    have := lexOK_ident (s := "NaN") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this
  | posInf =>
    have := lexOK_ident (s := "Inf") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this
  | negInf =>
    have := lexOK_ident (s := "Inf") (by decide) (by intro x hx; simp at hx; subst hx; decide) hstar
    simpa [imagText, toksI, String.toList_append] using this

theorem lexOK_Cb (v : Scalar) (hv : ConstOK v) {r : List Char} {ts : List String} (hb : Bd r)
    (h : LexOK r ts) : LexOK ((scalarText v).toList ++ r) (toksC v ++ ts) := by
  cases v with
  | real w => exact lexOK_Rb w hv hb h
  | float32 w => exact lexOK_Rb w hv hb h
  | complex re i =>
    rw [scalarText_complex]
    have hI := lexOK_infix (signJ_infix i) (lexOK_ws (lexOK_Ib i hv.2 hb h))
    have := lexOK_Rb re hv.1 (r := ' ' :: ((signJ i).toList ++ ' ' :: ((imagText i).toList ++ r)))
      (by intro x hx; simp at hx; subst hx; simp) (lexOK_ws hI)
    simpa [toksC, List.append_assoc] using this

theorem combine_dot2 (n a b a' b' : String) (hp : plainName n = true)
    (ha : stripBrackets a = .ok a') (hb : stripBrackets b = .ok b') :
    combineOpWithInputs (n ++ ".") [a, b] = .ok (n ++ "." ++ "(" ++ a' ++ ", " ++ b' ++ ")") := by
  obtain ⟨_, c, cs, hl, hal, _⟩ := ident_facts hp
  have hl' : (n ++ ".").toList = c :: (cs ++ ['.']) := by
    simp [String.toList_append, hl, toList_dot]
  have hc : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c || (n ++ ".") == "!=") = false := by
    have hne : (n ++ ".") ≠ "!=" :=
      ne_of_heads hl' (by decide : ("!=" : String).toList.head? = some '!')
        (by intro h; subst h; exact absurd hal (by decide))
    have hcc : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c) = false := by
      cases hcx : (['+', '-', '*', '/', '^', '.', '>', '<', '='].contains c)
      · rfl
      · exfalso
        rcases (by simpa using hcx : c = '+' ∨ c = '-' ∨ c = '*' ∨ c = '/' ∨ c = '^' ∨ c = '.' ∨
          c = '>' ∨ c = '<' ∨ c = '=') with h | h | h | h | h | h | h | h | h <;>
          (subst h; exact absurd hal (by decide))
    rw [hcc, Bool.false_or]
    simpa using hne
  unfold combineOpWithInputs
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, beq_self_eq_true, ↓reduceIte, hl',
    List.head?_cons]
  rw [hc]
  simp [ha, hb, intercalate_two, String.append_assoc]
  try rfl

/-- Every tree renders, strips, and lexes to its token specification. -/
theorem bRender {ops : Operators} {names : List String} (hops : BroadcastOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (hconst : BroadcastConsts names t) :
    ∃ s, rawTree (rcfg ops names) t = .ok s ∧ stripBrackets s = .ok (btext ops names t) ∧
      ∀ r ts, Bd r → LexOK r ts →
        LexOK ((btext ops names t).toList ++ r) (btoks ops names t ++ ts) := by
  induction t using Tree.induction with
  | hc v =>
    simp only [BroadcastConsts] at hconst
    exact ⟨stringConstant v, rfl, strip_const v hconst.1,
      fun r ts hr h => lexOK_Cb v hconst.1 hr h⟩
  | hf k =>
    simp only [Tree.WF] at hw
    have hk : k - 1 < names.length := by omega
    have hpn := hn.2.2 _ (List.getElem_mem hk)
    obtain ⟨_, c, cs, hl, hal, _⟩ := ident_facts hpn
    have hhead : names[k - 1].toList.head? ≠ some '(' := by
      rw [hl]; intro h; simp at h; subst h; exact absurd hal (by decide)
    have hne : names[k - 1].toList ≠ [] := by rw [hl]; simp
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    have hraw : rawTree (rcfg ops names) (.feature k) = .ok names[k - 1] := by
      have hz : k ≠ 0 := by omega
      simp [rawTree, rcfg, stringVariable, hz, List.getElem?_eq_getElem hk]
    refine ⟨names[k - 1], hraw, ?_, ?_⟩
    · show stripBrackets names[k - 1] = .ok (names[k - 1]?.getD "")
      rw [hname]
      exact strip_plain hne hhead
    · intro r ts hr h
      show LexOK ((names[k - 1]?.getD "").toList ++ r) ([names[k - 1]?.getD ""] ++ ts)
      rw [hname]
      simpa using lexOK_ident (ascii_of_plain hpn) (bd_ident hr) h
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have hk' := hconst
    simp only [BroadcastConsts] at hk'
    match cs, hl1, hl2, hi2, ih, hcs, hk' with
    | [c], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_singleton] at hi2
      obtain ⟨sc, hrc, hsc, hlc⟩ := ih c (by simp) (hcs c (by simp)) (hk' c (by simp))
      have hlen := table_len (ops := ops) (d := 1) (by decide) hi2
      have hpl := opName_plain hops hi1 hlen
      obtain ⟨_, c0, cs0, hnl0, hal, _⟩ := ident_facts hpl
      have hdisp := dispatch_bcast hops (d := 1) (by decide) hi1 hlen
      have hraw : rawTree (rcfg ops names) (.branch idx [c]) =
          .ok (opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")") := by
        simp only [rawTree, rawForest, hrc, bind, Except.bind, pure, Except.pure]
        simp only [rcfg, resolvePretty, Option.getD_none, Option.map_none, List.length_cons,
          List.length_nil, Nat.zero_add] at hdisp ⊢
        rw [hdisp]
        exact combine_prefix1 _ sc _ (by simp [String.toList_append, toList_dot]) hsc
      have htl : (opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")").toList =
          (opName ops 1 idx).toList ++ '.' :: '(' :: ((btext ops names c).toList ++ [')']) := by
        simp [String.toList_append, toList_lp, toList_rp, toList_dot]
      have hne : (opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")").toList ≠ [] := by
        rw [htl, hnl0]; simp
      have hhead : (opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")").toList.head? ≠
          some '(' := by
        rw [htl, hnl0]; intro h; simp at h; subst h; exact absurd hal (by decide)
      have hbt : btext ops names (.branch idx [c]) =
          opName ops 1 idx ++ "." ++ "(" ++ btext ops names c ++ ")" := by simp only [btext]
      have hbk : ∀ ts, btoks ops names (.branch idx [c]) ++ ts =
          opName ops 1 idx :: "." :: "(" :: (btoks ops names c ++ ")" :: ts) := by
        intro ts; simp [btoks]
      refine ⟨_, hraw, ?_, ?_⟩
      · rw [hbt]; exact strip_plain hne hhead
      · intro r ts hr h
        have hin := hlc (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp)
          (lexOK_rp h)
        have hN := lexOK_ident (ascii_of_plain hpl) (by intro x hx; simp at hx; subst hx; decide)
          (lexOK_dot (lexOK_lp hin))
        rw [hbt, hbk]
        simpa [String.toList_append, toList_lp, toList_rp, toList_dot, List.append_assoc] using hN
    | [a, b], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      obtain ⟨sa, hra, hsa, hla⟩ := ih a (by simp) (hcs a (by simp)) (hk' a (by simp))
      obtain ⟨sb, hrb, hsb, hlb⟩ := ih b (by simp) (hcs b (by simp)) (hk' b (by simp))
      have hlen := table_len (ops := ops) (d := 2) (by decide) hi2
      have hpl := opName_plain hops hi1 hlen
      obtain ⟨_, c0, cs0, hnl0, hal, _⟩ := ident_facts hpl
      have hdisp := dispatch_bcast hops (d := 2) (by decide) hi1 hlen
      have hraw : rawTree (rcfg ops names) (.branch idx [a, b]) =
          .ok (opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++ btext ops names b ++ ")") := by
        simp only [rawTree, rawForest, hra, hrb, bind, Except.bind, pure, Except.pure]
        simp only [rcfg, resolvePretty, Option.getD_none, Option.map_none, List.length_cons,
          List.length_nil, Nat.zero_add, Nat.reduceAdd] at hdisp ⊢
        rw [hdisp]
        exact combine_dot2 _ sa sb _ _ hpl hsa hsb
      have htl : (opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++
          btext ops names b ++ ")").toList =
          (opName ops 2 idx).toList ++ '.' :: '(' :: ((btext ops names a).toList ++
            ',' :: ' ' :: ((btext ops names b).toList ++ [')'])) := by
        simp [String.toList_append, toList_lp, toList_rp, toList_dot, toList_csp]
      have hne : (opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++
          btext ops names b ++ ")").toList ≠ [] := by
        rw [htl, hnl0]; simp
      have hhead : (opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++
          btext ops names b ++ ")").toList.head? ≠ some '(' := by
        rw [htl, hnl0]; intro h; simp at h; subst h; exact absurd hal (by decide)
      have hbt : btext ops names (.branch idx [a, b]) =
          opName ops 2 idx ++ "." ++ "(" ++ btext ops names a ++ ", " ++ btext ops names b ++ ")" := by
        simp only [btext]
      have hbk : ∀ ts, btoks ops names (.branch idx [a, b]) ++ ts =
          opName ops 2 idx :: "." :: "(" :: (btoks ops names a ++ "," ::
            (btoks ops names b ++ ")" :: ts)) := by
        intro ts; simp [btoks]
      refine ⟨_, hraw, ?_, ?_⟩
      · rw [hbt]; exact strip_plain hne hhead
      · intro r ts hr h
        have hB := hlb (')' :: r) (")" :: ts) (by intro x hx; simp at hx; subst hx; simp)
          (lexOK_rp h)
        have hC := lexOK_comma (lexOK_ws hB)
        have hA := hla (',' :: ' ' :: ((btext ops names b).toList ++ ')' :: r))
          ("," :: (btoks ops names b ++ ")" :: ts)) (by intro x hx; simp at hx; subst hx; simp) hC
        have hN := lexOK_ident (ascii_of_plain hpl) (by intro x hx; simp at hx; subst hx; decide)
          (lexOK_dot (lexOK_lp hA))
        rw [hbt, hbk]
        simpa [String.toList_append, toList_lp, toList_rp, toList_dot, toList_csp,
          List.append_assoc] using hN
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

/-! ## Token parsing -/

/-- Token lists without parentheses or commas. -/
def Flat (ts : List String) : Prop := ∀ x ∈ ts, x ≠ "(" ∧ x ≠ ")" ∧ x ≠ ","

theorem flat_nil : Flat [] := by intro x hx; simp at hx

theorem flat_cons {t : String} {ts : List String} (h1 : t ≠ "(") (h2 : t ≠ ")") (h3 : t ≠ ",")
    (h : Flat ts) : Flat (t :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact ⟨h1, h2, h3⟩
  · exact h x hx'

theorem flat_append {a b : List String} (ha : Flat a) (hb : Flat b) : Flat (a ++ b) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · exact hb x h

theorem flat_bal : ∀ {ts : List String}, Flat ts → Bal ts
  | [], _ => Bal.nil
  | t :: _, h =>
    Bal.tok (h t (by simp)).1 (h t (by simp)).2.1 (flat_bal (fun x hx => h x (by simp [hx])))

theorem topAux_mem (ts : List String) :
    ∀ (i d : Nat) (p : Nat × String), p ∈ topAux ts i d → p.2 ∈ ts := by
  induction ts with
  | nil => intro i d p hp; simp [topAux] at hp
  | cons t ts ih =>
    intro i d p hp
    simp only [topAux] at hp
    split at hp
    · exact List.mem_cons_of_mem _ (ih _ _ p hp)
    · split at hp
      · exact List.mem_cons_of_mem _ (ih _ _ p hp)
      · split at hp
        · rcases List.mem_cons.mp hp with rfl | hp'
          · simp
          · exact List.mem_cons_of_mem _ (ih _ _ p hp')
        · exact List.mem_cons_of_mem _ (ih _ _ p hp)

theorem flat_dec {q : Rat} (hq : 0 ≤ q) : dec q ≠ "(" ∧ dec q ≠ ")" ∧ dec q ≠ "," := by
  obtain ⟨⟨h1, h2, _, _, _, _, _, h8⟩, _⟩ := dec_facts hq
  exact ⟨h1, h2, h8⟩

theorem flat_realToks (q : Rat) : Flat (realToks q) := by
  unfold realToks
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := flat_dec (neg_nonneg_of h)
    exact flat_cons (by decide) (by decide) (by decide) (flat_cons h1 h2 h3 flat_nil)
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := flat_dec (num_nonneg h)
    exact flat_cons h1 h2 h3 flat_nil

theorem flat_toksR (w : JF) : Flat (toksR w) := by
  cases w with
  | fin q => exact flat_realToks q
  | nan => exact flat_cons (by decide) (by decide) (by decide) flat_nil
  | posInf => exact flat_cons (by decide) (by decide) (by decide) flat_nil
  | negInf =>
    exact flat_cons (by decide) (by decide) (by decide)
      (flat_cons (by decide) (by decide) (by decide) flat_nil)

theorem flat_toksI (w : JF) : Flat (toksI w) := by
  have hstar : Flat ["*", "im"] :=
    flat_cons (by decide) (by decide) (by decide) (flat_cons (by decide) (by decide) (by decide) flat_nil)
  cases w with
  | fin q =>
    have hmag : 0 ≤ imagMag q := by
      unfold imagMag; split
      · exact neg_nonneg_of ‹_›
      · exact num_nonneg ‹_›
    obtain ⟨h1, h2, h3⟩ := flat_dec hmag
    exact flat_cons h1 h2 h3 (flat_cons (by decide) (by decide) (by decide) flat_nil)
  | nan => exact flat_cons (by decide) (by decide) (by decide) hstar
  | posInf => exact flat_cons (by decide) (by decide) (by decide) hstar
  | negInf => exact flat_cons (by decide) (by decide) (by decide) hstar

theorem flat_toksC (v : Scalar) : Flat (toksC v) := by
  cases v with
  | real w => exact flat_toksR w
  | float32 w => exact flat_toksR w
  | complex r i =>
    have hs : signJ i ≠ "(" ∧ signJ i ≠ ")" ∧ signJ i ≠ "," := by
      rcases signJ_cases i with h | h <;> rw [h] <;> decide
    exact flat_append (flat_toksR r) (flat_cons hs.1 hs.2.1 hs.2.2 (flat_toksI i))

theorem toksC_ne (v : Scalar) : toksC v ≠ [] := by
  cases v with
  | real w => exact (toksR_facts w).2.1
  | float32 w => exact (toksR_facts w).2.1
  | complex r i => simp [toksC]

theorem topAux_dot {n : String} {x : List String} (hn1 : n ≠ "(") (hn2 : n ≠ ")") (hx : Bal x)
    (i : Nat) : topAux (n :: "." :: "(" :: (x ++ [")"])) i 0 = [(i, n), (i + 1, ".")] := by
  rw [topAux]
  simp only [ne_beq hn1, ne_beq hn2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  rw [topAux]
  simp only [ne_beq (show ("." : String) ≠ "(" by decide), ne_beq (show ("." : String) ≠ ")" by decide),
    Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  have e := topAux_wrapped hx (i + 1 + 1)
  simp only [List.cons_append] at e
  rw [e]

/-- A dot call `f.(args)` parses to `Expr(:., f, Expr(:tuple, args...))`
(`src/Parse.jl:298`). -/
theorem mpt_dot (rec : List String → Jl Surface) {n : String} {x : List String} (hn : plainTok n)
    (hx : Bal x) (args : List Surface) (hargs : (splitC x).mapM rec = .ok args) :
    mptBody rec (n :: "." :: "(" :: (x ++ [")"])) = .ok (.dotCall n args) := by
  have hop := plainTok_opTok hn
  obtain ⟨hn1, hn2, hn3, hn4, _⟩ := hn
  have ho : outerP (n :: "." :: "(" :: (x ++ [")"])) = false := outerP_head (by simpa using hn1)
  have hd : ftAux ("." :: "(" :: (x ++ [")"])) (some n) 1 0 = [(1, ".")] := by
    have hw := ftAux_wrapped hx (some ".") 2
    simp only [List.cons_append] at hw
    rw [ftAux]
    simp [hop, hw]
  have hl3 : ("(" :: (x ++ [")"])).getLast? = some ")" := by
    rw [← List.cons_append, getLast?_snoc]
  have ht : ftAux (n :: "." :: "(" :: (x ++ [")"])) none 0 0 = [(1, ".")] := by
    rw [ftAux]
    simp [hn1, hn2, hd]
  have hdrop : ((n :: "." :: "(" :: (x ++ [")"])).drop 3).take
      ((n :: "." :: "(" :: (x ++ [")"])).length - 4) = x := by
    simp
  unfold mptBody
  rw [tops_eq, ht, hdrop, hargs]
  simp [ho, hn3, hn4, hl3]
  try rfl

/-- Token invariants of every tree. -/
theorem bToks {ops : Operators} {names : List String} (hops : BroadcastOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (hconst : BroadcastConsts names t) :
    Bal (btoks ops names t) ∧ btoks ops names t ≠ [] ∧
      ∀ i p, p ∈ topAux (btoks ops names t) i 0 → p.2 ≠ "," := by
  induction t using Tree.induction with
  | hc v =>
    have hfl := flat_toksC v
    exact ⟨flat_bal hfl, toksC_ne v, fun i p hp => (hfl _ (topAux_mem _ i 0 p hp)).2.2⟩
  | hf k =>
    simp only [Tree.WF] at hw
    have hk : k - 1 < names.length := by omega
    have hpt := (ident_facts (hn.2.2 _ (List.getElem_mem hk))).1
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    show Bal [names[k - 1]?.getD ""] ∧ [names[k - 1]?.getD ""] ≠ [] ∧
      ∀ i p, p ∈ topAux [names[k - 1]?.getD ""] i 0 → p.2 ≠ ","
    rw [hname]
    refine ⟨Bal.single hpt.1 hpt.2.1, by simp, fun i p hp => ?_⟩
    have hm := topAux_mem _ i 0 p hp
    simp only [List.mem_singleton] at hm
    rw [hm]
    exact hpt.2.2.2.2.2.2.2
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have hk' := hconst
    simp only [BroadcastConsts] at hk'
    match cs, hl1, hl2, hi2, ih, hcs, hk' with
    | [c], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_singleton] at hi2
      have Fc := ih c (by simp) (hcs c (by simp)) (hk' c (by simp))
      have hpt := (ident_facts (opName_plain hops hi1 (table_len (ops := ops) (d := 1) (by decide) hi2))).1
      have hb : btoks ops names (.branch idx [c]) =
          opName ops 1 idx :: "." :: "(" :: (btoks ops names c ++ [")"]) := by simp [btoks]
      rw [hb]
      refine ⟨Bal.tok hpt.1 hpt.2.1 (Bal.tok (by decide) (by decide) (Bal.group Fc.1)), by simp,
        fun i p hp => ?_⟩
      rw [topAux_dot hpt.1 hpt.2.1 Fc.1] at hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hpt.2.2.2.2.2.2.2
      · exact (by decide : ("." : String) ≠ ",")
    | [a, b], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      have Fa := ih a (by simp) (hcs a (by simp)) (hk' a (by simp))
      have Fb := ih b (by simp) (hcs b (by simp)) (hk' b (by simp))
      have hpt := (ident_facts (opName_plain hops hi1 (table_len (ops := ops) (d := 2) (by decide) hi2))).1
      have hx : Bal (btoks ops names a ++ "," :: btoks ops names b) :=
        Bal.append Fa.1 (Bal.tok (by decide) (by decide) Fb.1)
      have hb : btoks ops names (.branch idx [a, b]) =
          opName ops 2 idx :: "." :: "(" :: ((btoks ops names a ++ "," :: btoks ops names b) ++ [")"]) := by
        simp [btoks]
      rw [hb]
      refine ⟨Bal.tok hpt.1 hpt.2.1 (Bal.tok (by decide) (by decide) (Bal.group hx)), by simp,
        fun i p hp => ?_⟩
      rw [topAux_dot hpt.1 hpt.2.1 hx] at hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hpt.2.2.2.2.2.2.2
      · exact (by decide : ("." : String) ≠ ",")
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

/-- Tokens of every tree parse to its dot-call syntax. -/
theorem bParse {ops : Operators} {names : List String} (hops : BroadcastOps ops)
    (hn : CleanNames names) (t : Tree Scalar) (hw : t.WF 2 ops.enum.nops names.length)
    (hconst : BroadcastConsts names t) :
    ∀ fuel, (btoks ops names t).length ≤ fuel →
      metaParseTokens fuel (btoks ops names t) = .ok (bsurf ops names t) := by
  induction t using Tree.induction with
  | hc v =>
    simp only [BroadcastConsts] at hconst
    intro fuel hf
    exact parse_C v hconst.1 fuel hf
  | hf k =>
    simp only [Tree.WF] at hw
    have hk : k - 1 < names.length := by omega
    have hpn := hn.2.2 _ (List.getElem_mem hk)
    have hname : names[k - 1]?.getD "" = names[k - 1] := by
      rw [List.getElem?_eq_getElem hk]; rfl
    intro fuel hf
    show metaParseTokens fuel [names[k - 1]?.getD ""] = .ok (.symbol (names[k - 1]?.getD ""))
    rw [hname]
    exact parse_ident hpn fuel (by simpa [btoks] using hf)
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have hk' := hconst
    simp only [BroadcastConsts] at hk'
    match cs, hl1, hl2, hi2, ih, hcs, hk' with
    | [c], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_singleton] at hi2
      have hpl := opName_plain hops hi1 (table_len (ops := ops) (d := 1) (by decide) hi2)
      have Fc := bToks hops hn c (hcs c (by simp)) (hk' c (by simp))
      have IHc := ih c (by simp) (hcs c (by simp)) (hk' c (by simp))
      intro fuel hf
      have hb : btoks ops names (.branch idx [c]) =
          opName ops 1 idx :: "." :: "(" :: (btoks ops names c ++ [")"]) := by simp [btoks]
      rw [hb] at hf ⊢
      obtain ⟨f, rfl, hf'⟩ := mpt_fuel
        (ts := opName ops 1 idx :: "." :: "(" :: (btoks ops names c ++ [")"])) (by simp) hf
      have hargs : (splitC (btoks ops names c)).mapM (metaParseTokens f) =
          .ok [bsurf ops names c] := by
        rw [splitC_single Fc.2.1 (Fc.2.2 0)]
        simp [IHc f (by simp at hf'; omega)] <;> rfl
      rw [mpt_succ, mpt_dot _ (ident_facts hpl).1 Fc.1 _ hargs]
      simp only [bsurf]
    | [a, b], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      have hpl := opName_plain hops hi1 (table_len (ops := ops) (d := 2) (by decide) hi2)
      have Fa := bToks hops hn a (hcs a (by simp)) (hk' a (by simp))
      have Fb := bToks hops hn b (hcs b (by simp)) (hk' b (by simp))
      have IHa := ih a (by simp) (hcs a (by simp)) (hk' a (by simp))
      have IHb := ih b (by simp) (hcs b (by simp)) (hk' b (by simp))
      have hx : Bal (btoks ops names a ++ "," :: btoks ops names b) :=
        Bal.append Fa.1 (Bal.tok (by decide) (by decide) Fb.1)
      intro fuel hf
      have hb : btoks ops names (.branch idx [a, b]) =
          opName ops 2 idx :: "." :: "(" :: ((btoks ops names a ++ "," :: btoks ops names b) ++ [")"]) := by
        simp [btoks]
      rw [hb] at hf ⊢
      obtain ⟨f, rfl, hf'⟩ := mpt_fuel
        (ts := opName ops 2 idx :: "." :: "(" :: ((btoks ops names a ++ "," :: btoks ops names b) ++ [")"]))
        (by simp) hf
      have hargs : (splitC (btoks ops names a ++ "," :: btoks ops names b)).mapM (metaParseTokens f) =
          .ok [bsurf ops names a, bsurf ops names b] := by
        rw [splitC_pair Fa.1 Fa.2.1 (Fa.2.2 0) (Fb.2.2 _)]
        simp [IHa f (by simp at hf'; omega), IHb f (by simp at hf'; omega)] <;> rfl
      rw [mpt_succ, mpt_dot _ (ident_facts hpl).1 hx _ hargs]
      simp only [bsurf]
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

/-! ## Package parsing -/

theorem normalize_dotCall (names : Option (List String)) (f : String) (args : List Surface) :
    normalize names (.dotCall f args) = .dotCall f (normalizeArgs names args) := by
  unfold normalize
  rfl

/-- `_parse_expression` rewrites `Expr(:., f, Expr(:tuple, args...))` into a
call of the symbol `f.` (`src/Parse.jl:389-394`). -/
theorem parseCore_dotCall (cfg : ParseConfig) (fuel : Nat) (f : String) (args : List Surface) :
    parseCore cfg (fuel + 1) (.dotCall f args) = parseCore cfg (fuel + 1) (.call (f ++ ".") args) := by
  first | rfl | simp only [parseCore]

/-- The normalized dot-call syntax of every tree parses successfully. -/
theorem bCore {ops : Operators} {names : List String} (hops : BroadcastOps ops)
    (hn : CleanNames names) (hnan : names.contains "NaN" = false)
    (hinf : names.contains "Inf" = false) (t : Tree Scalar)
    (hw : t.WF 2 ops.enum.nops names.length) (hconst : BroadcastConsts names t) :
    ∀ fuel, surfaceDepth (bsurf ops names t) < fuel →
      ∃ p, parseCore (parser ops names) fuel (normalize (some names) (bsurf ops names t)) = .ok p := by
  induction t using Tree.induction with
  | hc v =>
    simp only [BroadcastConsts] at hconst
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    show ∃ p, parseCore (parser ops names) (f + 1) (normalize (some names) (surfC v)) = .ok p
    rw [normalize_C hnan hinf v hconst.2]
    first
      | exact ⟨_, rfl⟩
      | exact ⟨_, by simp [parseCore, parseLeaf]⟩
  | hf k =>
    simp only [Tree.WF] at hw
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hk : k - 1 < names.length := by omega
    have hvi := variableIndex_clean hn (k := k) (by omega) (by omega)
    have hmem : names.contains (names[k - 1]?.getD "") = true := by
      rw [List.getElem?_eq_getElem hk]
      first
        | exact List.elem_eq_true_of_mem (List.getElem_mem hk)
        | simpa using List.getElem_mem hk
    show ∃ p, parseCore (parser ops names) (f + 1)
      (normalize (some names) (.symbol (names[k - 1]?.getD ""))) = .ok p
    rw [normalize_symbol_mem hmem]
    generalize names[k - 1]?.getD "" = s at hvi ⊢
    exact ⟨⟨"Node", .feature k⟩, by simp [parseCore, parseLeaf, parser, hvi]⟩
  | hb idx cs ih =>
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, ⟨hi1, hi2, _⟩, hcs⟩ := hw'
    have hk' := hconst
    simp only [BroadcastConsts] at hk'
    match cs, hl1, hl2, hi2, ih, hcs, hk' with
    | [c], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_singleton] at hi2
      have hlen := table_len (ops := ops) (d := 1) (by decide) hi2
      intro fuel hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hd : surfaceDepth (bsurf ops names c) < f := by
        simp only [bsurf, surfaceDepth, argsDepth] at hf; omega
      obtain ⟨p, hp⟩ := ih c (by simp) (hcs c (by simp)) (hk' c (by simp)) f hd
      obtain ⟨identity, hres, j, hj⟩ := bLookup hops names (d := 1) (by decide) hi1 hlen
      have hmap : [normalize (some names) (bsurf ops names c)].mapM (parseCore (parser ops names) f) =
          .ok [p] := by
        simp [hp] <;> rfl
      have hs : normalize (some names) (bsurf ops names (.branch idx [c])) =
          .dotCall (opName ops 1 idx) [normalize (some names) (bsurf ops names c)] := by
        simp only [bsurf]
        rw [normalize_dotCall, normalizeArgs_cons, normalizeArgs_nil]
      rw [hs, parseCore_dotCall]
      exact ⟨_, parseExact (parser ops names) f (opName ops 1 idx ++ ".") identity
        [normalize (some names) (bsurf ops names c)] [p] j hres rfl hj hmap⟩
    | [a, b], _, _, hi2, ih, hcs, hk' =>
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi2
      have hlen := table_len (ops := ops) (d := 2) (by decide) hi2
      intro fuel hf
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hda : surfaceDepth (bsurf ops names a) < f := by
        simp only [bsurf, surfaceDepth, argsDepth] at hf; omega
      have hdb : surfaceDepth (bsurf ops names b) < f := by
        simp only [bsurf, surfaceDepth, argsDepth] at hf; omega
      obtain ⟨pa, hpa⟩ := ih a (by simp) (hcs a (by simp)) (hk' a (by simp)) f hda
      obtain ⟨pb, hpb⟩ := ih b (by simp) (hcs b (by simp)) (hk' b (by simp)) f hdb
      obtain ⟨identity, hres, j, hj⟩ := bLookup hops names (d := 2) (by decide) hi1 hlen
      have hmap : [normalize (some names) (bsurf ops names a),
          normalize (some names) (bsurf ops names b)].mapM (parseCore (parser ops names) f) =
          .ok [pa, pb] := by
        simp [hpa, hpb] <;> rfl
      have hs : normalize (some names) (bsurf ops names (.branch idx [a, b])) =
          .dotCall (opName ops 2 idx)
            [normalize (some names) (bsurf ops names a), normalize (some names) (bsurf ops names b)] := by
        simp only [bsurf]
        rw [normalize_dotCall, normalizeArgs_cons, normalizeArgs_cons, normalizeArgs_nil]
      rw [hs, parseCore_dotCall]
      exact ⟨_, parseExact (parser ops names) f (opName ops 2 idx ++ ".") identity
        [normalize (some names) (bsurf ops names a), normalize (some names) (bsurf ops names b)]
        [pa, pb] j hres rfl hj hmap⟩
    | [], h, _, _, _, _, _ => simp at h
    | _ :: _ :: _ :: _, _, h, _, _, _, _ => simp at h

theorem broadcastRoundtrip : BroadcastRoundtrip := by
  intro ops names t hn hnan hinf hw hops hconst
  obtain ⟨s, hraw, hstrip, hlex⟩ := bRender hops hn t hw hconst
  have hst : stringTree (renderer ops names) t = .ok (btext ops names t) := by
    show stringTree (rcfg ops names) t = _
    simp only [stringTree, resolveNames, bind, Except.bind, pure, Except.pure]
    show (do let x ← rawTree (rcfg ops names) t; stripBrackets x) = _
    rw [hraw]
    exact hstrip
  have hl := hlex [] [] (by intro x hx; simp at hx) lexOK_nil
  simp only [List.append_nil] at hl
  have hlexed : lex ((btext ops names t).length + 1) (btext ops names t).toList = btoks ops names t :=
    hl _ (by rw [String.length_toList]; omega)
  have hfuel : (btoks ops names t).length ≤ (btext ops names t).length + 1 := by
    rw [← hlexed]; exact lex_length _ _
  have hmeta : metaParse (btext ops names t) = .ok (bsurf ops names t) := by
    unfold metaParse
    rw [hlexed]
    exact bParse hops hn t hw hconst _ hfuel
  obtain ⟨p, hp⟩ := bCore hops hn hnan hinf t hw hconst (surfaceDepth (bsurf ops names t) + 1)
    (by omega)
  have hps : parseString (parser ops names) (btext ops names t) = .ok p := by
    unfold parseString
    rw [hmeta]
    show parseExpression (parser ops names) (bsurf ops names t) = _
    unfold parseExpression
    exact hp
  unfold renderParse
  rw [hst]
  show (parseString (parser ops names) (btext ops names t)).toOption.isSome = true
  rw [hps]
  all_goals rfl

private def cosBroadcast : NamedOp :=
  {named "cos" (fun _ => zero) with display := "cos.", pretty := "cos.", broadcast := true}
private def broadcastOps : Operators := [[cosBroadcast]]

example : CleanNames ["x1", "x2"] ∧ (["x1", "x2"] : List String).contains "NaN" = false ∧
    (["x1", "x2"] : List String).contains "Inf" = false ∧
    (Tree.branch 1 [.feature 1] : Tree Scalar).WF 2 broadcastOps.enum.nops 2 ∧
    BroadcastOps broadcastOps ∧ BroadcastConsts ["x1", "x2"] (.branch 1 [.feature 1]) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [CleanNames, plainName, asciiIdent, reservedWords]
  · simp [Tree.WF, Operators.enum, OpEnum.nops, broadcastOps]
  · intro os hos
    simp only [broadcastOps, List.mem_singleton] at hos
    subst hos
    refine ⟨by simp, ?_⟩
    intro op hop
    simp only [List.mem_singleton] at hop
    subst hop
    exact ⟨by decide, rfl, rfl⟩
  · simp [BroadcastConsts]

example : renderParse broadcastOps ["x1", "x2"] (.branch 1 [.feature 1]) =
    some ⟨"Node", .branch 1 [.feature 1]⟩ := by decide +kernel

/-- Two broadcast callables of functions both named `cos` at one degree both
print `cos.`, so `_find_operator_by_name` rejects the reparse as ambiguous
(`src/Parse.jl:325-333`); this is why `BroadcastOps` requires unique names (Q55). -/
example : renderParse [[cosBroadcast, {cosBroadcast with identity := "other_cos"}]] ["x1"]
    (.branch 1 [.feature 1]) = none := by decide +kernel

end DynExpr.StringsParse.General
