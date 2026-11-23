import DynExpr.Simplify.JFLaws

/-!
Proofs of the `combine_operators!` properties (src/Simplify.jl:32-126) for the
heap mirror `combineOps` on unshared inputs.

The heap simulation uses `Rep g a t F`: graph `g` stores the binary tree `t`
at address `a` using only addresses in the footprint `F`, with disjoint
footprints for distinct children and the parent outside its children's
footprints. Writes outside a footprint leave the stored tree intact
(`Rep.frame`), which is how `NoAlias` lets each rewrite step reason locally.
-/

namespace DynExpr.Simplify

open DynExpr

variable {T : Type}

/-! ## Heap representation of binary trees -/

/-- `g` stores `t` at `a`, using only addresses satisfying `F`. -/
private inductive Rep (g : Graph T) : Addr → Tree T → (Addr → Prop) → Prop where
  | const {a : Addr} {c : Cell T} {v : T} {F : Addr → Prop} :
      g.cells a = some c → c.degree = 0 → c.children = [] → c.constant = true →
      c.val = some v → F a → Rep g a (.const v) F
  | feature {a : Addr} {c : Cell T} {i : Nat} {F : Addr → Prop} :
      g.cells a = some c → c.degree = 0 → c.children = [] → c.constant = false →
      c.feature = i → F a → Rep g a (.feature i) F
  | unary {a : Addr} {c : Cell T} {op : Nat} {b : Addr} {t : Tree T} {F G : Addr → Prop} :
      g.cells a = some c → c.degree = 1 → c.op = op → c.children = [b] →
      Rep g b t G → (∀ x, G x → F x) → ¬ G a → F a → Rep g a (.branch op [t]) F
  | binary {a : Addr} {c : Cell T} {op : Nat} {b1 b2 : Addr} {t1 t2 : Tree T}
      {F G1 G2 : Addr → Prop} :
      g.cells a = some c → c.degree = 2 → c.op = op → c.children = [b1, b2] →
      Rep g b1 t1 G1 → Rep g b2 t2 G2 → (∀ x, G1 x → F x) → (∀ x, G2 x → F x) →
      (∀ x, G1 x → ¬ G2 x) → ¬ G1 a → ¬ G2 a → F a → Rep g a (.branch op [t1, t2]) F

namespace Rep

variable {g : Graph T} {a : Addr} {t : Tree T} {F : Addr → Prop}

private theorem mem (h : Rep g a t F) : F a := by
  cases h <;> assumption

private theorem mono {F' : Addr → Prop} (h : Rep g a t F) (hs : ∀ x, F x → F' x) :
    Rep g a t F' := by
  cases h with
  | const hc hd hch hk hv hF => exact .const hc hd hch hk hv (hs _ hF)
  | feature hc hd hch hk hi hF => exact .feature hc hd hch hk hi (hs _ hF)
  | unary hc hd hop hch hr hsub hn hF =>
    exact .unary hc hd hop hch hr (fun x hx => hs x (hsub x hx)) hn (hs _ hF)
  | binary hc hd hop hch hr1 hr2 hs1 hs2 hdj hn1 hn2 hF =>
    exact .binary hc hd hop hch hr1 hr2 (fun x hx => hs x (hs1 x hx))
      (fun x hx => hs x (hs2 x hx)) hdj hn1 hn2 (hs _ hF)

private theorem frame {g' : Graph T} (h : Rep g a t F)
    (hf : ∀ x, F x → g'.cells x = g.cells x) :
    Rep g' a t F := by
  revert hf
  induction h with
  | const hc hd hch hk hv hF =>
    intro hf; exact .const (by rw [hf _ hF]; exact hc) hd hch hk hv hF
  | feature hc hd hch hk hi hF =>
    intro hf; exact .feature (by rw [hf _ hF]; exact hc) hd hch hk hi hF
  | unary hc hd hop hch _ hsub hn hF ih =>
    intro hf
    exact .unary (by rw [hf _ hF]; exact hc) hd hop hch (ih fun x hx => hf x (hsub x hx))
      hsub hn hF
  | binary hc hd hop hch _ _ hs1 hs2 hdj hn1 hn2 hF ih1 ih2 =>
    intro hf
    exact .binary (by rw [hf _ hF]; exact hc) hd hop hch (ih1 fun x hx => hf x (hs1 x hx))
      (ih2 fun x hx => hf x (hs2 x hx)) hs1 hs2 hdj hn1 hn2 hF

end Rep

/-! ## Monadic steps of the mirror -/

private theorem ok_bind {α β : Type} (x : α) (f : α → Jl β) :
    ((Except.ok x : Jl α) >>= f) = f x := rfl

private theorem pure_ok {α : Type} (x : α) : (pure x : Jl α) = Except.ok x := rfl

private theorem iteT {α : Type} {c : Prop} [Decidable c] (h : c) (x y : α) :
    (if c then x else y) = x := by simp [h]
private theorem iteF {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (x y : α) :
    (if c then x else y) = y := by simp [h]

private theorem read_ok {g : Graph T} {a : Addr} {c : Cell T} (h : g.cells a = some c) :
    g.read a = .ok c := by
  simp [Heap.read, h]

private theorem write_ok {g : Graph T} {a : Addr} {c : Cell T} (h : g.cells a = some c)
    (v : Cell T) : ∃ g' : Graph T, g.write a v = .ok g' ∧
      ∀ x, g'.cells x = if x = a then some v else g.cells x := by
  unfold Heap.write
  split
  · simp_all
  · exact ⟨_, rfl, fun _ => rfl⟩

private theorem ne_of_mem {G : Addr → Prop} {x y : Addr} (hx : G x) (hy : ¬ G y) : y ≠ x :=
  fun h => hy (h ▸ hx)

private theorem ne_of_disj {G H : Addr → Prop} (hdj : ∀ z, G z → ¬ H z) {x y : Addr}
    (hx : G x) (hy : H y) : x ≠ y :=
  fun h => hdj x hx (h ▸ hy)

private theorem childAt_ok {c : Cell T} {i : Nat} {b : Addr} (hi : i ≠ 0)
    (h : c.children[i - 1]? = some b) : childAt c i = .ok b := by
  unfold childAt; rw [iteF hi, h]; rfl

private theorem ch1 {c : Cell T} {b : Addr} {l : List Addr} (h : c.children = b :: l) :
    childAt c 1 = .ok b := childAt_ok (by decide) (by simp [h])

private theorem ch2 {c : Cell T} {b1 b2 : Addr} (h : c.children = [b1, b2]) :
    childAt c 2 = .ok b2 := childAt_ok (by decide) (by simp [h])

private theorem childOf_ok {g : Graph T} {a : Addr} {c : Cell T} {i : Nat} {b : Addr}
    (hc : g.cells a = some c) (h : childAt c i = .ok b) : childOf g a i = .ok b := by
  simp only [childOf, read_ok hc, ok_bind, h]

private theorem isConstAt_ok {g : Graph T} {a : Addr} {c : Cell T} (hc : g.cells a = some c) :
    isConstAt g a = .ok (cellConst c) := by
  simp only [isConstAt, read_ok hc, ok_bind] <;> rfl

private theorem valOf_ok {g : Graph T} {a : Addr} {c : Cell T} {v : T}
    (hc : g.cells a = some c) (hv : c.val = some v) : valOf g a = .ok v := by
  simp only [valOf, read_ok hc, ok_bind, hv] <;> rfl

private theorem setChild_ok {g : Graph T} {a : Addr} {c : Cell T} {i : Nat} (b : Addr)
    (hc : g.cells a = some c) (hi : i = 1 ∨ i = 2) (hl : i - 1 < c.children.length) :
    ∃ g' : Graph T, setChild g a i b = .ok g' ∧
      ∀ x, g'.cells x = if x = a then some { c with children := c.children.set (i - 1) b }
        else g.cells x := by
  obtain ⟨g', hw, hg'⟩ := write_ok hc { c with children := c.children.set (i - 1) b }
  refine ⟨g', ?_, hg'⟩
  simp only [setChild, read_ok hc, ok_bind]
  rw [iteF (by omega), iteT hl, hw]

/-- `set_child!(n, b, 1)` on a binary node. -/
private theorem setChild1_ok {g : Graph T} {a : Addr} {c : Cell T} {b1 b2 : Addr} (b : Addr)
    (hc : g.cells a = some c) (hch : c.children = [b1, b2]) :
    ∃ g' : Graph T, setChild g a 1 b = .ok g' ∧
      g'.cells a = some { c with children := [b, b2] } ∧ ∀ x, x ≠ a → g'.cells x = g.cells x := by
  obtain ⟨g', hs, hg'⟩ := setChild_ok (i := 1) b hc (by omega) (by simp [hch])
  refine ⟨g', hs, ?_, fun x hx => by rw [hg', iteF hx]⟩
  rw [hg', iteT rfl]; simp [hch]

/-- `set_child!(n, b, 2)` on a binary node. -/
private theorem setChild2_ok {g : Graph T} {a : Addr} {c : Cell T} {b1 b2 : Addr} (b : Addr)
    (hc : g.cells a = some c) (hch : c.children = [b1, b2]) :
    ∃ g' : Graph T, setChild g a 2 b = .ok g' ∧
      g'.cells a = some { c with children := [b1, b] } ∧ ∀ x, x ≠ a → g'.cells x = g.cells x := by
  obtain ⟨g', hs, hg'⟩ := setChild_ok (i := 2) b hc (by omega) (by simp [hch])
  refine ⟨g', hs, ?_, fun x hx => by rw [hg', iteF hx]⟩
  rw [hg', iteT rfl]; simp [hch]

/-- `set_child!(n, b, 1)` on a unary node. -/
private theorem setChildU_ok {g : Graph T} {a : Addr} {c : Cell T} {b1 : Addr} (b : Addr)
    (hc : g.cells a = some c) (hch : c.children = [b1]) :
    ∃ g' : Graph T, setChild g a 1 b = .ok g' ∧
      g'.cells a = some { c with children := [b] } ∧ ∀ x, x ≠ a → g'.cells x = g.cells x := by
  obtain ⟨g', hs, hg'⟩ := setChild_ok (i := 1) b hc (by omega) (by simp [hch])
  refine ⟨g', hs, ?_, fun x hx => by rw [hg', iteF hx]⟩
  rw [hg', iteT rfl]; simp [hch]

private theorem binop_ok [Add T] [Mul T] [Sub T] {o : CEnum T} {op : Nat} {b : BinOp T}
    (h0 : op ≠ 0) (hb : o.bin[op - 1]? = some b) : o.binop op = .ok b := by
  unfold CEnum.binop; rw [iteF h0, hb]; rfl

private theorem isC_true {t : Tree T} (h : isC t = true) : ∃ v, t = .const v := by
  cases t <;> simp_all [isC, cval?]

private theorem cval_none {t : Tree T} (h : isC t = false) : cval? t = none := by
  cases t <;> simp_all [isC, cval?]

private theorem isC_const (v : T) : isC (Tree.const v) = true := rfl
private theorem isC_feature (i : Nat) : isC (Tree.feature i : Tree T) = false := rfl
private theorem isC_branch (op : Nat) (cs : List (Tree T)) : isC (Tree.branch op cs) = false := rfl
private theorem cval_const (v : T) : cval? (Tree.const v) = some v := rfl
private theorem cval_feature (i : Nat) : cval? (Tree.feature i : Tree T) = none := rfl
private theorem cval_branch (op : Nat) (cs : List (Tree T)) : cval? (Tree.branch op cs) = none :=
  rfl

namespace Rep

variable {g : Graph T} {a : Addr} {t : Tree T} {F : Addr → Prop}

private theorem isConst (h : Rep g a t F) : isConstAt g a = .ok (isC t) := by
  cases h with
  | const hc hd _ hk => rw [isConstAt_ok hc]; simp [cellConst, isC, cval?, hd, hk]
  | feature hc hd _ hk => rw [isConstAt_ok hc]; simp [cellConst, isC, cval?, hd, hk]
  | unary hc hd => rw [isConstAt_ok hc]; simp [cellConst, isC, cval?, hd]
  | binary hc hd => rw [isConstAt_ok hc]; simp [cellConst, isC, cval?, hd]

private theorem valOf {v : T} (h : Rep g a (.const v) F) :
    DynExpr.Simplify.valOf g a = .ok v := by
  cases h with
  | const hc _ _ _ hv => exact valOf_ok hc hv

/-- `node.val = w` on a constant leaf. -/
private theorem setVal_ok {v : T} (h : Rep g a (.const v) F) (w : T) :
    ∃ g' : Graph T, setVal g a w = .ok g' ∧ Rep g' a (.const w) F ∧
      ∀ x, x ≠ a → g'.cells x = g.cells x := by
  cases h with
  | @const _ c _ _ hc hd hch hk _ hF =>
    obtain ⟨g', hw, hg'⟩ := write_ok hc { c with val := some w }
    refine ⟨g', ?_, .const (c := { c with val := some w }) (by rw [hg', iteT rfl]) hd hch hk
      rfl hF, fun x hx => by rw [hg', iteF hx]⟩
    simp only [DynExpr.Simplify.setVal, read_ok hc, ok_bind, hw]

private theorem branch2 {op : Nat} {x y : Tree T} (h : Rep g a (.branch op [x, y]) F) :
    ∃ c : Cell T, g.cells a = some c ∧ c.degree = 2 ∧ c.op = op := by
  cases h with
  | binary hc hd hop => exact ⟨_, hc, hd, hop⟩

end Rep

/-! ## Commutative block -/

section Comm

variable [Add T] [Mul T] [Sub T]

/-- The commutative block after the constant was moved to the right
(src/Simplify.jl:63-79). -/
private def commRest (o : CEnum T) (g : Graph T) (tree : Addr) (op : Nat) :
    Jl (Addr × Graph T) := do
  let topconstant ← valOf g (← childOf g tree 2)
  let below ← childOf g tree 1
  let bc ← g.read below
  if bc.degree = 2 ∧ bc.op = op then
    let b1 ← childAt bc 1
    if ← isConstAt g b1 then
      let f ← o.binop op
      let g ← setVal g b1 (f.eval (← valOf g b1) topconstant)
      return (below, g)
    else
      let b2 ← childAt bc 2
      if ← isConstAt g b2 then
        let f ← o.binop op
        let g ← setVal g b2 (f.eval (← valOf g b2) topconstant)
        return (below, g)
      else return (tree, g)
  else return (tree, g)

private theorem commBlock_eq (o : CEnum T) (g : Graph T) (tree : Addr) :
    commBlock o g tree = (do
      let c ← g.read tree
      let g ← if ← isConstAt g (← childAt c 1) then do
          let tmp ← childOf g tree 2
          let g ← setChild g tree 2 (← childOf g tree 1)
          setChild g tree 1 tmp
        else pure g
      commRest o g tree c.op) := rfl

/-- The pure commutative block after the constant was moved to the right. -/
private def commCore (op : Nat) (b : BinOp T) (l r : Tree T) : Tree T :=
  match cval? r, l with
  | some k, .branch op2 [a, c] =>
    if op2 = op then
      match cval? a, cval? c with
      | some va, _ => .branch op2 [.const (b.eval va k), c]
      | none, some vc => .branch op2 [a, .const (b.eval vc k)]
      | none, none => .branch op [l, r]
    else .branch op [l, r]
  | _, _ => .branch op [l, r]

/-- The commutative block returns the lower node (`tree = below`,
src/Simplify.jl:68,73) after the constant was moved to the right. -/
private def coreRepl (op : Nat) (l r : Tree T) : Bool :=
  match cval? r, l with
  | some _, .branch op2 [a, c] => op2 == op && (isC a || isC c)
  | _, _ => false

private theorem commPure_eq (op : Nat) (b : BinOp T) (l r : Tree T) :
    commPure op b l r = if isC l then commCore op b r l else commCore op b l r := by
  unfold commPure; cases isC l <;> rfl

private theorem commCore_shape (op : Nat) (b : BinOp T) (l r : Tree T) :
    ∃ x y, commCore op b l r = .branch op [x, y] := by
  unfold commCore
  split
  · split
    · rename_i h; subst h
      split <;> exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private theorem commPure_shape (op : Nat) (b : BinOp T) (l r : Tree T) :
    ∃ x y, commPure op b l r = .branch op [x, y] := by
  rw [commPure_eq]; split <;> exact commCore_shape _ _ _ _

private theorem commRest_ok (o : CEnum T) {g : Graph T} {a : Addr} {c : Cell T} {op : Nat}
    {b1 b2 : Addr} {L R : Tree T} {F G1 G2 : Addr → Prop} {bop : BinOp T}
    (hc : g.cells a = some c) (hch : c.children = [b1, b2])
    (h1 : Rep g b1 L G1) (h2 : Rep g b2 R G2) (hs1 : ∀ x, G1 x → F x)
    (hb : o.binop op = .ok bop) (hR : isC R = true) (hbase : Rep g a (.branch op [L, R]) F) :
    ∃ r g', commRest o g a op = .ok (r, g') ∧ Rep g' r (commCore op bop L R) F ∧
      (∀ x, ¬ F x → g'.cells x = g.cells x) ∧ (coreRepl op L R = false → r = a) := by
  obtain ⟨k, rfl⟩ := isC_true hR
  have e2 : childOf g a 2 = .ok b2 := childOf_ok hc (ch2 hch)
  have e1 : childOf g a 1 = .ok b1 := childOf_ok hc (ch1 hch)
  have ek : valOf g b2 = .ok k := h2.valOf
  cases h1 with
  | const hc1 hd1 =>
    refine ⟨a, g, ?_, by simpa [commCore, cval_const] using hbase, fun _ _ => rfl, fun _ => rfl⟩
    simp [commRest, e2, ok_bind, pure_ok, ek, e1, read_ok hc1, hd1]
  | feature hc1 hd1 =>
    refine ⟨a, g, ?_, by simpa [commCore, cval_const] using hbase, fun _ _ => rfl, fun _ => rfl⟩
    simp [commRest, e2, ok_bind, pure_ok, ek, e1, read_ok hc1, hd1]
  | unary hc1 hd1 =>
    refine ⟨a, g, ?_, by simpa [commCore, cval_const] using hbase, fun _ _ => rfl, fun _ => rfl⟩
    simp [commRest, e2, ok_bind, pure_ok, ek, e1, read_ok hc1, hd1]
  | @binary _ cb op2 d1 d2 x y _ H1 H2 hcb hdb hopb hchb hx hy hsx hsy hdxy hnx hny hFb =>
    have eb := read_ok hcb
    by_cases hop2 : op2 = op
    · subst hop2
      have ex := hx.isConst
      have ey := hy.isConst
      cases hxc : isC x
      · cases hyc : isC y
        · refine ⟨a, g, ?_, ?_, fun _ _ => rfl, fun _ => rfl⟩
          · simp [commRest, e2, ok_bind, pure_ok, ek, e1, eb, hdb, hopb, ch1 hchb, ch2 hchb,
              ex, ey, hxc, hyc]
          · simpa [commCore, cval_const, cval_none hxc, cval_none hyc] using hbase
        · obtain ⟨vc, rfl⟩ := isC_true hyc
          obtain ⟨g1, hsv, hry, hfr⟩ := hy.setVal_ok (bop.eval vc k)
          refine ⟨b1, g1, ?_, ?_, ?_, fun h => by simp [coreRepl, cval_const, isC_const] at h⟩
          · simp [commRest, e2, ok_bind, pure_ok, ek, e1, eb, hdb, hopb, ch1 hchb, ch2 hchb,
              ex, ey, hxc, isC_const, hb, hy.valOf, hsv]
          · simp only [commCore, cval_const, cval_none hxc, iteT]
            exact (Rep.binary (by rw [hfr b1 (ne_of_mem hy.mem hny)]; exact hcb) hdb hopb
              hchb (hx.frame fun z hz => hfr z (ne_of_disj hdxy hz hy.mem)) hry
              hsx hsy hdxy hnx hny hFb).mono hs1
          · exact fun z hz => hfr z (ne_of_mem (hs1 _ (hsy _ hy.mem)) hz)
      · obtain ⟨va, rfl⟩ := isC_true hxc
        obtain ⟨g1, hsv, hrx, hfr⟩ := hx.setVal_ok (bop.eval va k)
        refine ⟨b1, g1, ?_, ?_, ?_, fun h => by simp [coreRepl, cval_const, isC_const] at h⟩
        · simp [commRest, e2, ok_bind, pure_ok, ek, e1, eb, hdb, hopb, ch1 hchb,
            ex, isC_const, hb, hx.valOf, hsv]
        · simp only [commCore, cval_const, iteT]
          exact (Rep.binary (by rw [hfr b1 (ne_of_mem hx.mem hnx)]; exact hcb) hdb hopb
            hchb hrx (hy.frame fun z hz => hfr z (ne_of_disj hdxy hx.mem hz).symm)
            hsx hsy hdxy hnx hny hFb).mono hs1
        · exact fun z hz => hfr z (ne_of_mem (hs1 _ (hsx _ hx.mem)) hz)
    · refine ⟨a, g, ?_, by simpa [commCore, cval_const, hop2] using hbase, fun _ _ => rfl,
        fun _ => rfl⟩
      simp [commRest, e2, ok_bind, pure_ok, ek, e1, eb, hdb, hopb, hop2]

private theorem commBlock_ok (o : CEnum T) {g : Graph T} {a : Addr} {c : Cell T} {op : Nat}
    {b1 b2 : Addr} {l r : Tree T} {F G1 G2 : Addr → Prop} {bop : BinOp T}
    (hc : g.cells a = some c) (hd : c.degree = 2) (hop : c.op = op)
    (hch : c.children = [b1, b2]) (h1 : Rep g b1 l G1) (h2 : Rep g b2 r G2)
    (hs1 : ∀ x, G1 x → F x) (hs2 : ∀ x, G2 x → F x) (hdj : ∀ x, G1 x → ¬ G2 x)
    (hn1 : ¬ G1 a) (hn2 : ¬ G2 a) (hF : F a)
    (hb : o.binop op = .ok bop) (htlc : (isC l || isC r) = true) :
    ∃ r' g', commBlock o g a = .ok (r', g') ∧ Rep g' r' (commPure op bop l r) F ∧
      (∀ x, ¬ F x → g'.cells x = g.cells x) ∧
      ((if isC l then coreRepl op r l else coreRepl op l r) = false → r' = a) := by
  have ec1 := h1.isConst
  rw [commBlock_eq, commPure_eq]
  cases hl : isC l
  · have hr : isC r = true := by simpa [hl] using htlc
    obtain ⟨r', g', he, hrep, hfr, hra⟩ := commRest_ok o hc hch h1 h2 hs1 hb hr
      (.binary hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF)
    refine ⟨r', g', ?_, by simpa using hrep, hfr, fun h => hra (by simpa [hl] using h)⟩
    simp [read_ok hc, ok_bind, pure_ok, ch1 hch, ec1, hl, hop, he]
  · obtain ⟨g1, hw1, hc1, hf1⟩ := setChild2_ok b1 hc hch
    obtain ⟨g2, hw2, hc2, hf2⟩ := setChild1_ok b2 hc1 rfl
    have hfa : ∀ x, x ≠ a → g2.cells x = g.cells x := fun x hx => by rw [hf2 x hx, hf1 x hx]
    have h1' : Rep g2 b1 l G1 := h1.frame fun x hx => hfa x (fun h => hn1 (h ▸ hx))
    have h2' : Rep g2 b2 r G2 := h2.frame fun x hx => hfa x (fun h => hn2 (h ▸ hx))
    obtain ⟨r', g', he, hrep, hfr, hra⟩ := commRest_ok o hc2 rfl h2' h1' hs2 hb hl
      (.binary hc2 hd hop rfl h2' h1' hs2 hs1 (fun x h2x h1x => hdj x h1x h2x) hn2 hn1 hF)
    refine ⟨r', g', ?_, by simpa using hrep,
      fun x hx => by rw [hfr x hx, hfa x (fun h => hx (h ▸ hF))],
      fun h => hra (by simpa [hl] using h)⟩
    simp [read_ok hc, ok_bind, pure_ok, ch1 hch, ec1, hl, hop, childOf_ok hc (ch2 hch),
      childOf_ok hc (ch1 hch), hw1, hw2, he]

omit [Mul T] in
private theorem subBlock_ok {g : Graph T} {a : Addr} {c : Cell T} {op : Nat}
    {b1 b2 : Addr} {l r : Tree T} {F G1 G2 : Addr → Prop}
    (hc : g.cells a = some c) (hd : c.degree = 2) (hop : c.op = op)
    (hch : c.children = [b1, b2]) (h1 : Rep g b1 l G1) (h2 : Rep g b2 r G2)
    (hs1 : ∀ x, G1 x → F x) (hs2 : ∀ x, G2 x → F x) (hdj : ∀ x, G1 x → ¬ G2 x)
    (hn1 : ¬ G1 a) (hn2 : ¬ G2 a) (hF : F a) (htlc : (isC l || isC r) = true) :
    ∃ r' g', subBlock g a = .ok (r', g') ∧ Rep g' r' (subPure op l r) F ∧
      (∀ x, ¬ F x → g'.cells x = g.cells x) ∧ r' = a := by
  have hbase : Rep g a (.branch op [l, r]) F := .binary hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF
  have ea := read_ok hc
  have e1 := ch1 hch
  have e2 := ch2 hch
  have ec1 := h1.isConst
  have ca1 : childOf g a 1 = .ok b1 := childOf_ok hc e1
  have ca2 : childOf g a 2 = .ok b2 := childOf_ok hc e2
  have na1 : ∀ z, G1 z → z ≠ a := fun z hz => (ne_of_mem hz hn1).symm
  have na2 : ∀ z, G2 z → z ≠ a := fun z hz => (ne_of_mem hz hn2).symm
  have m1 := h1.mem
  have m2 := h2.mem
  cases hl : isC l
  · -- `((const - var) - const)` and `((var - const) - const)` (src/Simplify.jl:105-121)
    have hr : isC r = true := by simpa [hl] using htlc
    obtain ⟨vr, rfl⟩ := isC_true hr
    have evr := h2.valOf
    cases h1 with
    | const => simp [isC_const] at hl
    | feature hc1 hd1 =>
      refine ⟨a, g, ?_, by simpa [subPure, cval_const, cval_feature] using hbase,
        fun _ _ => rfl, rfl⟩
      simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, read_ok hc1, hd1]
    | unary hc1 hd1 =>
      refine ⟨a, g, ?_, by simpa [subPure, cval_const, cval_branch] using hbase,
        fun _ _ => rfl, rfl⟩
      simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, read_ok hc1, hd1]
    | @binary _ cl op2 d1 d2 x y _ H1 H2 hcl hdl hopl hchl hx hy hsx hsy hdxy hnx hny hFl =>
      have el := read_ok hcl
      have ex := hx.isConst
      have ey := hy.isConst
      have cb1 : childOf g b1 1 = .ok d1 := childOf_ok hcl (ch1 hchl)
      have cb2 : childOf g b1 2 = .ok d2 := childOf_ok hcl (ch2 hchl)
      by_cases hop2 : op = op2
      · subst hop2
        cases hxc : isC x
        · cases hyc : isC y
          · refine ⟨a, g, ?_, ?_, fun _ _ => rfl, rfl⟩
            · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, el, hdl, hop, hopl,
                ch1 hchl, ch2 hchl, ex, ey, hxc, hyc]
            · simpa [subPure, cval_const, cval_branch, cval_none hxc, cval_none hyc] using hbase
          · obtain ⟨v2, rfl⟩ := isC_true hyc
            obtain ⟨g1, hw1, hc1', hf1⟩ := setChild1_ok d1 hc hch
            have h2a : Rep g1 b2 (.const vr) G2 := h2.frame fun z hz => hf1 z (na2 z hz)
            obtain ⟨g2, hw2, hr2, hf2⟩ := h2a.setVal_ok (vr + v2)
            refine ⟨a, g2, ?_, ?_, ?_, rfl⟩
            · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, el, hdl, hop, hopl,
                ch1 hchl, ch2 hchl, ex, ey, hxc, isC_const, evr, hy.valOf, ca1, cb1, hw1,
                childOf_ok hc1' (ch2 rfl), hw2]
            · simp only [subPure, cval_branch, cval_const, cval_none hxc, iteT]
              exact .binary ((hf2 a (na2 b2 m2).symm).trans hc1') hd hop rfl
                (hx.frame fun z hz => by
                  rw [hf2 z (ne_of_disj hdj (hsx z hz) m2), hf1 z (na1 z (hsx z hz))])
                hr2 (fun z hz => hs1 z (hsx z hz)) hs2 (fun z hz => hdj z (hsx z hz))
                (fun h => hn1 (hsx a h)) hn2 hF
            · intro z hz
              rw [hf2 z (ne_of_mem (hs2 _ m2) hz), hf1 z (ne_of_mem hF hz)]
        · obtain ⟨v1, rfl⟩ := isC_true hxc
          obtain ⟨g1, hw1, hc1', hf1⟩ := setChild2_ok d2 hc hch
          obtain ⟨g2, hw2, hc2', hf2⟩ := setChild1_ok b2 hc1' rfl
          have h2a : Rep g2 b2 (.const vr) G2 := h2.frame fun z hz => by
            rw [hf2 z (na2 z hz), hf1 z (na2 z hz)]
          obtain ⟨g3, hw3, hr3, hf3⟩ := h2a.setVal_ok (v1 - vr)
          refine ⟨a, g3, ?_, ?_, ?_, rfl⟩
          · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, el, hdl, hop, hopl,
              ch1 hchl, ex, isC_const, evr, hx.valOf, ca1, cb2, hw1, hw2,
              childOf_ok hc2' (ch1 rfl), hw3]
          · simp only [subPure, cval_branch, cval_const, iteT]
            exact .binary ((hf3 a (na2 b2 m2).symm).trans hc2') hd hop rfl hr3
              (hy.frame fun z hz => by
                rw [hf3 z (ne_of_disj hdj (hsy z hz) m2), hf2 z (na1 z (hsy z hz)),
                  hf1 z (na1 z (hsy z hz))])
              hs2 (fun z hz => hs1 z (hsy z hz)) (fun z h2z hyz => hdj z (hsy z hyz) h2z)
              hn2 (fun h => hn1 (hsy a h)) hF
          · intro z hz
            rw [hf3 z (ne_of_mem (hs2 _ m2) hz), hf2 z (ne_of_mem hF hz),
              hf1 z (ne_of_mem hF hz)]
      · refine ⟨a, g, ?_, by simpa [subPure, cval_const, cval_branch, hop2] using hbase,
          fun _ _ => rfl, rfl⟩
        simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, hl, el, hdl, hop, hopl, hop2]
  · -- `(const - (const - var))` and `(const - (var - const))` (src/Simplify.jl:85-102)
    obtain ⟨vl, rfl⟩ := isC_true hl
    have evl := h1.valOf
    cases h2 with
    | const hc2 hd2 =>
      refine ⟨a, g, ?_, by simpa [subPure, cval_const] using hbase, fun _ _ => rfl, rfl⟩
      simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, read_ok hc2, hd2]
    | feature hc2 hd2 =>
      refine ⟨a, g, ?_, by simpa [subPure, cval_const] using hbase, fun _ _ => rfl, rfl⟩
      simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, read_ok hc2, hd2]
    | unary hc2 hd2 =>
      refine ⟨a, g, ?_, by simpa [subPure, cval_const] using hbase, fun _ _ => rfl, rfl⟩
      simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, read_ok hc2, hd2]
    | @binary _ cr op2 d1 d2 x y _ H1 H2 hcr hdr hopr hchr hx hy hsx hsy hdxy hnx hny hFr =>
      have er := read_ok hcr
      have ex := hx.isConst
      have ey := hy.isConst
      have cb1 : childOf g b2 1 = .ok d1 := childOf_ok hcr (ch1 hchr)
      have cb2 : childOf g b2 2 = .ok d2 := childOf_ok hcr (ch2 hchr)
      by_cases hop2 : op = op2
      · subst hop2
        cases hxc : isC x
        · cases hyc : isC y
          · refine ⟨a, g, ?_, ?_, fun _ _ => rfl, rfl⟩
            · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, er, hdr, hop, hopr,
                ch1 hchr, ch2 hchr, ex, ey, hxc, hyc]
            · simpa [subPure, cval_const, cval_none hxc, cval_none hyc] using hbase
          · obtain ⟨v2, rfl⟩ := isC_true hyc
            obtain ⟨g1, hw1, hc1', hf1⟩ := setChild2_ok d1 hc hch
            have h1a : Rep g1 b1 (.const vl) G1 := h1.frame fun z hz => hf1 z (na1 z hz)
            obtain ⟨g2, hw2, hr2, hf2⟩ := h1a.setVal_ok (vl + v2)
            refine ⟨a, g2, ?_, ?_, ?_, rfl⟩
            · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, er, hdr, hop, hopr,
                ch1 hchr, ch2 hchr, ex, ey, hxc, evl, hy.valOf, ca2, cb1, hw1,
                childOf_ok hc1' (ch1 rfl), hw2]
            · simp only [subPure, cval_const, cval_none hxc, iteT]
              exact .binary ((hf2 a (na1 b1 m1).symm).trans hc1') hd hop rfl hr2
                (hx.frame fun z hz => by
                  rw [hf2 z ((ne_of_disj hdj m1 (hsx z hz)).symm), hf1 z (na2 z (hsx z hz))])
                hs1 (fun z hz => hs2 z (hsx z hz)) (fun z h1z hxz => hdj z h1z (hsx z hxz))
                hn1 (fun h => hn2 (hsx a h)) hF
            · intro z hz
              rw [hf2 z (ne_of_mem (hs1 _ m1) hz), hf1 z (ne_of_mem hF hz)]
        · obtain ⟨v1, rfl⟩ := isC_true hxc
          obtain ⟨g1, hw1, hc1', hf1⟩ := setChild1_ok d2 hc hch
          obtain ⟨g2, hw2, hc2', hf2⟩ := setChild2_ok b1 hc1' rfl
          have h1a : Rep g2 b1 (.const vl) G1 := h1.frame fun z hz => by
            rw [hf2 z (na1 z hz), hf1 z (na1 z hz)]
          obtain ⟨g3, hw3, hr3, hf3⟩ := h1a.setVal_ok (v1 - vl)
          refine ⟨a, g3, ?_, ?_, ?_, rfl⟩
          · simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, er, hdr, hop, hopr,
              ch1 hchr, ex, evl, hx.valOf, ca2, cb2, hw1, hw2,
              childOf_ok hc2' (ch2 rfl), hw3]
          · simp only [subPure, cval_const, iteT]
            exact .binary ((hf3 a (na1 b1 m1).symm).trans hc2') hd hop rfl
              (hy.frame fun z hz => by
                rw [hf3 z ((ne_of_disj hdj m1 (hsy z hz)).symm), hf2 z (na2 z (hsy z hz)),
                  hf1 z (na2 z (hsy z hz))])
              hr3 (fun z hz => hs2 z (hsy z hz)) hs1 (fun z hyz h1z => hdj z h1z (hsy z hyz))
              (fun h => hn2 (hsy a h)) hn1 hF
          · intro z hz
            rw [hf3 z (ne_of_mem (hs1 _ m1) hz), hf2 z (ne_of_mem hF hz),
              hf1 z (ne_of_mem hF hz)]
      · refine ⟨a, g, ?_, by simpa [subPure, cval_const, hop2] using hbase, fun _ _ => rfl,
          rfl⟩
        simp [subBlock, ea, ok_bind, pure_ok, e1, e2, ec1, isC_const, er, hdr, hop, hopr, hop2]

private theorem tlc_ok (p q : Bool) :
    (if p = true then (Except.ok true : Jl Bool) else Except.ok q) = Except.ok (p || q) := by
  cases p <;> rfl

omit [Add T] [Mul T] [Sub T] in
private theorem commReplacesAt_eq (o : CEnum T) {op : Nat} {b : BinOp T} (h0 : op ≠ 0)
    (hb : o.bin[op - 1]? = some b) (l r : Tree T) :
    commReplacesAt o op l r = ((b.isComm && (isC l || isC r)) &&
      (if isC l then coreRepl op r l else coreRepl op l r)) := by
  unfold commReplacesAt
  rw [iteF h0, hb]
  dsimp only
  cases b.isComm <;> cases isC l <;> cases isC r <;> rfl

/-- `rewrite` at a binary node whose children store `l` and `r`. -/
private theorem rewrite_ok (o : CEnum T) {g : Graph T} {a : Addr} {c : Cell T} {op : Nat}
    {b1 b2 : Addr} {l r : Tree T} {F G1 G2 : Addr → Prop} {bop : BinOp T}
    (hc : g.cells a = some c) (hd : c.degree = 2) (hop : c.op = op)
    (hch : c.children = [b1, b2]) (h1 : Rep g b1 l G1) (h2 : Rep g b2 r G2)
    (hs1 : ∀ x, G1 x → F x) (hs2 : ∀ x, G2 x → F x) (hdj : ∀ x, G1 x → ¬ G2 x)
    (hn1 : ¬ G1 a) (hn2 : ¬ G2 a) (hF : F a)
    (h0 : op ≠ 0) (hbin : o.bin[op - 1]? = some bop) :
    ∃ r' g', rewrite o g a = .ok (r', g') ∧ Rep g' r' (rewritePure o op l r) F ∧
      (∀ x, ¬ F x → g'.cells x = g.cells x) ∧ (commReplacesAt o op l r = false → r' = a) := by
  have hb : o.binop op = .ok bop := binop_ok h0 hbin
  have ec1 := h1.isConst
  have ec2 := h2.isConst
  have ea := read_ok hc
  have hpure : rewritePure o op l r =
      if (bop.isComm && (isC l || isC r)) = true then commPure op bop l r
      else if (bop.isSub && (isC l || isC r)) = true then subPure op l r
      else .branch op [l, r] := by
    unfold rewritePure; rw [iteF h0, hbin]
  rw [hpure]
  cases htl : (isC l || isC r)
  · have hlr : isC l = false ∧ isC r = false := by simpa using htl
    refine ⟨a, g, ?_, ?_, fun _ _ => rfl, fun _ => rfl⟩
    · simp [rewrite, ea, ok_bind, pure_ok, hd, ch1 hch, ch2 hch, ec1, ec2, hlr.1, hlr.2, hop,
        hb]
    · simpa using Rep.binary hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF
  · cases hcomm : bop.isComm
    · cases hsub : bop.isSub
      · refine ⟨a, g, ?_, ?_, fun _ _ => rfl, fun _ => rfl⟩
        · simp [rewrite, ea, ok_bind, pure_ok, hd, ch1 hch, ch2 hch, ec1, ec2, hop,
            hb, hcomm, hsub]
        · simpa using Rep.binary hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF
      · obtain ⟨r', g', he, hrep, hfr, hra⟩ :=
          subBlock_ok hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF htl
        refine ⟨r', g', ?_, by simpa using hrep, hfr, fun _ => hra⟩
        simp [rewrite, ea, ok_bind, pure_ok, hd, ch1 hch, ch2 hch, ec1, ec2, hop,
          hb, hcomm, hsub, he] <;> intro h1 h2 <;> simp [h1, h2] at htl
    · have hsub : bop.isSub = false := by
        cases bop <;> simp_all [BinOp.isComm, BinOp.isSub]
      obtain ⟨r', g', he, hrep, hfr, hra⟩ :=
        commBlock_ok o hc hd hop hch h1 h2 hs1 hs2 hdj hn1 hn2 hF hb htl
      obtain ⟨x, y, hxy⟩ := commPure_shape op bop l r
      have hrep' := hrep
      rw [hxy] at hrep'
      obtain ⟨c', hc', hd', hop'⟩ := hrep'.branch2
      refine ⟨r', g', ?_, by simpa using hrep, hfr, fun h => hra (by
        rw [commReplacesAt_eq o h0 hbin] at h; simpa [hcomm, htl] using h)⟩
      simp [rewrite, ea, ok_bind, pure_ok, hd, ch1 hch, ch2 hch, ec1, ec2, hop,
        hb, hcomm, he, read_ok hc', hd', hop', hsub] <;> intro h1 h2 <;> simp [h1, h2] at htl

/-- `rewrite` leaves a unary node unchanged. -/
private theorem rewrite_unary (o : CEnum T) {g : Graph T} {a : Addr} {c : Cell T}
    (hc : g.cells a = some c) (hd : c.degree = 1) : rewrite o g a = .ok (a, g) := by
  simp [rewrite, read_ok hc, ok_bind, pure_ok, hd]

/-- Heap simulation: `combineOps` computes `combinePure` in place, writing only
inside the footprint. -/
private theorem sim (o : CEnum T) {nf : Nat} : ∀ (fuel : Nat) (g : Graph T) (a : Addr)
    (t : Tree T) (F : Addr → Prop), Rep g a t F → t.WF 2 o.nops nf → t.depth ≤ fuel →
    ∃ r g', combineOps o fuel g a = .ok (r, g') ∧ Rep g' r (combinePure o t) F ∧
      (∀ x, ¬ F x → g'.cells x = g.cells x) ∧ (commReplaces o t = false → r = a)
  | 0, _, _, t, _, _, _, hdep => by have := Tree.depth_pos t; omega
  | fuel + 1, g, a, t, F, h, hw, hdep => by
    cases h with
    | const hc hd hch hk hv hF =>
      refine ⟨a, g, ?_, ?_, fun _ _ => rfl, fun _ => rfl⟩
      · simp [combineOps, read_ok hc, ok_bind, pure_ok, hd]
      · simp only [combinePure]; exact .const hc hd hch hk hv hF
    | feature hc hd hch hk hi hF =>
      refine ⟨a, g, ?_, ?_, fun _ _ => rfl, fun _ => rfl⟩
      · simp [combineOps, read_ok hc, ok_bind, pure_ok, hd]
      · simp only [combinePure]; exact .feature hc hd hch hk hi hF
    | @unary _ c op b t1 _ G hc hd hop hch hr hs hn hF =>
      simp only [Tree.WF] at hw
      have hw1 : t1.WF 2 o.nops nf := hw.2.2 t1 (by simp)
      have hd1 : t1.depth ≤ fuel := by simp [Tree.depth] at hdep; omega
      obtain ⟨r1, g1, he1, hr1, hf1, -⟩ := sim o fuel g b t1 G hr hw1 hd1
      obtain ⟨g2, hw2, hc2, hf2⟩ := setChildU_ok r1 ((hf1 a hn).trans hc) hch
      refine ⟨a, g2, ?_, ?_, ?_, fun _ => rfl⟩
      · simp [combineOps, read_ok hc, ok_bind, pure_ok, hd, ch1 hch, he1, hw2,
          rewrite_unary o hc2 hd]
      · simp only [combinePure]
        exact .unary hc2 hd hop rfl (hr1.frame fun z hz => hf2 z (ne_of_mem hz hn).symm) hs hn hF
      · intro z hz; rw [hf2 z (ne_of_mem hF hz), hf1 z (fun h => hz (hs z h))]
    | @binary _ c op b1 b2 t1 t2 _ G1 G2 hc hd hop hch hr1 hr2 hs1 hs2 hdj hn1 hn2 hF =>
      simp only [Tree.WF] at hw
      have hw1 : t1.WF 2 o.nops nf := hw.2.2 t1 (by simp)
      have hw2 : t2.WF 2 o.nops nf := hw.2.2 t2 (by simp)
      have hm1 := Nat.le_max_left t1.depth t2.depth
      have hm2 := Nat.le_max_right t1.depth t2.depth
      have hd1 : t1.depth ≤ fuel := by simp [Tree.depth] at hdep; omega
      have hd2 : t2.depth ≤ fuel := by simp [Tree.depth] at hdep; omega
      have h0 : op ≠ 0 := by omega
      have hlt : op - 1 < o.bin.length := by
        have := hw.2.1.2.1; simp [CEnum.nops] at this; omega
      have hbin : o.bin[op - 1]? = some o.bin[op - 1] := List.getElem?_eq_getElem hlt
      have na1 : ∀ z, G1 z → z ≠ a := fun z hz => (ne_of_mem hz hn1).symm
      have na2 : ∀ z, G2 z → z ≠ a := fun z hz => (ne_of_mem hz hn2).symm
      obtain ⟨r1, g1, he1, hq1, hf1, -⟩ := sim o fuel g b1 t1 G1 hr1 hw1 hd1
      obtain ⟨g2, hx2, hc2, hf2⟩ := setChild1_ok r1 ((hf1 a hn1).trans hc) hch
      have hr2' : Rep g2 b2 t2 G2 := hr2.frame fun z hz => by
        rw [hf2 z (na2 z hz), hf1 z (fun h => hdj z h hz)]
      obtain ⟨r2, g3, he2, hq2, hf3, -⟩ := sim o fuel g2 b2 t2 G2 hr2' hw2 hd2
      obtain ⟨g4, hx4, hc4, hf4⟩ := setChild2_ok r2 ((hf3 a hn2).trans hc2) rfl
      have hq1' : Rep g4 r1 (combinePure o t1) G1 := hq1.frame fun z hz => by
        rw [hf4 z (na1 z hz), hf3 z (hdj z hz), hf2 z (na1 z hz)]
      have hq2' : Rep g4 r2 (combinePure o t2) G2 := hq2.frame fun z hz => hf4 z (na2 z hz)
      obtain ⟨r', g5, he5, hrep, hf5, hra⟩ :=
        rewrite_ok o hc4 hd hop rfl hq1' hq2' hs1 hs2 hdj hn1 hn2 hF h0 hbin
      refine ⟨r', g5, ?_, ?_, ?_, fun h => hra (by simp only [commReplaces] at h; exact h)⟩
      · simp [combineOps, read_ok hc, ok_bind, pure_ok, hd, ch1 hch, he1, hx2,
          childOf_ok hc2 (ch2 rfl), he2, hx4, he5]
      · simp only [combinePure]; exact hrep
      · intro z hz
        rw [hf5 z hz, hf4 z (ne_of_mem hF hz), hf3 z (fun h => hz (hs2 z h)),
          hf2 z (ne_of_mem hF hz), hf1 z (fun h => hz (hs1 z h))]

end Comm

/-! ## From `unfold` and `NoAlias` to `Rep`, and back -/

private theorem path_inv {g : Graph T} {a z : Addr} {p : List Nat} {c : Cell T}
    (hp : Graph.Path g a p z) (hc : g.cells a = some c) :
    (p = [] ∧ z = a) ∨ ∃ i b q, c.children[i]? = some b ∧ p = i :: q ∧ Graph.Path g b q z := by
  cases hp with
  | nil => exact .inl ⟨rfl, rfl⟩
  | cons hcell hget hq => rw [hc] at hcell; cases hcell; exact .inr ⟨_, _, _, hget, rfl, hq⟩

private theorem child1 {c : Cell T} {b1 b : Addr} {i : Nat} (hch : c.children = [b1])
    (hget : c.children[i]? = some b) : i = 0 ∧ b = b1 := by
  rw [hch] at hget; rcases i with _ | i <;> simp at hget; exact ⟨rfl, hget.symm⟩

private theorem child2 {c : Cell T} {b1 b2 b : Addr} {i : Nat} (hch : c.children = [b1, b2])
    (hget : c.children[i]? = some b) : (i = 0 ∧ b = b1) ∨ (i = 1 ∧ b = b2) := by
  rw [hch] at hget
  rcases i with _ | _ | i <;> simp at hget
  · exact .inl ⟨rfl, hget.symm⟩
  · exact .inr ⟨rfl, hget.symm⟩

/-- Every address reachable from a stored tree lies in its footprint. -/
private theorem rep_reach {g : Graph T} {a : Addr} {t : Tree T} {F : Addr → Prop}
    (h : Rep g a t F) : ∀ p z, Graph.Path g a p z → F z := by
  induction h with
  | const hc _ hch _ _ hF =>
    intro p z hp
    rcases path_inv hp hc with ⟨_, rfl⟩ | ⟨i, b, q, hget, _, _⟩
    · exact hF
    · simp [hch] at hget
  | feature hc _ hch _ _ hF =>
    intro p z hp
    rcases path_inv hp hc with ⟨_, rfl⟩ | ⟨i, b, q, hget, _, _⟩
    · exact hF
    · simp [hch] at hget
  | unary hc _ _ hch _ hs _ hF ih =>
    intro p z hp
    rcases path_inv hp hc with ⟨_, rfl⟩ | ⟨i, b, q, hget, _, hq⟩
    · exact hF
    · obtain ⟨_, rfl⟩ := child1 hch hget
      exact hs _ (ih q z hq)
  | binary hc _ _ hch _ _ hs1 hs2 _ _ _ hF ih1 ih2 =>
    intro p z hp
    rcases path_inv hp hc with ⟨_, rfl⟩ | ⟨i, b, q, hget, _, hq⟩
    · exact hF
    · rcases child2 hch hget with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hs1 _ (ih1 q z hq)
      · exact hs2 _ (ih2 q z hq)

/-- A stored tree has unique paths: the result of `combine_operators!` is unshared. -/
private theorem rep_noAlias {g : Graph T} {a : Addr} {t : Tree T} {F : Addr → Prop}
    (h : Rep g a t F) : Graph.NoAlias g a := by
  induction h with
  | const hc _ hch =>
    intro p q z hp hq
    rcases path_inv hp hc with ⟨rfl, _⟩ | ⟨i, b, _, hget, _, _⟩
    · rcases path_inv hq hc with ⟨rfl, _⟩ | ⟨j, b', _, hget', _, _⟩
      · rfl
      · simp [hch] at hget'
    · simp [hch] at hget
  | feature hc _ hch =>
    intro p q z hp hq
    rcases path_inv hp hc with ⟨rfl, _⟩ | ⟨i, b, _, hget, _, _⟩
    · rcases path_inv hq hc with ⟨rfl, _⟩ | ⟨j, b', _, hget', _, _⟩
      · rfl
      · simp [hch] at hget'
    · simp [hch] at hget
  | unary hc _ _ hch hr _ hn _ ih =>
    intro p q z hp hq
    rcases path_inv hp hc with ⟨rfl, hz⟩ | ⟨i, b, p', hget, rfl, hp'⟩ <;>
      rcases path_inv hq hc with ⟨rfl, hz'⟩ | ⟨j, b', q', hget', rfl, hq'⟩
    · rfl
    · subst hz; obtain ⟨_, rfl⟩ := child1 hch hget'; exact absurd (rep_reach hr _ _ hq') hn
    · subst hz'; obtain ⟨_, rfl⟩ := child1 hch hget; exact absurd (rep_reach hr _ _ hp') hn
    · obtain ⟨rfl, rfl⟩ := child1 hch hget
      obtain ⟨rfl, rfl⟩ := child1 hch hget'
      rw [ih p' q' z hp' hq']
  | binary hc _ _ hch hr1 hr2 _ _ hdj hn1 hn2 _ ih1 ih2 =>
    intro p q z hp hq
    rcases path_inv hp hc with ⟨rfl, hz⟩ | ⟨i, b, p', hget, rfl, hp'⟩ <;>
      rcases path_inv hq hc with ⟨rfl, hz'⟩ | ⟨j, b', q', hget', rfl, hq'⟩
    · rfl
    · subst hz
      rcases child2 hch hget' with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact absurd (rep_reach hr1 _ _ hq') hn1
      · exact absurd (rep_reach hr2 _ _ hq') hn2
    · subst hz'
      rcases child2 hch hget with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact absurd (rep_reach hr1 _ _ hp') hn1
      · exact absurd (rep_reach hr2 _ _ hp') hn2
    · rcases child2 hch hget with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases child2 hch hget' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ih1 p' q' z hp' hq']
      · exact absurd (rep_reach hr2 _ _ hq') (hdj z (rep_reach hr1 _ _ hp'))
      · exact absurd (rep_reach hr2 _ _ hp') (hdj z (rep_reach hr1 _ _ hq'))
      · rw [ih2 p' q' z hp' hq']

/-- A stored tree unfolds to itself with at least its depth in fuel. -/
private theorem unfold_of_rep {g : Graph T} {a : Addr} {t : Tree T} {F : Addr → Prop}
    (h : Rep g a t F) : ∀ fuel, t.depth ≤ fuel → g.unfold fuel a = some t := by
  induction h with
  | const hc hd hch hk hv =>
    intro fuel hf
    cases fuel with
    | zero => simp [Tree.depth] at hf
    | succ f => simp [Graph.unfold, hc, hd, hch, hk, hv]
  | feature hc hd hch hk hi =>
    intro fuel hf
    cases fuel with
    | zero => simp [Tree.depth] at hf
    | succ f => simp [Graph.unfold, hc, hd, hch, hk, hi]
  | unary hc hd hop hch _ _ _ _ ih =>
    intro fuel hf
    cases fuel with
    | zero => simp [Tree.depth] at hf
    | succ f =>
      simp [Tree.depth] at hf
      simp [Graph.unfold, hc, hd, hch, hop, ih f (by omega)]
  | binary hc hd hop hch _ _ _ _ _ _ _ _ ih1 ih2 =>
    intro fuel hf
    cases fuel with
    | zero => simp [Tree.depth] at hf
    | succ f =>
      simp [Tree.depth] at hf
      simp [Graph.unfold, hc, hd, hch, hop, ih1 f (by omega), ih2 f (by omega)]

private theorem noAlias_child {g : Graph T} {a b : Addr} {c : Cell T} {i : Nat}
    (h : Graph.NoAlias g a) (hc : g.cells a = some c) (hb : c.children[i]? = some b) :
    Graph.NoAlias g b := fun p q z hp hq => by
  have := h (i :: p) (i :: q) z (.cons hc hb hp) (.cons hc hb hq)
  simpa using this

private theorem reach_child {g : Graph T} {a b : Addr} {c : Cell T} {i : Nat}
    (hc : g.cells a = some c) (hb : c.children[i]? = some b) :
    ∀ z, Graph.Reachable g b z → Graph.Reachable g a z :=
  fun _ ⟨p, hp⟩ => ⟨i :: p, .cons hc hb hp⟩

private theorem not_reach_parent {g : Graph T} {a b : Addr} {c : Cell T} {i : Nat}
    (h : Graph.NoAlias g a) (hc : g.cells a = some c) (hb : c.children[i]? = some b) :
    ¬ Graph.Reachable g b a := fun ⟨p, hp⟩ => by
  have := h [] (i :: p) a (.nil a) (.cons hc hb hp)
  simp at this

private theorem disj_children {g : Graph T} {a b1 b2 : Addr} {c : Cell T} {i j : Nat}
    (h : Graph.NoAlias g a) (hc : g.cells a = some c) (hb1 : c.children[i]? = some b1)
    (hb2 : c.children[j]? = some b2) (hij : i ≠ j) :
    ∀ z, Graph.Reachable g b1 z → ¬ Graph.Reachable g b2 z := fun z ⟨p, hp⟩ ⟨q, hq⟩ => by
  have := h (i :: p) (j :: q) z (.cons hc hb1 hp) (.cons hc hb2 hq)
  simp at this
  exact hij this.1

private theorem mapM_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ys.length = l.length
  | [], ys, h => by simp at h; simp [← h]
  | x :: l, ys, h => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, hx, hl] at h
      | some zs =>
        simp [List.mapM_cons, hx, hl] at h
        subst h
        simp [mapM_length f l zs hl]

/-- An unshared graph that unfolds to a well-formed binary tree stores it with
the reachable set as footprint. -/
private theorem rep_of_unfold {nops : Nat → Nat} {nf : Nat} : ∀ (fuel : Nat) (g : Graph T)
    (a : Addr) (t : Tree T), g.unfold fuel a = some t → t.WF 2 nops nf →
    Graph.NoAlias g a → Rep g a t (Graph.Reachable g a) ∧ t.depth ≤ fuel
  | 0, _, _, _, h, _, _ => by simp [Graph.unfold] at h
  | fuel + 1, g, a, t, h, hw, hna => by
    have self : Graph.Reachable g a a := ⟨[], .nil a⟩
    unfold Graph.unfold at h
    cases hc : g.cells a with
    | none => rw [hc] at h; simp at h
    | some c =>
      rw [hc] at h
      simp only [bind, Option.bind] at h
      split at h
      · simp at h
      rename_i hlen
      have hlen : c.children.length = c.degree := by simpa using hlen
      split at h
      · rename_i hd
        have hch : c.children = [] := List.eq_nil_of_length_eq_zero (by omega)
        split at h
        · rename_i hk
          cases hv : c.val with
          | none => simp [hv] at h
          | some v =>
            simp [hv] at h
            subst h
            exact ⟨.const hc hd hch hk hv self, by simp [Tree.depth]⟩
        · rename_i hk
          simp at h
          subst h
          exact ⟨.feature hc hd hch (by simpa using hk) rfl self, by simp [Tree.depth]⟩
      · rename_i hd
        cases hm : c.children.mapM (Graph.unfold g fuel) with
        | none => simp [hm] at h
        | some ts =>
          simp [hm] at h
          subst h
          have hlts := mapM_length _ _ _ hm
          simp only [Tree.WF] at hw
          obtain ⟨⟨hl1, hl2, _⟩, _, hwc⟩ := hw
          match hch : c.children, hm, hlts with
          | [b1], hm, _ =>
            cases h1 : g.unfold fuel b1 with
            | none => simp [h1] at hm
            | some t1 =>
              simp [h1] at hm
              subst hm
              have hg1 : c.children[0]? = some b1 := by simp [hch]
              obtain ⟨hr1, hd1⟩ := rep_of_unfold fuel g b1 t1 h1 (hwc t1 (by simp))
                (noAlias_child hna hc hg1)
              refine ⟨.unary hc (by simp [hch] at hlen; omega) rfl hch hr1
                (reach_child hc hg1) (not_reach_parent hna hc hg1) self, ?_⟩
              simp [Tree.depth]; omega
          | [b1, b2], hm, _ =>
            cases h1 : g.unfold fuel b1 with
            | none => simp [h1] at hm
            | some t1 =>
              cases h2 : g.unfold fuel b2 with
              | none => simp [h1, h2] at hm
              | some t2 =>
                simp [h1, h2] at hm
                subst hm
                have hg1 : c.children[0]? = some b1 := by simp [hch]
                have hg2 : c.children[1]? = some b2 := by simp [hch]
                obtain ⟨hr1, hd1⟩ := rep_of_unfold fuel g b1 t1 h1 (hwc t1 (by simp))
                  (noAlias_child hna hc hg1)
                obtain ⟨hr2, hd2⟩ := rep_of_unfold fuel g b2 t2 h2 (hwc t2 (by simp))
                  (noAlias_child hna hc hg2)
                refine ⟨.binary hc (by simp [hch] at hlen; omega) rfl hch hr1 hr2
                  (reach_child hc hg1) (reach_child hc hg2)
                  (disj_children hna hc hg1 hg2 (by decide)) (not_reach_parent hna hc hg1)
                  (not_reach_parent hna hc hg2) self, ?_⟩
                have := Nat.max_le.2 ⟨hd1, hd2⟩
                simp [Tree.depth]; omega
          | [], _, hlts => simp only [List.length_nil] at hlts; omega
          | _ :: _ :: _ :: _, _, hlts => simp only [List.length_cons] at hlts; omega

/-! ## Pure properties of `combinePure` -/

private theorem cval_some {t : Tree T} {k : T} (h : cval? t = some k) : t = .const k := by
  cases t <;> simp_all [cval?]

/-- Induction over well-formed trees of degree at most two. -/
private theorem wf_induct {nops : Nat → Nat} {nf : Nat} {P : Tree T → Prop}
    (pc : ∀ v, P (.const v)) (pf : ∀ i, (Tree.feature i : Tree T).WF 2 nops nf → P (.feature i))
    (pu : ∀ op c, (Tree.branch op [c]).WF 2 nops nf → P c → P (.branch op [c]))
    (pb : ∀ op c1 c2, (Tree.branch op [c1, c2]).WF 2 nops nf → P c1 → P c2 →
      P (.branch op [c1, c2])) :
    ∀ t : Tree T, t.WF 2 nops nf → P t := by
  intro t
  induction t using Tree.induction with
  | hc v => intro _; exact pc v
  | hf i => intro hw; exact pf i hw
  | hb op cs ih =>
    intro hw
    have hw' := hw
    simp only [Tree.WF] at hw'
    obtain ⟨⟨hl1, hl2, _⟩, _, hwc⟩ := hw'
    match cs, ih, hw, hwc, hl1, hl2 with
    | [c], ih, hw, hwc, _, _ => exact pu op c hw (ih c (by simp) (hwc c (by simp)))
    | [c1, c2], ih, hw, hwc, _, _ =>
      exact pb op c1 c2 hw (ih c1 (by simp) (hwc c1 (by simp))) (ih c2 (by simp) (hwc c2 (by simp)))
    | [], _, _, _, hl1, _ => simp at hl1
    | _ :: _ :: _ :: _, _, _, _, _, hl2 => simp only [List.length_cons] at hl2; omega

/-- The local rewrite result is well formed and no larger or deeper than `l op r`. -/
private def Shrinks (nops : Nat → Nat) (nf : Nat) (l r t : Tree T) : Prop :=
  t.WF 2 nops nf ∧ t.size ≤ 1 + l.size + r.size ∧ t.depth ≤ 1 + max l.depth r.depth

private theorem shrinks_swap {nops : Nat → Nat} {nf : Nat} {l r t : Tree T}
    (h : Shrinks nops nf r l t) : Shrinks nops nf l r t := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by omega, by rw [Nat.max_comm]; exact h3⟩

section PureOps

variable [Add T] [Mul T] [Sub T]

private theorem rewritePure_eq (o : CEnum T) {op : Nat} {b : BinOp T} (h0 : op ≠ 0)
    (hb : o.bin[op - 1]? = some b) (l r : Tree T) :
    rewritePure o op l r =
      if (b.isComm && (isC l || isC r)) = true then commPure op b l r
      else if (b.isSub && (isC l || isC r)) = true then subPure op l r
      else .branch op [l, r] := by
  unfold rewritePure; rw [iteF h0, hb]

private theorem rewritePure_base (o : CEnum T) {op : Nat} (h : op = 0 ∨ o.bin[op - 1]? = none)
    (l r : Tree T) : rewritePure o op l r = .branch op [l, r] := by
  unfold rewritePure
  rcases h with h | h
  · rw [iteT h]
  · by_cases h0 : op = 0
    · rw [iteT h0]
    · rw [iteF h0, h]

variable {nops : Nat → Nat} {nf : Nat}

omit [Add T] [Mul T] [Sub T] in
private theorem base_shrinks {op : Nat} {l r : Tree T} (hl : l.WF 2 nops nf)
    (hr : r.WF 2 nops nf) (hop : 1 ≤ op ∧ op ≤ nops 2 ∧ op ≤ 255) :
    Shrinks nops nf l r (.branch op [l, r]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tree.WF, hl, hr, hop]
  · simp; omega
  · simp [Tree.depth]

private theorem commCore_shrinks {op : Nat} {b : BinOp T}
    {l r : Tree T} (hl : l.WF 2 nops nf) (hr : r.WF 2 nops nf)
    (hop : 1 ≤ op ∧ op ≤ nops 2 ∧ op ≤ 255) : Shrinks nops nf l r (commCore op b l r) := by
  have base := base_shrinks hl hr hop
  unfold commCore
  split
  · split
    · rename_i h2
      subst h2
      split <;> simp_all [Shrinks, Tree.WF, Tree.size, Tree.depth] <;> omega
    · exact base
  · exact base

omit [Mul T] in
private theorem subPure_shrinks {op : Nat} {l r : Tree T} (hl : l.WF 2 nops nf)
    (hr : r.WF 2 nops nf) (hop : 1 ≤ op ∧ op ≤ nops 2 ∧ op ≤ 255) :
    Shrinks nops nf l r (subPure op l r) := by
  have base := base_shrinks hl hr hop
  unfold subPure
  split
  · split
    · split
      · split <;> simp_all [Shrinks, Tree.WF, Tree.size, Tree.depth] <;> omega
      · exact base
    · exact base
  · split
    · split
      · split <;> simp_all [Shrinks, Tree.WF, Tree.size, Tree.depth] <;> omega
      · exact base
    · exact base

private theorem rewritePure_shrinks (o : CEnum T) {op : Nat} {l r : Tree T}
    (hl : l.WF 2 nops nf) (hr : r.WF 2 nops nf) (hop : 1 ≤ op ∧ op ≤ nops 2 ∧ op ≤ 255) :
    Shrinks nops nf l r (rewritePure o op l r) := by
  have base := base_shrinks hl hr hop
  by_cases h0 : op = 0
  · rw [rewritePure_base o (.inl h0)]; exact base
  cases hb : o.bin[op - 1]? with
  | none => rw [rewritePure_base o (.inr hb)]; exact base
  | some b =>
    rw [rewritePure_eq o h0 hb]
    split
    · rw [commPure_eq]
      split
      · exact shrinks_swap (commCore_shrinks hr hl hop)
      · exact commCore_shrinks hl hr hop
    · split
      · exact subPure_shrinks hl hr hop
      · exact base

/-- `combinePure` keeps trees well formed and does not grow them. -/
private theorem combinePure_shrinks (o : CEnum T) {nf : Nat} :
    ∀ t : Tree T, t.WF 2 o.nops nf →
      (combinePure o t).WF 2 o.nops nf ∧ (combinePure o t).size ≤ t.size ∧
        (combinePure o t).depth ≤ t.depth :=
  wf_induct
    (fun v => by simp [combinePure, Tree.WF])
    (fun i hw => by simp [combinePure, hw])
    (fun op c hw ih => by
      have hw' := hw
      simp only [Tree.WF] at hw'
      obtain ⟨⟨_, _, _⟩, hop, _⟩ := hw'
      simp only [List.length_singleton] at hop
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · simp [combinePure, Tree.WF, h1, hop]
      · simp [combinePure]; omega
      · simp [combinePure, Tree.depth]; omega)
    (fun op c1 c2 hw ih1 ih2 => by
      have hw' := hw
      simp only [Tree.WF] at hw'
      obtain ⟨⟨_, _, _⟩, hop, _⟩ := hw'
      simp only [List.length_cons] at hop
      obtain ⟨h1, h2, h3⟩ := ih1
      obtain ⟨k1, k2, k3⟩ := ih2
      obtain ⟨s1, s2, s3⟩ := rewritePure_shrinks o h1 k1 hop
      have hm : max (combinePure o c1).depth (combinePure o c2).depth ≤ max c1.depth c2.depth :=
        Nat.max_le.2 ⟨Nat.le_trans h3 (Nat.le_max_left _ _), Nat.le_trans k3 (Nat.le_max_right _ _)⟩
      refine ⟨?_, ?_, ?_⟩
      · simp only [combinePure]; exact s1
      · simp only [combinePure]; simp; omega
      · simp only [combinePure]; simp [Tree.depth]; omega)

end PureOps

/-! ## Denotation under the commutative-ring laws -/

section Denote

variable [Add T] [Mul T] [Sub T] [Neg T] [Inhabited T]

omit [Neg T] in
private theorem den_bin (o : CEnum T) {op : Nat} {b : BinOp T} (h0 : op ≠ 0)
    (hb : o.bin[op - 1]? = some b) (l r : Tree T) (x : Nat → Option T) :
    (Tree.branch op [l, r]).denote o.toOpEnum x =
      (l.denote o.toOpEnum x).bind fun vl =>
        (r.denote o.toOpEnum x).map fun vr => b.eval vl vr := by
  have hlk : o.toOpEnum.lookup 2 op = some fun xs => b.eval xs[0]! xs[1]! := by
    simp [OpEnum.lookup, CEnum.toOpEnum, h0, hb]
  cases hl : l.denote o.toOpEnum x <;> cases hr : r.denote o.toOpEnum x <;>
    simp [Tree.denote, hlk, List.mapM_cons, hl, hr]

omit [Add T] [Mul T] [Sub T] [Neg T] [Inhabited T] in
private theorem den_congr1 (o : OpEnum T) {op : Nat} {t t' : Tree T}
    (h : ∀ x, t'.denote o x = t.denote o x) (x : Nat → Option T) :
    (Tree.branch op [t']).denote o x = (Tree.branch op [t]).denote o x := by
  simp [Tree.denote, List.mapM_cons, h]

omit [Add T] [Mul T] [Sub T] [Neg T] [Inhabited T] in
private theorem den_congr2 (o : OpEnum T) {op : Nat} {t1 t1' t2 t2' : Tree T}
    (h1 : ∀ x, t1'.denote o x = t1.denote o x) (h2 : ∀ x, t2'.denote o x = t2.denote o x)
    (x : Nat → Option T) :
    (Tree.branch op [t1', t2']).denote o x = (Tree.branch op [t1, t2]).denote o x := by
  simp [Tree.denote, List.mapM_cons, h1, h2]

omit [Inhabited T] in
private theorem eval_comm (hR : RingLaws T) {b : BinOp T} (hc : b.isComm = true) (u v : T) :
    b.eval u v = b.eval v u := by
  cases b <;> simp_all [BinOp.isComm, BinOp.eval, hR.add_comm, hR.mul_comm]

omit [Inhabited T] in
private theorem eval_assoc (hR : RingLaws T) {b : BinOp T} (hc : b.isComm = true) (u v w : T) :
    b.eval (b.eval u v) w = b.eval u (b.eval v w) := by
  cases b <;> simp_all [BinOp.isComm, BinOp.eval, hR.add_assoc, hR.mul_assoc]

private theorem den_swap (hR : RingLaws T) (o : CEnum T) {op : Nat} {b : BinOp T}
    (h0 : op ≠ 0) (hb : o.bin[op - 1]? = some b) (hc : b.isComm = true) (l r : Tree T)
    (x : Nat → Option T) :
    (Tree.branch op [r, l]).denote o.toOpEnum x = (Tree.branch op [l, r]).denote o.toOpEnum x := by
  rw [den_bin o h0 hb, den_bin o h0 hb]
  cases l.denote o.toOpEnum x <;> cases r.denote o.toOpEnum x <;> simp [eval_comm hR hc]

private theorem commCore_denote (hR : RingLaws T) (o : CEnum T) {op : Nat} {b : BinOp T}
    (h0 : op ≠ 0) (hb : o.bin[op - 1]? = some b) (hc : b.isComm = true) (l r : Tree T)
    (x : Nat → Option T) :
    (commCore op b l r).denote o.toOpEnum x = (Tree.branch op [l, r]).denote o.toOpEnum x := by
  unfold commCore
  split
  · rename_i k op2 a c hk
    obtain rfl := cval_some hk
    split
    · rename_i h2
      subst h2
      split
      · obtain ⟨va, hva⟩ : ∃ v, cval? a = some v := ⟨_, by assumption⟩
        obtain rfl := cval_some hva
        simp only [cval_const, Option.some.injEq] at *; subst_vars
        simp only [den_bin o h0 hb]
        cases c.denote o.toOpEnum x <;> simp [Tree.denote]
        rw [eval_assoc hR hc, eval_comm hR hc k, ← eval_assoc hR hc]
      · obtain ⟨vc, hvc⟩ : ∃ v, cval? c = some v := ⟨_, by assumption⟩
        obtain rfl := cval_some hvc
        simp only [cval_const, Option.some.injEq] at *; subst_vars
        simp only [den_bin o h0 hb]
        cases a.denote o.toOpEnum x <;> simp [Tree.denote, eval_assoc hR hc]
      · rfl
    · rfl
  · rfl

omit [Inhabited T] in
private theorem alg (hR : RingLaws T) :
    (∀ y v1 vl : T, y - (v1 - vl) = vl - (v1 - y)) ∧
    (∀ y vl v2 : T, vl + v2 - y = vl - (y - v2)) ∧
    (∀ y v1 vr : T, v1 - vr - y = v1 - y - vr) ∧
    (∀ y vr v2 : T, y - (vr + v2) = y - v2 - vr) := by
  have lc : ∀ a b c : T, a + (b + c) = b + (a + c) := fun a b c => by
    rw [← hR.add_assoc, hR.add_comm a b, hR.add_assoc]
  refine ⟨fun _ _ _ => ?_, fun _ _ _ => ?_, fun _ _ _ => ?_, fun _ _ _ => ?_⟩ <;>
    simp only [hR.sub_eq, hR.neg_add, hR.neg_neg, hR.add_assoc, hR.add_comm, lc]

private theorem subPure_denote (hR : RingLaws T) (o : CEnum T) {op : Nat} (h0 : op ≠ 0)
    (hb : o.bin[op - 1]? = some .minus) (l r : Tree T) (x : Nat → Option T) :
    (subPure op l r).denote o.toOpEnum x = (Tree.branch op [l, r]).denote o.toOpEnum x := by
  obtain ⟨s1, s2, s3, s4⟩ := alg hR
  unfold subPure
  split
  · rename_i vl hl
    obtain rfl := cval_some hl
    split
    · rename_i op2 r1 r2
      split
      · rename_i h2
        subst h2
        split
        · obtain ⟨v1, hv1⟩ : ∃ v, cval? r1 = some v := ⟨_, by assumption⟩
          obtain rfl := cval_some hv1
          simp only [cval_const, Option.some.injEq] at *; subst_vars
          simp only [den_bin o h0 hb]
          cases r2.denote o.toOpEnum x <;> simp [Tree.denote, BinOp.eval, s1]
        · obtain ⟨v2, hv2⟩ : ∃ v, cval? r2 = some v := ⟨_, by assumption⟩
          obtain rfl := cval_some hv2
          simp only [cval_const, Option.some.injEq] at *; subst_vars
          simp only [den_bin o h0 hb]
          cases r1.denote o.toOpEnum x <;> simp [Tree.denote, BinOp.eval, s2]
        · rfl
      · rfl
    · rfl
  · split
    · rename_i _ _ l1 l2 _ _
      obtain ⟨vr, hvr⟩ : ∃ v, cval? r = some v := ⟨_, by assumption⟩
      obtain rfl := cval_some hvr
      split
      · rename_i h2
        subst h2
        split
        · obtain ⟨v1, hv1⟩ : ∃ v, cval? l1 = some v := ⟨_, by assumption⟩
          obtain rfl := cval_some hv1
          simp only [cval_const, Option.some.injEq] at *; subst_vars
          simp only [den_bin o h0 hb]
          cases l2.denote o.toOpEnum x <;> simp [Tree.denote, BinOp.eval, s3]
        · obtain ⟨v2, hv2⟩ : ∃ v, cval? l2 = some v := ⟨_, by assumption⟩
          obtain rfl := cval_some hv2
          simp only [cval_const, Option.some.injEq] at *; subst_vars
          simp only [den_bin o h0 hb]
          cases l1.denote o.toOpEnum x <;> simp [Tree.denote, BinOp.eval, s4]
        · rfl
      · rfl
    · rfl

private theorem rewritePure_denote (hR : RingLaws T) (o : CEnum T) (op : Nat) (l r : Tree T)
    (x : Nat → Option T) :
    (rewritePure o op l r).denote o.toOpEnum x = (Tree.branch op [l, r]).denote o.toOpEnum x := by
  by_cases h0 : op = 0
  · rw [rewritePure_base o (.inl h0)]
  cases hb : o.bin[op - 1]? with
  | none => rw [rewritePure_base o (.inr hb)]
  | some b =>
    rw [rewritePure_eq o h0 hb]
    split
    · rename_i hcm
      have hc : b.isComm = true := by simp_all
      rw [commPure_eq]
      split
      · rw [commCore_denote hR o h0 hb hc, den_swap hR o h0 hb hc]
      · exact commCore_denote hR o h0 hb hc l r x
    · split
      · rename_i _ hsm
        have hs : b = .minus := by cases b <;> simp_all [BinOp.isSub]
        subst hs
        exact subPure_denote hR o h0 hb l r x
      · rfl

/-- `combinePure` preserves the denotation under the commutative-ring laws. -/
private theorem combinePure_denote (hR : RingLaws T) (o : CEnum T) {nf : Nat} :
    ∀ t : Tree T, t.WF 2 o.nops nf →
      ∀ x, (combinePure o t).denote o.toOpEnum x = t.denote o.toOpEnum x :=
  wf_induct
    (fun v x => by simp [combinePure])
    (fun i _ x => by simp [combinePure])
    (fun op c _ ih x => by simp only [combinePure]; exact den_congr1 _ ih x)
    (fun op c1 c2 _ ih1 ih2 x => by
      simp only [combinePure]
      rw [rewritePure_denote hR o]
      exact den_congr2 _ ih1 ih2 x)

end Denote

/-! ## Main theorems -/

/-- The heap run on an unshared input succeeds, unfolds to the specification,
and returns an unshared tree. -/
private theorem combine_heap [Add T] [Mul T] [Sub T] (o : CEnum T) {nf fuel : Nat}
    {g : Graph T} {root : Addr} {t : Tree T} (hu : g.unfold fuel root = some t)
    (hw : t.WF 2 o.nops nf) (hna : Graph.NoAlias g root) :
    ∃ r g', combineOps o fuel g root = .ok (r, g') ∧
      g'.unfold fuel r = some (combinePure o t) ∧ Graph.NoAlias g' r := by
  obtain ⟨hrep, hdep⟩ := rep_of_unfold fuel g root t hu hw hna
  obtain ⟨r, g', he, hr, -, -⟩ := sim o fuel g root t _ hrep hw hdep
  exact ⟨r, g', he, unfold_of_rep hr fuel (Nat.le_trans (combinePure_shrinks o t hw).2.2 hdep),
    rep_noAlias hr⟩

/-- Combination rewrites only the original tree's footprint and cannot reach outside it. -/
theorem combineOps_frame [Add T] [Mul T] [Sub T] (o : CEnum T) {nf fuel : Nat}
    {g h : Graph T} {root result : Addr} {t : Tree T} (hu : g.unfold fuel root = some t)
    (hw : t.WF 2 o.nops nf) (hna : Graph.NoAlias g root)
    (run : combineOps o fuel g root = .ok (result, h)) :
    (∀ a, ¬ Graph.Reachable g root a → h.cells a = g.cells a) ∧
    (∀ a, Graph.Reachable h result a → Graph.Reachable g root a) := by
  obtain ⟨hrep, hdep⟩ := rep_of_unfold fuel g root t hu hw hna
  obtain ⟨r, g', he, hr, frame, _⟩ := sim o fuel g root t _ hrep hw hdep
  rw [run] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj he)
  exact ⟨frame, fun a ⟨p, hp⟩ => rep_reach hr p a hp⟩

theorem combine_matches_spec_proof : combine_matches_spec := by
  intro T _ _ _ o nf fuel g root t hu hw hna
  obtain ⟨r, g', he, hun, -⟩ := combine_heap o hu hw hna
  exact ⟨r, g', he, hun⟩

theorem combine_wf_proof : combine_wf := by
  intro T _ _ _ o nf fuel g root t hu hw hna
  obtain ⟨r, g', he, hun, -⟩ := combine_heap o hu hw hna
  obtain ⟨h1, h2, -⟩ := combinePure_shrinks o t hw
  exact ⟨r, g', _, he, hun, h1, h2⟩

theorem combine_preserves_denote_ring_proof : combine_preserves_denote_ring := by
  intro T _ _ _ _ _ hR o nf fuel g root t hu hw hna
  obtain ⟨r, g', he, hun, -⟩ := combine_heap o hu hw hna
  exact ⟨r, g', _, he, hun, combinePure_denote hR o t hw⟩

theorem combine_result_noalias_proof : combine_result_noalias := by
  intro T _ _ _ o nf fuel g root t hu hw hna
  obtain ⟨r, g', he, -, hr⟩ := combine_heap o hu hw hna
  exact ⟨r, g', he, hr⟩

/-- When the commutative block does not replace the root, `combine_operators!`
returns the input root itself, which then holds the combined tree. -/
theorem combine_input_unchanged_unless_replaced_proof :
    combine_input_unchanged_unless_replaced := by
  intro o nf fuel g root t hu hw hna hnr
  obtain ⟨hrep, hdep⟩ := rep_of_unfold fuel g root t hu hw hna
  obtain ⟨r, g', he, hr, -, hra⟩ := sim o fuel g root t _ hrep hw hdep
  obtain rfl := hra hnr
  exact ⟨r, g', _, he,
    unfold_of_rep hr fuel (Nat.le_trans (combinePure_shrinks o t hw).2.2 hdep),
    combinePure_denote jf_ringLaws o t hw⟩

/-! ## Satisfiable hypotheses -/

/-- `OperatorEnum(2 => (+, -, *))` on integers. -/
private def exOps : CEnum Int := ⟨[], [.plus, .minus, .times]⟩

/-- `(x1 + 1) + 2`. -/
private def exTree : Tree Int := .branch 1 [.branch 1 [.feature 1, .const 1], .const 2]

private theorem ex_hyps :
    (Graph.ofTree (Heap.empty : Graph Int) exTree).2.unfold 3
        (Graph.ofTree (Heap.empty : Graph Int) exTree).1 = some exTree ∧
      exTree.WF 2 exOps.nops 1 ∧
      Graph.NoAlias (Graph.ofTree (Heap.empty : Graph Int) exTree).2
        (Graph.ofTree (Heap.empty : Graph Int) exTree).1 :=
  ⟨Graph.unfold_ofTree _ _ (by simp [exTree, Tree.Representable]) _
      (by simp [exTree, Tree.depth]),
    by simp [exTree, Tree.WF, CEnum.nops, exOps], Graph.noAlias_ofTree _ _⟩

private theorem ringLaws_int : RingLaws Int :=
  ⟨fun _ _ _ => by omega, fun _ _ => by omega, Int.mul_assoc, Int.mul_comm,
    fun _ _ => by omega, fun _ _ => by omega, fun _ => by omega⟩

/-- Hypotheses of `combine_matches_spec` are satisfiable. -/
example : ∃ (o : CEnum Int) (nf fuel : Nat) (g : Graph Int) (root : Addr) (t : Tree Int),
    g.unfold fuel root = some t ∧ t.WF 2 o.nops nf ∧ Graph.NoAlias g root :=
  ⟨exOps, 1, 3, _, _, exTree, ex_hyps⟩

/-- Hypotheses of `combine_wf` are satisfiable. -/
example : ∃ (o : CEnum Int) (nf fuel : Nat) (g : Graph Int) (root : Addr) (t : Tree Int),
    g.unfold fuel root = some t ∧ t.WF 2 o.nops nf ∧ Graph.NoAlias g root :=
  ⟨exOps, 1, 3, _, _, exTree, ex_hyps⟩

/-- Hypotheses of `combine_preserves_denote_ring` are satisfiable. -/
example : RingLaws Int ∧
    ∃ (o : CEnum Int) (nf fuel : Nat) (g : Graph Int) (root : Addr) (t : Tree Int),
      g.unfold fuel root = some t ∧ t.WF 2 o.nops nf ∧ Graph.NoAlias g root :=
  ⟨ringLaws_int, exOps, 1, 3, _, _, exTree, ex_hyps⟩

/-- Hypotheses of `combine_result_noalias` are satisfiable. -/
example : ∃ (o : CEnum Int) (nf fuel : Nat) (g : Graph Int) (root : Addr) (t : Tree Int),
    g.unfold fuel root = some t ∧ t.WF 2 o.nops nf ∧ Graph.NoAlias g root :=
  ⟨exOps, 1, 3, _, _, exTree, ex_hyps⟩

/-- `OperatorEnum(2 => (+, -, *))` on Float64-like scalars. -/
private def exOpsJF : CEnum JF := ⟨[], [.plus, .minus, .times]⟩

/-- `x1 + 1.0`, whose root `combine_operators!` keeps. -/
private def exTreeJF : Tree JF := .branch 1 [.feature 1, .const (.fin 1)]

/-- Hypotheses of `combine_input_unchanged_unless_replaced` are satisfiable. -/
example : ∃ (o : CEnum JF) (nf fuel : Nat) (g : Graph JF) (root : Addr) (t : Tree JF),
    g.unfold fuel root = some t ∧ t.WF 2 o.nops nf ∧ Graph.NoAlias g root ∧
      commReplaces o t = false :=
  ⟨exOpsJF, 1, 2, (Graph.ofTree (Heap.empty : Graph JF) exTreeJF).2,
    (Graph.ofTree (Heap.empty : Graph JF) exTreeJF).1, exTreeJF,
    Graph.unfold_ofTree _ _ (by simp [exTreeJF, Tree.Representable]) _
      (by simp [exTreeJF, Tree.depth]),
    by simp [exTreeJF, Tree.WF, CEnum.nops, exOpsJF], Graph.noAlias_ofTree _ _, rfl⟩

end DynExpr.Simplify
