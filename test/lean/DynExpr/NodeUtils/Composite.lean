import DynExpr.NodeUtils.Success

namespace DynExpr.NodeUtils

/-- src/NodeUtils.jl:109-115: allocate using value counts, then pack refs in order. -/
def getCompositeConstants (p : ValueProtocol T) (g : Graph T) (refs : List Addr) : Jl (List JF) := do
  let values ← readValues g refs
  let buffer := List.replicate ((values.map p.count).sum) (JF.fin 0)
  let (_,buffer) ← values.foldlM (fun (i,buffer) v => p.pack buffer i v) (1,buffer)
  return buffer

/-- src/NodeUtils.jl:126-145: unpack every ref, including zero-count composites,
then reject numeric entries left over after the final ref. -/
def setCompositeConstants (p : ValueProtocol T) (g : Graph T) (nums : List JF)
    (idx : Nat) : List Addr → Jl (Graph T)
  | [] => if idx ≤ nums.length then .error (.errorException "bad unpack_scalar_constants") else .ok g
  | a :: rs => do
      let c ← g.read a
      let v ← match c.val with | some v => .ok v | none => .error .undefRefError
      let (j,v') ← p.unpack nums idx v
      let h ← setValue g a v'
      setCompositeConstants p h nums j rs
/-- Numeric-vector value protocol used by the Julia empty-composite reproducer. -/
def unpackVector (nums : List JF) (idx : Nat) : List JF → Jl (Nat × List JF)
  | [] => .ok (idx,[])
  | _ :: rest => do
      let (j,v) ← unpackScalar nums idx
      let (k,vs) ← unpackVector nums j rest
      return (k,v :: vs)

def emptyProtocol : ValueProtocol (List JF) :=
  { count := List.length
    pack := fun xs i values => values.foldlM (fun (j,buffer) v => packScalar buffer j v) (i,xs)
    unpack := unpackVector }

/-- The lawful numeric-vector protocol has length counts and preserves each
vector through packing and unpacking into any equal-length template. -/
def VectorProtocolLawful (p : ValueProtocol (List JF)) : Prop :=
  (∀ values, p.count values = values.length) ∧
  ∀ (values xs template : List JF) (idx : Nat),
    1 ≤ idx → idx - 1 + values.length ≤ xs.length →
    template.length = values.length →
    ∃ packed, p.pack xs idx values = .ok (idx + values.length, packed) ∧
      p.unpack packed idx template = .ok (idx + values.length, values) ∧
      packed.length = xs.length

/-- Packing preserves slots outside its value segment; unpacking reads only
the segment selected by its index and template length. -/
def VectorProtocolLocal (p : ValueProtocol (List JF)) : Prop :=
  (∀ xs idx values j packed,
    p.pack xs idx values = .ok (j, packed) →
    1 ≤ idx → idx - 1 + values.length ≤ xs.length →
    packed.length = xs.length ∧
      ∀ n, (n < idx - 1 ∨ idx - 1 + values.length ≤ n) → packed[n]? = xs[n]?) ∧
  (∀ nums nums' idx template,
    (∀ n, idx - 1 ≤ n → n < idx - 1 + template.length → nums[n]? = nums'[n]?) →
    p.unpack nums idx template = p.unpack nums' idx template)

private theorem vectorRoundtrip (values xs template : List JF) (idx : Nat)
    (hpos : 1 ≤ idx) (hslots : idx - 1 + values.length ≤ xs.length)
    (htemplate : template.length = values.length) :
    ∃ packed,
      values.foldlM (fun (j,buffer) v => packScalar buffer j v) (idx,xs) =
        .ok (idx + values.length, packed) ∧
      unpackVector packed idx template = .ok (idx + values.length, values) ∧
      packed.length = xs.length ∧
      ∀ n, (n < idx - 1 ∨ idx - 1 + values.length ≤ n) → packed[n]? = xs[n]? := by
  induction values generalizing xs template idx with
  | nil =>
      have ht : template = [] := List.length_eq_zero_iff.mp htemplate
      subst template
      exact ⟨xs, by simp; rfl, by simp [unpackVector], rfl, fun _ _ => rfl⟩
  | cons v rest ih =>
      cases template with
      | nil => simp at htemplate
      | cons t ts =>
          have hbound : idx ≤ xs.length := by simp only [List.length_cons] at hslots; omega
          have hlt : idx - 1 < xs.length := by omega
          have hstep := (scalarRoundtrip_proven xs idx v hpos hbound).1
          have hrest : idx + 1 - 1 + rest.length ≤ (xs.set (idx - 1) v).length := by
            simp only [List.length_set]
            simp only [List.length_cons] at hslots
            omega
          have ht : ts.length = rest.length := by simpa using htemplate
          obtain ⟨packed,hpack,hunpack,hlen,hframe⟩ :=
            ih (xs.set (idx - 1) v) ts (idx + 1) (by omega) hrest ht
          have hhead : packed[idx - 1]? = some v := by
            rw [hframe (idx - 1) (Or.inl (by omega)), List.getElem?_set_self hlt]
          have hread : unpackScalar packed idx = .ok (idx + 1,v) := by
            have hne : idx ≠ 0 := by omega
            simp [unpackScalar, hne, hhead]
          have hend : idx + 1 + rest.length = idx + (v :: rest).length := by
            simp only [List.length_cons]; omega
          refine ⟨packed, ?_, ?_, ?_, ?_⟩
          · simp only [List.foldlM_cons, hstep, bindOk]
            simpa only [hend] using hpack
          · simp [unpackVector, hread, hunpack, bindOk, mapOk, hend]
          · simpa using hlen
          · intro n hn
            rw [hframe n (by
              rcases hn with hn | hn
              · exact Or.inl (by omega)
              · exact Or.inr (by simp only [List.length_cons] at hn; omega)),
              List.getElem?_set_ne (by
                rcases hn with hn | hn <;> simp only [List.length_cons] at * <;> omega)]

def EmptyProtocolLaws : Prop := VectorProtocolLawful emptyProtocol

theorem emptyProtocolLaws_proven : EmptyProtocolLaws := by
  constructor
  · intro values; rfl
  · intro values xs template idx hpos hslots htemplate
    obtain ⟨packed,hpack,hunpack,hlen,_⟩ :=
      vectorRoundtrip values xs template idx hpos hslots htemplate
    exact ⟨packed,hpack,hunpack,hlen⟩

private theorem unpackVectorLocal (nums nums' template : List JF) (idx : Nat)
    (h : ∀ n, idx - 1 ≤ n → n < idx - 1 + template.length →
      nums[n]? = nums'[n]?) :
    unpackVector nums idx template = unpackVector nums' idx template := by
  induction template generalizing idx with
  | nil => rfl
  | cons v vs ih =>
      by_cases hz : idx = 0
      · subst idx
        simp [unpackVector, unpackScalar, bindError]
      · have hs : unpackScalar nums idx = unpackScalar nums' idx := by
          simp [unpackScalar, hz, h (idx - 1) (by omega) (by simp)]
        have ht : unpackVector nums (idx + 1) vs = unpackVector nums' (idx + 1) vs :=
          ih (idx + 1) (by
            intro n hlo hhi
            apply h n
            · omega
            · simp only [List.length_cons]; omega)
        simp only [unpackVector, hs]
        unfold unpackScalar
        simp only [hz, ↓reduceIte]
        cases nums'[idx - 1]? <;> simp [bindError, bindOk, ht]

theorem emptyProtocolLocal_proven : VectorProtocolLocal emptyProtocol := by
  constructor
  · intro xs idx values j packed hp hpos hslots
    obtain ⟨expected,he,_,hlen,hframe⟩ :=
      vectorRoundtrip values xs values idx hpos hslots rfl
    have heq : (j,packed) = (idx + values.length,expected) := by
      exact Except.ok.inj (hp.symm.trans he)
    cases heq
    exact ⟨hlen,hframe⟩
  · intro nums nums' idx template h
    exact unpackVectorLocal nums nums' template idx h

example : VectorProtocolLocal emptyProtocol := emptyProtocolLocal_proven

example : 1 ≤ (1 : Nat) ∧
    1 - 1 + ([] : List JF).length ≤ ([] : List JF).length ∧
    ([] : List JF).length = ([] : List JF).length := by decide

/-- src/NodeUtils.jl:99-115: traverse the input tree to collect refs before
packing the composite values in depth-first order. -/
def getCompositeScalarConstants (p : ValueProtocol T) (g : Graph T)
    (sharing : Bool) (fuel : Nat) (root : Addr) : Jl (List JF × List Addr) := do
  let (refs, _) ← constantRefs g sharing fuel root []
  return ((← getCompositeConstants p g refs), refs)

def emptyComposite : Graph (List JF) :=
  (Heap.empty.alloc (constantCell [])).2

def EmptyCompositeRoundtrip : Prop :=
  ∀ (p : ValueProtocol (List JF)) (g : Graph (List JF)) sharing fuel root nums refs,
    VectorProtocolLawful p → VectorProtocolLocal p →
    Graph.NoAlias g root → Traversable g fuel root →
    getCompositeScalarConstants p g sharing fuel root = .ok (nums,refs) →
    setCompositeConstants p g nums 1 refs = .ok g


example : VectorProtocolLawful emptyProtocol ∧ VectorProtocolLocal emptyProtocol ∧
    Graph.NoAlias emptyComposite 0 ∧ Traversable emptyComposite 1 0 ∧
    getCompositeScalarConstants emptyProtocol emptyComposite false 1 0 = .ok ([],[0]) := by
  exact ⟨emptyProtocolLaws_proven, emptyProtocolLocal_proven,
    Graph.noAlias_ofTree Heap.empty (.const []),
    ⟨constantCell [],rfl,rfl,by intro _ _; exact ⟨[],rfl⟩,by simp [constantCell]⟩, rfl⟩

/-- Empty values may occur anywhere except at the final constant ref. -/
def NoTrailingEmpty : List (List JF) → Prop
  | [] => True
  | [v] => v ≠ []
  | _ :: v :: vs => NoTrailingEmpty (v :: vs)

private theorem noTrailingEmpty_cons (v : List JF) (vs : List (List JF))
    (h : NoTrailingEmpty (v :: vs)) :
    0 < (v :: vs).flatten.length ∧ NoTrailingEmpty vs := by
  induction vs generalizing v with
  | nil => simpa [NoTrailingEmpty, List.length_pos_iff] using h
  | cons w ws ih =>
      have ht : NoTrailingEmpty (w :: ws) := h
      have hp := (ih w ht).1
      refine ⟨?_, ht⟩
      simp only [List.flatten_cons, List.length_append] at hp ⊢
      omega

private theorem packVectorAt (values slots pre suffix : List JF)
    (hlen : values.length = slots.length) :
    values.foldlM (fun (j,buffer) v => packScalar buffer j v)
      (pre.length + 1, pre ++ slots ++ suffix) =
    .ok (pre.length + 1 + values.length, pre ++ values ++ suffix) := by
  induction values generalizing slots pre with
  | nil =>
      have hs : slots = [] := List.length_eq_zero_iff.mp hlen.symm
      subst slots
      simp; rfl
  | cons v vs ih =>
      cases slots with
      | nil => simp at hlen
      | cons s ss =>
          have hs : vs.length = ss.length := by simpa using hlen
          have hb : pre.length + 1 ≤ (pre ++ (s :: ss) ++ suffix).length := by
            simp only [List.length_append, List.length_cons]
            omega
          have hp : packScalar (pre ++ (s :: ss) ++ suffix) (pre.length + 1) v =
              .ok (pre.length + 1 + 1, (pre ++ [v]) ++ ss ++ suffix) := by
            have hs := (scalarRoundtrip_proven (pre ++ (s :: ss) ++ suffix)
              (pre.length + 1) v (by omega) hb).1
            simpa [List.append_assoc, List.set_append_right] using hs
          simp only [List.foldlM_cons, hp, bindOk]
          simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih ss (pre ++ [v]) hs

private theorem packVectorsFlatten (values : List (List JF)) (state : Nat × List JF) :
    values.foldlM (fun (i,buffer) v => emptyProtocol.pack buffer i v) state =
    values.flatten.foldlM (fun (i,buffer) v => packScalar buffer i v) state := by
  induction values generalizing state with
  | nil => rfl
  | cons v vs ih =>
      cases state with
      | mk idx buffer =>
          simp only [List.foldlM_cons, List.flatten_cons, List.foldlM_append]
          change (v.foldlM (fun (i,buffer) v => packScalar buffer i v) (idx,buffer) >>=
            fun next => vs.foldlM (fun (i,buffer) v => emptyProtocol.pack buffer i v) next) = _
          congr 1
          funext next
          exact ih next

private theorem getCompositeFlatten (g : Graph (List JF)) (refs : List Addr)
    (values : List (List JF)) (hr : readValues g refs = .ok values) :
    getCompositeConstants emptyProtocol g refs = .ok values.flatten := by
  have hp : values.flatten.foldlM (fun (i,buffer) v => packScalar buffer i v)
      (1, List.replicate values.flatten.length (JF.fin 0)) =
      .ok (1 + values.flatten.length, values.flatten) := by
    simpa using packVectorAt values.flatten
      (List.replicate values.flatten.length (JF.fin 0)) [] [] (by simp)
  simp only [getCompositeConstants, hr, bindOk, packVectorsFlatten]
  change (fun state : Nat × List JF => state.2) <$>
    values.flatten.foldlM (fun (i,buffer) v => packScalar buffer i v)
      (1, List.replicate ((values.map List.length).sum) (JF.fin 0)) = .ok values.flatten
  rw [← List.length_flatten, hp, mapOk]

private theorem unpackVectorAt (values pre suffix : List JF) :
    unpackVector (pre ++ values ++ suffix) (pre.length + 1) values =
      .ok (pre.length + 1 + values.length, values) := by
  induction values generalizing pre with
  | nil => rfl
  | cons v vs ih =>
      have hr : unpackScalar (pre ++ (v :: vs) ++ suffix) (pre.length + 1) =
          .ok (pre.length + 1 + 1, v) := by
        simp [unpackScalar]
      have ht : unpackVector (pre ++ (v :: vs) ++ suffix) (pre.length + 1 + 1) vs =
          .ok (pre.length + 1 + 1 + vs.length, vs) := by
        simpa [List.append_assoc] using ih (pre ++ [v])
      simp only [unpackVector, hr, bindOk, ht, List.length_cons]
      congr 2 <;> omega

private theorem restoreCompositeRefs (refs : List Addr) (g : Graph (List JF))
    (values : List (List JF)) (pre : List JF)
    (hr : readValues g refs = .ok values) (htail : NoTrailingEmpty values) :
    setCompositeConstants emptyProtocol g (pre ++ values.flatten)
      (pre.length + 1) refs = .ok g := by
  induction refs generalizing values pre with
  | nil =>
      simp [readValues] at hr
      subst values
      simp [setCompositeConstants]
  | cons a refs ih =>
      cases hc : g.cells a with
      | none => simp [readValues, Heap.read, hc, bindError] at hr
      | some c =>
          cases hv : c.val with
          | none => simp [readValues, Heap.read, hc, hv, bindOk, bindError] at hr
          | some v =>
              cases hs : readValues g refs with
              | error e => simp [readValues, Heap.read, hc, hv, hs, bindOk, mapError] at hr
              | ok rest =>
                  simp [readValues, Heap.read, hc, hv, hs, bindOk, mapOk] at hr
                  subst values
                  obtain ⟨_,hrest⟩ := noTrailingEmpty_cons v rest htail
                  have hu : unpackVector (pre ++ (v :: rest).flatten) (pre.length + 1) v =
                      .ok (pre.length + 1 + v.length, v) := by
                    simpa [List.append_assoc] using unpackVectorAt v pre rest.flatten
                  have hw := setValueRestore g a c v hc hv
                  simp only [setCompositeConstants, Heap.read, hc,
                    bindOk, hv, emptyProtocol, hu, hw]
                  simpa [emptyProtocol, List.flatten_cons, List.append_assoc, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm]
                    using ih rest (pre ++ v) hs hrest

private theorem packProtocolValues (p : ValueProtocol (List JF))
    (hlaw : VectorProtocolLawful p) (values : List (List JF)) (buffer : List JF) (idx : Nat)
    (hpos : 1 ≤ idx) (hslots : idx - 1 + (values.map List.length).sum ≤ buffer.length) :
    ∃ packed, values.foldlM (fun (i,buffer) v => p.pack buffer i v) (idx,buffer) =
      .ok (idx + (values.map List.length).sum, packed) := by
  induction values generalizing buffer idx with
  | nil => exact ⟨buffer, by simp; rfl⟩
  | cons v vs ih =>
      have hslots' : idx - 1 + (v.length + (vs.map List.length).sum) ≤ buffer.length := by
        simpa using hslots
      obtain ⟨mid,hpack,_hunpack,hlen⟩ := hlaw.2 v buffer v idx hpos (by omega) rfl
      have hrest : idx + v.length - 1 + (vs.map List.length).sum ≤ mid.length := by
        rw [hlen]
        omega
      obtain ⟨packed,hpacked⟩ := ih mid (idx + v.length) (by omega) hrest
      refine ⟨packed, ?_⟩
      simp only [List.foldlM_cons, hpack, bindOk]
      simpa [Nat.add_assoc] using hpacked

private theorem packProtocolRestore (p : ValueProtocol (List JF))
    (hlaw : VectorProtocolLawful p) (hlocal : VectorProtocolLocal p)
    (values : List (List JF)) (buffer : List JF) (idx : Nat)
    (hpos : 1 ≤ idx) (hslots : idx - 1 + (values.map List.length).sum ≤ buffer.length) :
    ∃ packed,
      values.foldlM (fun (i,buffer) v => p.pack buffer i v) (idx,buffer) =
        .ok (idx + (values.map List.length).sum, packed) ∧
      packed.length = buffer.length ∧
      (∀ n, n < idx - 1 → packed[n]? = buffer[n]?) ∧
      (∀ g refs, readValues g refs = .ok values →
        packed.length < idx + (values.map List.length).sum →
        setCompositeConstants p g packed idx refs = .ok g) := by
  induction values generalizing buffer idx with
  | nil =>
      refine ⟨buffer, by simp; rfl, rfl, fun _ _ => rfl, ?_⟩
      intro g refs hr hend
      cases refs with
      | nil => simp [setCompositeConstants, show ¬ idx ≤ buffer.length by simpa using hend]
      | cons a refs =>
          cases hc : g.cells a with
          | none => simp [readValues, Heap.read, hc, bindError] at hr
          | some c =>
              cases hv : c.val with
              | none => simp [readValues, Heap.read, hc, hv, bindOk, bindError] at hr
              | some v =>
                  cases hs : readValues g refs <;>
                    simp [readValues, Heap.read, hc, hv, hs, bindOk, mapOk, mapError] at hr
  | cons v vs ih =>
      have hslots' : idx - 1 + (v.length + (vs.map List.length).sum) ≤ buffer.length := by
        simpa using hslots
      obtain ⟨mid,hpack,hunpack,hlen⟩ := hlaw.2 v buffer v idx hpos (by omega) rfl
      have hrest : idx + v.length - 1 + (vs.map List.length).sum ≤ mid.length := by
        rw [hlen]; omega
      obtain ⟨packed,hpacked,hplen,hframe,hrestore⟩ :=
        ih mid (idx + v.length) (by omega) hrest
      have hmidframe := (hlocal.1 buffer idx v _ mid hpack hpos (by omega)).2
      have hu : p.unpack packed idx v = .ok (idx + v.length,v) := by
        rw [hlocal.2 packed mid idx v (by
          intro n _ hn
          exact hframe n (by omega)), hunpack]
      refine ⟨packed, ?_, hplen.trans hlen, ?_, ?_⟩
      · simp only [List.foldlM_cons, hpack, bindOk]
        simpa [Nat.add_assoc] using hpacked
      · intro n hn
        rw [hframe n (by omega), hmidframe n (Or.inl hn)]
      · intro g refs hr hend
        cases refs with
        | nil => simp [readValues] at hr
        | cons a refs =>
            cases hc : g.cells a with
            | none => simp [readValues, Heap.read, hc, bindError] at hr
            | some c =>
                cases hv : c.val with
                | none => simp [readValues, Heap.read, hc, hv, bindOk, bindError] at hr
                | some w =>
                    cases hs : readValues g refs with
                    | error e =>
                        simp [readValues, Heap.read, hc, hv, hs, bindOk, mapError] at hr
                    | ok rest =>
                        simp only [readValues, Heap.read, hc, hv, hs, bindOk] at hr
                        obtain ⟨rfl,rfl⟩ := hr
                        have ht := hrestore g refs hs (by simpa [Nat.add_assoc] using hend)
                        simp only [setCompositeConstants, Heap.read, hc, hv, bindOk,
                          hu, setValueRestore g a c v hc hv, ht]

theorem emptyCompositeRoundtrip_proven : EmptyCompositeRoundtrip := by
  intro p g sharing fuel root nums refs hlaw hlocal _hna hsource hget
  obtain ⟨actual,visited,hrefs,hvalid⟩ :=
    constantRefs_success g sharing fuel root [] hsource
  obtain ⟨values,hread⟩ := readValues_success g actual hvalid
  have hcount : p.count = List.length := funext hlaw.1
  obtain ⟨packed,hpack,hlen,_,hrestore⟩ :=
    packProtocolRestore p hlaw hlocal values
      (List.replicate (values.map List.length).sum (JF.fin 0)) 1 (by omega) (by simp)
  have hp : getCompositeConstants p g actual = .ok packed := by
    simp [getCompositeConstants, hread, hcount, hpack, bindOk, mapOk]
  simp only [getCompositeScalarConstants, hrefs, bindOk, hp] at hget
  obtain ⟨rfl,rfl⟩ := hget
  exact hrestore g _ hread (by simp only [List.length_replicate] at hlen; omega)

def CompositeGetterSuccess : Prop :=
  ∀ (p : ValueProtocol (List JF)) (g : Graph (List JF)) sharing fuel root,
    VectorProtocolLawful p → Graph.NoAlias g root → Traversable g fuel root →
    ∃ nums refs, getCompositeScalarConstants p g sharing fuel root = .ok (nums,refs)

theorem compositeGetterSuccess_proven : CompositeGetterSuccess := by
  intro p g sharing fuel root hlaw _hna hsource
  obtain ⟨refs,visited,hrefs,hvalid⟩ := constantRefs_success g sharing fuel root [] hsource
  obtain ⟨values,hread⟩ := readValues_success g refs hvalid
  have hcount : p.count = List.length := funext hlaw.1
  obtain ⟨packed,hpack⟩ := packProtocolValues p hlaw values
    (List.replicate (values.map List.length).sum (JF.fin 0)) 1 (by omega) (by simp)
  have hget : getCompositeConstants p g refs = .ok packed := by
    simp [getCompositeConstants, hread, hcount, hpack, bindOk, mapOk]
  exact ⟨packed,refs,by simp [getCompositeScalarConstants, hrefs, hget, bindOk, mapOk]⟩

def CompositeRoundtripNoTrailingEmpty : Prop :=
  ∀ (g : Graph (List JF)) sharing fuel root,
    Graph.NoAlias g root → Traversable g fuel root →
    ∃ nums refs values,
      getCompositeScalarConstants emptyProtocol g sharing fuel root = .ok (nums,refs) ∧
      readValues g refs = .ok values ∧
      (NoTrailingEmpty values → setCompositeConstants emptyProtocol g nums 1 refs = .ok g)

theorem compositeRoundtripNoTrailingEmpty_proven : CompositeRoundtripNoTrailingEmpty := by
  intro g sharing fuel root _hna hsource
  obtain ⟨refs,visited,hrefs,hvalid⟩ := constantRefs_success g sharing fuel root [] hsource
  obtain ⟨values,hread⟩ := readValues_success g refs hvalid
  have hget := getCompositeFlatten g refs values hread
  refine ⟨values.flatten,refs,values,?_,hread,?_⟩
  · simp [getCompositeScalarConstants, hrefs, hget, bindOk, mapOk]
  · intro htail
    simpa using restoreCompositeRefs refs g values [] hread htail

example : NoTrailingEmpty [[], [JF.fin 1]] := by
  simp [NoTrailingEmpty]

example : Graph.NoAlias ((Heap.empty.alloc (constantCell [JF.fin 1])).2) 0 ∧
    Traversable ((Heap.empty.alloc (constantCell [JF.fin 1])).2) 1 0 ∧
    NoTrailingEmpty [[JF.fin 1]] := by
  exact ⟨Graph.noAlias_ofTree Heap.empty (.const [JF.fin 1]),
    ⟨constantCell [JF.fin 1],rfl,rfl,by intro _ _; exact ⟨[JF.fin 1],rfl⟩,
      by simp [constantCell]⟩, by simp [NoTrailingEmpty]⟩

/-- src/NodeUtils.jl:129: writes to existing refs succeed and preserve every
non-value field and every other identity. -/
def ValueUpdateFrame : Prop := ∀ (g : Graph Nat) a v c,
  g.cells a = some c → ∃ h, setValue g a v = .ok h ∧
  h.cells a = some { c with val := some v } ∧
  ∀ b, b ≠ a → h.read b = g.read b

theorem valueUpdateFrame_proven : ValueUpdateFrame := by
  intro g a v c hc
  have hex : ∃ h, g.write a { c with val := some v } = .ok h := by
    simp [Heap.write, hc]
  obtain ⟨h,hw⟩ := hex
  refine ⟨h, ?_, ?_, ?_⟩
  · simpa only [setValue, Heap.read, hc, bindOk] using hw
  · have hr := Heap.read_write_same g h a _ hw
    cases hh : h.cells a <;> simp [Heap.read, hh] at hr
    simp [hr]
  · exact fun b hb => Heap.read_write_other g h a b _ hw hb

example : ((Heap.empty.alloc (constantCell (1 : Nat))).2).cells 0 =
    some (constantCell 1) := by rfl

example : ∃ h : Graph Nat,
    ((Heap.empty.alloc (constantCell (1 : Nat))).2).cells 0 = some (constantCell 1) ∧
    setValue ((Heap.empty.alloc (constantCell (1 : Nat))).2) 0 2 = .ok h := by
  exact ⟨_,rfl,rfl⟩

example : getCompositeConstants emptyProtocol emptyComposite [0] = .ok [] := rfl

end DynExpr.NodeUtils
