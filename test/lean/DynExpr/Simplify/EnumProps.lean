import DynExpr.Simplify.EnumConstruction

/-! Properties of operator enum construction (src/OperatorEnumConstruction.jl). -/

namespace DynExpr.Simplify

open DynExpr

/-- All degrees positive (reasonable input for the pair constructors). -/
def DegreesPos (all : List (Int × List Fn)) : Prop := ∀ q ∈ all, 1 ≤ q.1

/-- Construction from degree pairs with distinct positive degrees places each
tuple at its degree, in the given operator order, fills missing degrees with
empty tuples, and has `maximum(degree)` slots. -/
def enum_pairs_layout : Prop :=
  ∀ (p : Int × List Fn) (ps : List (Int × List Fn)),
    DegreesPos (p :: ps) → ((p :: ps).map Prod.fst).Nodup →
    ∃ ops, pairsToOpsTuple p ps = .ok ops ∧
      ops.length = (ps.foldl (fun m q => max m q.1) p.1).toNat ∧
      (∀ q ∈ p :: ps, ops[q.1.toNat - 1]? = some q.2) ∧
      (∀ d, 1 ≤ d → d ≤ ops.length → (∀ q ∈ p :: ps, q.1 ≠ d) → ops[d - 1]? = some [])

/-- A pair with a degree below 1 is rejected with an `ArgumentError`. -/
def enum_pairs_nonpositive_rejected : Prop :=
  ∀ (p : Int × List Fn) (ps : List (Int × List Fn)),
    (∃ q ∈ p :: ps, q.1 < 1) → ∃ msg, pairsToOpsTuple p ps = .error (.argumentError msg)

/-- Positive degree pairs construct successfully; the last pair for each
degree supplies its tuple, and missing degrees have empty tuples. A pair is
last for its degree exactly when its suffix contains no pair of that degree. -/
def enum_pairs_keep_all_operators : Prop :=
  ∀ (p : Int × List Fn) (ps : List (Int × List Fn)), DegreesPos (p :: ps) →
    ∃ ops, pairsToOpsTuple p ps = .ok ops ∧
      ops.length = (ps.foldl (fun m q => max m q.1) p.1).toNat ∧
      (∀ before q after, p :: ps = before ++ q :: after →
        (∀ r ∈ after, r.1 ≠ q.1) → ops[q.1.toNat - 1]? = some q.2) ∧
      (∀ d, 1 ≤ d → d ≤ ops.length → (∀ q ∈ p :: ps, q.1 ≠ d) → ops[d - 1]? = some [])

/-- Companion of `enum_pairs_keep_all_operators`: with distinct positive
degrees every operator is kept at its degree. -/
def enum_pairs_keep_all_operators_distinct : Prop :=
  ∀ (p : Int × List Fn) (ps : List (Int × List Fn)), DegreesPos (p :: ps) →
    ((p :: ps).map Prod.fst).Nodup →
    ∃ ops, pairsToOpsTuple p ps = .ok ops ∧
      ∀ q ∈ p :: ps, ∀ f ∈ q.2, ∃ tup, ops[q.1.toNat - 1]? = some tup ∧ f ∈ tup

/-- Reasonable enum input: positive degrees, at most 255 operators per degree,
and no operator that is both broadcast and plain. -/
def EnumInput (p : Int × List Fn) (ps : List (Int × List Fn)) : Prop :=
  DegreesPos (p :: ps) ∧ (∀ q ∈ p :: ps, q.2.length ≤ 255) ∧
    (∀ q ∈ p :: ps, ∀ n, Fn.bcast n ∈ q.2 → ∀ q' ∈ p :: ps, Fn.plain n ∉ q'.2)

/-- `lookup_op` inverts construction: after `OperatorEnum(pairs...)` (or
`GenericOperatorEnum`) with default keywords, `lookup_op(f, Val(d))` returns an
index of `f` in the degree-`d` tuple exactly when `f` is in it, and fails
otherwise (or returns 0 with `allow_failure=true`). -/
def enum_lookup_inverts : Prop :=
  ∀ (inBase : Fn → Bool) (kind : EnumKind) (p : Int × List Fn) (ps : List (Int × List Fn))
    (st : Globals), EnumInput p ps →
    ∃ ops st', makeEnum inBase kind p ps true true st = .ok (ops, st') ∧
      ∀ (d : Nat) (f : Fn), 1 ≤ d →
        (f ∈ (ops[d - 1]?.getD []) →
          ∃ i, lookupOp st' f d false = .ok i ∧ (ops[d - 1]?.getD [])[i - 1]? = some f ∧ 1 ≤ i) ∧
        (f ∉ (ops[d - 1]?.getD []) →
          (∃ msg, lookupOp st' f d false = .error (.errorException msg)) ∧
          lookupOp st' f d true = .ok 0)

/-- Generated methods build the node they claim: after `OperatorEnum(pairs...)`
with default keywords, calling a `Base` operator `f` of the enum on nodes (or
a node and a scalar) succeeds and the result denotes `f` applied to the
arguments' values; all-constant calls fold to the direct value. -/
def enum_overload_denote : Prop :=
  ∀ (T : Type) (I : Fn → List T → T) (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st : Globals), EnumInput p ps →
    ∃ ops st', makeEnum inBase kind p ps true true st = .ok (ops, st') ∧
      ∀ (f : Fn), inBase f = true →
        (f ∈ (ops[0]?.getD []) → ∀ l : Tree T, ∃ t', callUnary I st' f l = .ok t' ∧
          ∀ x, t'.denote (opEnumOf I ops) x =
            (do let a ← l.denote (opEnumOf I ops) x; pure (I f [a]))) ∧
        (f ∈ (ops[1]?.getD []) →
          (∀ l r : Tree T, ∃ t', callBinary I st' f l r = .ok t' ∧
            ∀ x, t'.denote (opEnumOf I ops) x =
              (do let a ← l.denote (opEnumOf I ops) x
                  let b ← r.denote (opEnumOf I ops) x
                  pure (I f [a, b]))) ∧
          (∀ (l : Tree T) (b : T), ∃ t', callBinaryNS I st' f l b = .ok t' ∧
            ∀ x, t'.denote (opEnumOf I ops) x =
              (do let a ← l.denote (opEnumOf I ops) x; pure (I f [a, b]))) ∧
          (∀ (a : T) (r : Tree T), ∃ t', callBinarySN I st' f a r = .ok t' ∧
            ∀ x, t'.denote (opEnumOf I ops) x =
              (do let b ← r.denote (opEnumOf I ops) x; pure (I f [a, b]))))

/-- `@extend_operators operators` (default `empty_old_operators=true`) makes
every operator of the enum, including user-defined non-`Base` functions,
usable on nodes: the binary method succeeds and denotes the operator. -/
def extend_operators_user_ops : Prop :=
  ∀ (T : Type) (I : Fn → List T → T) (inBase : Fn → Bool) (ops : List (List Fn))
    (st : Globals),
    (∀ tup ∈ ops, tup.length ≤ 255) →
    (∀ n, (∃ tup ∈ ops, Fn.bcast n ∈ tup) → ∀ tup ∈ ops, Fn.plain n ∉ tup) →
    ∃ st', extendOperators inBase false ops true st = .ok st' ∧
      ∀ (f : Fn), f ∈ (ops[1]?.getD []) → ∀ l r : Tree T, ∃ t',
        callBinary I st' f l r = .ok t' ∧
        ∀ x, t'.denote (opEnumOf I ops) x =
          (do let a ← l.denote (opEnumOf I ops) x
              let b ← r.denote (opEnumOf I ops) x
              pure (I f [a, b]))

/-- A generated binary call either raises an error or builds a node that
denotes the called operator under the enum just built. -/
def BinaryCallSound {T : Type} (I : Fn → List T → T) (st : Globals) (ops : List (List Fn)) : Prop :=
  ∀ (f : Fn) (l r : Tree T),
    (∃ e, callBinary I st f l r = .error e) ∨
    ∃ t', callBinary I st f l r = .ok t' ∧
      ∀ x, t'.denote (opEnumOf I ops) x =
        (do let a ← l.denote (opEnumOf I ops) x
            let b ← r.denote (opEnumOf I ops) x
            pure (I f [a, b]))

/-- `empty_old_operators=false` keeps earlier mappings (intended behaviour,
QUESTIONS.md Q15): after building an enum with helper functions, the mapping
of every operator absent from the new degree tuple is the earlier mapping;
operators of the new enum map to an index of themselves in it; every generated
binary call follows the latest mapping, so calls of new-enum operators error
or build the right node. -/
def enum_keep_old_mappings : Prop :=
  ∀ (T : Type) (I : Fn → List T → T) (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st : Globals),
    EnumInput p ps →
    ∃ ops st', makeEnum inBase kind p ps true false st = .ok (ops, st') ∧
      (∀ d f, f ∉ (ops[d - 1]?.getD []) → 1 ≤ d → st'.mapping d f = st.mapping d f) ∧
      (∀ d f, 1 ≤ d → f ∈ (ops[d - 1]?.getD []) →
        ∃ i, st'.mapping d f = some i ∧ 1 ≤ i ∧ (ops[d - 1]?.getD [])[i - 1]? = some f) ∧
      (∀ f (l r t' : Tree T), callBinary I st' f l r = .ok t' →
        (∃ a b, l = .const a ∧ r = .const b ∧ t' = .const (I f [a, b])) ∨
        ∃ i, st'.mapping 2 f = some i ∧ t' = .branch i [l, r]) ∧
      ∀ f, f ∈ (ops[1]?.getD []) → ∀ l r : Tree T,
        (∃ e, callBinary I st' f l r = .error e) ∨
        ∃ t', callBinary I st' f l r = .ok t' ∧
          ∀ x, t'.denote (opEnumOf I ops) x =
            (do let a ← l.denote (opEnumOf I ops) x
                let b ← r.denote (opEnumOf I ops) x
                pure (I f [a, b]))

/-- With `empty_old_operators=true` (the default), every generated binary call
errors or builds a node denoting the called operator under the new enum. -/
def enum_overload_latest_enum_cleared : Prop :=
  ∀ (T : Type) (I : Fn → List T → T) (inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st : Globals),
    EnumInput p ps →
    ∃ ops st', makeEnum inBase kind p ps true true st = .ok (ops, st') ∧
      BinaryCallSound I st' ops

/-- The deprecated keyword constructors produce exactly the unary and binary
slots `(unary or (), binary or ())`. -/
def enum_kw_shape : Prop :=
  ∀ (inBase : Fn → Bool) (kind : EnumKind) (binary unary : Option (List Fn))
    (helpers emptyOld : Bool) (st : Globals),
    (helpers = true → EnumInput (1, unary.getD []) [(2, binary.getD [])]) →
    ∃ st', makeEnumKw inBase kind binary unary helpers emptyOld st =
      .ok ([unary.getD [], binary.getD []], st')

/-- `GenericOperatorEnum` and `OperatorEnum` build the same operator tuples;
with helpers the latest default enum records the kind and tuples, and without
helpers the global state is untouched. -/
def enum_generic_same_ops : Prop :=
  ∀ (inBase : Fn → Bool) (p : Int × List Fn) (ps : List (Int × List Fn))
    (emptyOld : Bool) (st : Globals), EnumInput p ps →
    ∃ ops st1 st2,
      makeEnum inBase .operatorEnum p ps true emptyOld st = .ok (ops, st1) ∧
      makeEnum inBase .genericOperatorEnum p ps true emptyOld st = .ok (ops, st2) ∧
      st1.latest = some (.operatorEnum, ops) ∧ st2.latest = some (.genericOperatorEnum, ops) ∧
      st1.mapping = st2.mapping ∧
      makeEnum inBase .genericOperatorEnum p ps false emptyOld st = .ok (ops, st)

/-- With helper functions, construction rejects exactly the enums that contain
both `f` and `Broadcast.BroadcastFunction(f)` (distinct positive degrees,
≤ 255 operators per degree). -/
def enum_broadcast_validation : Prop :=
  ∀ (inBase : Fn → Bool) (kind : EnumKind) (p : Int × List Fn) (ps : List (Int × List Fn))
    (emptyOld : Bool) (st : Globals),
    DegreesPos (p :: ps) → ((p :: ps).map Prod.fst).Nodup → (∀ q ∈ p :: ps, q.2.length ≤ 255) →
    ((∃ n, (∃ q ∈ p :: ps, Fn.bcast n ∈ q.2) ∧ (∃ q ∈ p :: ps, Fn.plain n ∈ q.2)) ↔
      ∃ msg, makeEnum inBase kind p ps true emptyOld st = .error (.argumentError msg))

/-- An n-ary call `f(a, b, c)` of a chainable operator (`+`, `*`) that is binary
but not ternary in the latest enum (default keywords) folds left through the
binary method: it denotes `f(f(a, b), c)`. -/
def enum_nary_chain : Prop :=
  ∀ (T : Type) (I : Fn → List T → T) (chainable inBase : Fn → Bool) (kind : EnumKind)
    (p : Int × List Fn) (ps : List (Int × List Fn)) (st : Globals) (f : Fn),
    EnumInput p ps → chainable f = true → inBase f = true → st.defined 3 f = true →
    ∃ ops st', makeEnum inBase kind p ps true true st = .ok (ops, st') ∧
      (f ∈ (ops[1]?.getD []) → f ∉ (ops[2]?.getD []) →
        ∀ a b c : Tree T, [a, b, c].mapM leafConst? = none →
          ∃ t', callNary I chainable st' f [a, b, c] = .ok t' ∧
            ∀ x, t'.denote (opEnumOf I ops) x =
              (do let va ← a.denote (opEnumOf I ops) x
                  let vb ← b.denote (opEnumOf I ops) x
                  let vc ← c.denote (opEnumOf I ops) x
                  pure (I f [I f [va, vb], vc])))

/-- `set_default_variable_names!(v)` stores a copy: later writes to `v` do not
change the stored default names, and the stored names equal `v` at call time. -/
def set_default_variable_names_copies : Prop :=
  ∀ (h : Heap (List String)) (v : Addr) (names : List String) (st : Globals),
    h.read v = .ok names →
    ∃ a h1 st1, setDefaultVariableNames h v st = .ok (a, h1, st1) ∧ st1.varNames = a ∧
      h1.read a = .ok names ∧
      ∀ (newNames : List String) (h2 : Heap (List String)),
        h1.write v newNames = .ok h2 → h2.read st1.varNames = .ok names

end DynExpr.Simplify
