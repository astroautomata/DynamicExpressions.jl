# Lean formalization of DynamicExpressions.jl

This directory models the Julia package in `../../src` in Lean 4 (toolchain
`leanprover/lean4:v4.34.1`, core library only, no Mathlib) and checks
correctness properties against the model. Each property ends as **proven** (a
Lean proof) or **refuted** (a Lean proof of its negation on a concrete
counterexample, plus a Julia script showing the same bug in the real package).

## Layout

| Path | Contents |
|---|---|
| `DynExpr/Runtime/` | Model of the Julia runtime pieces the package relies on: errors, scalar values, arrays/matrices, the mutable heap. |
| `DynExpr/Runtime/Axioms.lean` | The only file allowed to declare axioms (currently none). |
| `DynExpr/Model/` | Shared data model: pure trees, heap-allocated nodes, operator enums, denotational semantics. |
| `DynExpr/<Slice>/` and `DynExpr/<Slice>.lean` | One slice per group of Julia files. The slice root imports the slice's files and defines `DynExpr.<Slice>.entries`. |
| `DynExpr/Registry.lean` | Concatenates every slice's `entries` into `DynExpr.Registry.all`. |
| `Audit.lean`, `Report.lean`, `Restating.lean` | Registry audit, tab-separated report, and checks for overlapping properties. |
| `registry.tsv` | Generated registry: ID, status, kind, quantified inputs, Julia file, statement, preconditions. |
| `QUESTIONS.md` | Questions and rulings about intended Julia behaviour. |
| `repro/` | Julia project using the local checkout, with checks for modelled behaviour and reproducers for refuted properties. |
| `scripts/` | Audit, proof-escape and short-circuit checks, Julia coverage and reproducer runners. |

## Modelling rules

1. **Mirror, then specify.** For each Julia function, write a Lean definition
   that follows the Julia control flow as written, including fast paths,
   early exits, constant-tree shortcuts, fused kernels, buffer reuse, index
   bases, and integer field widths (`UInt8` degree/op, `UInt16` feature) where
   they are reachable. Its docstring cites the Julia `file:line` it mirrors.
   Separately, write the simplest specification of what the function should
   do (usually via `Model` denotations). Properties relate the mirror to the
   specification.
2. **Never fix Julia in the model.** If the Julia code looks wrong, the mirror
   copies the wrong behaviour; the property then fails and gets refuted.
3. **Runtime behaviour is defined, not assumed.** Model Julia semantics with
   definitions in `DynExpr/Runtime` (or slice-local definitions for narrow
   cases). Exceptions are values of `JlError` in the `Jl` monad. Behaviour
   under `@inbounds` with an out-of-range index is `JlError.undefinedBehavior`.
   Add an axiom to `Runtime/Axioms.lean` only when a Julia fact cannot be
   defined in Lean. Document each such assumption in that file.
4. **Operators are arbitrary functions.** User operators are modelled as
   arbitrary total Lean functions `List T → T` and properties quantify over
   them, unless the property is about a specific Julia operator (`+`, `*`,
   `-`, ...). Scalar validity is the abstract `JlValue.valid` (`is_valid`,
   which is `isfinite` for numbers).
5. **Reasonable inputs.** Properties may assume reasonable inputs, stated as
   explicit hypotheses and summarised in the registry entry's
   `preconditions`: finite acyclic trees; `degree ≤ D` with small `D`; at most
   255 operators per degree; feature indices in `1..nfeatures` and below
   65536; well-typed metadata; operators that do not throw. A precondition must
   never assume away the behaviour under test (a NaN-handling property cannot
   assume no NaN), and must be satisfiable: for every proven property with
   hypotheses, add an `example` in the same file exhibiting inputs that satisfy
   them.
6. **Sharing and mutation.** Pure functions on `Node` (which has
   `preserve_sharing = false`) may be modelled on the pure `Tree`. Functions
   that mutate nodes, or that depend on object identity (`GraphNode`,
   `break_sharing`, identity caches, `copy_node` with sharing), are modelled on
   the heap (`Model/NodeHeap.lean`). Aliased subtrees in plain `Node` trees are
   legal Julia (`x * x` reuses `x`), so mutation properties must state whether
   they assume no aliasing.

## Properties and the registry

- A property is a closed `def <name> : Prop` (no universe parameters; write
  `Type`, not `Type u`) in the slice namespace. Quantify inside the `Prop`.
- Register it in the slice's `entries : List DynExpr.Registry.Entry` with the
  Julia file (`src/Foo.jl`), the exact Julia names covered (exported names
  exactly as `names(DynamicExpressions)` prints them, e.g. `@parse_expression`,
  `Node`, `eval_tree_array`), an informal statement, the preconditions, the
  status, `prop`, and `thm`.
- `proven`: `thm` has type exactly `prop`. `refuted`: `thm` has type exactly
  `¬ prop`, proven by exhibiting a concrete counterexample, and
  `repro/<id>.jl` prints `REPRODUCED <id>` when the bug shows in the real
  package (and nothing of that form otherwise).
- **No worked examples.** Every property must quantify over the inputs of the function it is about: all trees,
  operator enums, matrices, values, buffers, ... satisfying the stated
  reasonable-input preconditions. A statement about one fixed tree such as
  `2*x+5` is a test, not a property. Refuted properties are also general
  statements; only their refutation uses a concrete counterexample. The audit
  rejects a general property with no universally quantified data variable;
  padding a concrete statement with an unused `∀` does not count. The only
  exception is `DynExpr.Registry.staticFacts`, a list of IDs for facts about
  package code that takes no inputs (such as include order or a version string).
- `todo` and `stuck` are unsettled statuses and fail the audit.
- Forbidden anywhere in `.lean` files, including comments: the words `sorry`,
  `admit`, `native_decide`. Use `decide` or `simp`/`rfl` on concrete data for
  counterexamples.
- Coverage: across the whole registry, every `src/*.jl` file and every name in
  `names(DynamicExpressions)` must appear in at least one entry.

## Unclear intent

When the intended behaviour of Julia code is unclear (for example, whether a
behaviour is a deliberate early exit or a bug), append an item to
`QUESTIONS.md`: the Julia `file:line`, the two readings, the reading you
modelled and why. Then continue with that reading.

## Building and running

See [README.md](README.md) for build and reproducer commands. For the Julia
coverage check, run the audit and instantiate the reproducer project first,
then run from the repository root:

```bash
julia --project=test/lean/repro test/lean/scripts/check-coverage.jl test/lean/.lake/audit.out
```

The reproducer runner uses the entries marked `refuted` in `registry.tsv`.
Each matching script must exit successfully and print `REPRODUCED <id>` on
its own line. The runner reports `REPROS <succeeded>/<total>`.

## Audit

`scripts/audit.sh` builds everything, scans Lean code for proof escapes,
and rejects new short-circuit hoists. Lean must use `<&&>` or `<||>` when
the right operand performs an action that Julia would skip.
`Audit.lean` requires every entry to be `proven` or `refuted`, checks
each `thm` against `prop` / `¬ prop` by definitional equality, and requires
every theorem's axioms to be among `propext`, `Classical.choice`,
`Quot.sound`, and axioms declared in `DynExpr.Runtime.Axioms`. The audit
prints the registry report and counts for each status. `Restating.lean`
reports candidate duplicate and partially matching properties for review.

Regenerate `registry.tsv` after changing registry entries: run the audit and
copy `test/lean/.lake/registry.tsv` to `test/lean/registry.tsv`.
