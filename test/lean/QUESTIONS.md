# Open questions about intended Julia behaviour

Format per item: `## Q<n> (<slice>): <short title>`, then the Julia `file:line`,
the two readings, the reading modelled, and why. Mark answered items
`(answered: ...)` instead of deleting them.

## Q1 (ParamStruct): Scalar setter input length (answered: bug; the setter must require exact length. Refute.)

`src/ParametricExpression.jl:250-276` and `src/StructuredExpression.jl:162-172`.
One reading allows partial parameter updates and ignores excess values. The other
requires the input length to equal the getter's flattened length. The mirror follows
the loops exactly, including silently ignored values; the correctness properties
use exact-length validation because the public setter takes a full scalar vector
and the ordinary node setter explicitly checks its length. Julia reproductions
confirm short parametric input and excess parametric/structured input are accepted.

## Q2 (ParamStruct): Zero samples with empty classes (answered: bug; zero samples with empty classes must return an empty result. Refute.)

`src/ParametricExpression.jl:378-379`. One reading requires at least one sample.
The other permits a features-by-zero-samples matrix with an empty classes vector.
The mirror retains the empty `maximum` error. The correctness property expects
empty output because the explicit length assertion passes and the ordinary
constant/feature evaluator supports empty sample axes.

## Q3 (ParamStruct): Empty structured member tuple (answered: not a bug; ArgumentError on empty members is acceptable.)

`src/StructuredExpression.jl:94-106`. One reading allows a structure function
that ignores its input and returns a constant expression. The other requires
at least one member so its type and default metadata can be inferred. The mirror
and proven rejection property use the second reading; Julia raises ArgumentError
from `first(values(trees))`. No bug is claimed for this constructor restriction.

## Q4 (Plumbing): Mandatory interface metadata and nonfinite constants (answered: accept the restriction to configured metadata and finite constants.)

`src/Interfaces.jl:83-98,249-250` and `src/Expression.jl:251-254`. One reading
requires every constructible built-in expression, including one with omitted
operator/name metadata or NaN constants, to pass all mandatory checks. The other
requires configured metadata and finite numeric constants for these fixtures.
The model uses the second reading: operator/name checks explicitly require
concrete types, and scalar equality intentionally retains Julia NaN inequality.
The proven interface properties state these restrictions; they do not establish
the checks for all constructible expressions or aliased graphs.

## Q5 (Plumbing): Deprecation requests versus printed warnings (answered: a Base.depwarn request is the right promise.)

`src/deprecated.jl:1-118`. One reading promises a visible warning on every legacy
call. The other promises a Base.depwarn request subject to Julia configuration
and warning deduplication. The model uses the second reading because Base
controls suppression outside the package. Forwarding includes exceptions and
heap effects regardless of whether a warning is printed.

## Q6 (NodeUtils): Independent constants versus aliased plain Node leaves (answered: plain Node trees must never contain aliased nodes. Drop the aliasing refutation; instead prove that the package's own node-building and mutating operations never create aliasing from alias-free, mutually disjoint inputs. Handled by the NoAlias slice.)

`src/NodeUtils.jl:94-96,102-107,124-128`. One reading promises that setting
the getter's scalar vector produces that vector on the next getter call. The
other treats duplicate refs in plain Node as tied parameters, with the final
write determining every occurrence. The mirror follows the actual duplicate
refs and final-write behaviour. The refuted property uses the first reading
because the documented depth-first getter/setter interface does not state
that different scalar-vector entries can designate the same mutable value.
Unchanged-vector round trips are proven even with aliases.

## Q7 (NodeUtils): Undersized preallocated storage (answered: callers must provide adequate capacity.)

`src/NodePreallocation.jl:44,47`. One reading requires a catchable bounds
exception for a destination smaller than the source. The other places adequate
capacity on the caller and permits unchecked behaviour on insufficient storage.
The mirror uses the second reading because both accesses use `@inbounds`; an
invalid slot is `JlError.undefinedBehavior` under ARCHITECTURE.md. The proven
capacity property records that undefined access rather than promising a
BoundsError or safely testing potentially invalid memory in Julia.

## Q8 (NodeUtils): Zero-scalar composite constants (answered: bug; get-then-set must round-trip for a lawful zero-scalar value type. Refute.)

`src/ValueInterface.jl:98-113,119-136,138-140` and `src/NodeUtils.jl:130-140`.
One reading permits composite values with zero scalar constants, such as an
empty vector. The other requires strictly positive counts at every constant
leaf. The model uses the first reading: the interface requires an integer count
and checks pack/unpack advancement by that count, without a positivity rule.
A lawful empty-vector implementation passes those checks, but the tree setter
raises an error when given the getter's empty vector.

## Q9 (NodeUtils): UInt16 constant-index capacity (answered: unreasonable input; add a precondition of at most 65535 constant leaves (and, generally, UInt16 index ranges), then prove.)

`src/NodeUtils.jl:184-200`. One reading implicitly limits trees to 65535
constant leaves when using the default index type. The other expects every
finite acyclic tree to have usable nonzero indices, or an explicit overflow
error. The mirror retains wrapping UInt16 arithmetic. The refuted property
uses the second reading because neither the function signature nor a local
check states a constant-count restriction; a balanced 65536-leaf tree reaches
the collision with the zero marker without deep recursion.

## Q10 (Expressions): Invalid probability weights (answered: bug; reject negative and nonfinite weights, provided the check is cheap.)

`src/Random.jl:23-26,61-94`. One reading requires callers to supply finite,
nonnegative weights with positive total. The other requires NodeSampler to
reject weights that cannot represent probabilities. The mirror preserves the
implementation: negative values are accepted, and nonfinite weights can cause
a TypeError or be accepted depending on preceding cumulative values. The general
negative/nonfinite-weight rejection properties use the second reading because
the documented weights are proportional to sampling probability and zero totals
are explicitly rejected. Reproducers show [-1,2,1] at draw zero and [1,-Inf,1] at
draw one-half produce nodes instead of errors.

## Q11 (Deriv): Tangents from different trees (answered: not a bug.)

`src/ChainRules.jl:22-28`. One reading requires both the extraction target
and added tangents to refer to the same tree. The other treats the tree field
as metadata and leaves matching to callers. The mirror follows the second
reading because extraction ignores its tree argument and addition's equality
assertion is commented out. No bug is claimed for cross-tree tangent algebra.

## Q12 (Deriv): Directional completion and gradient early exits (answered: bug.)

`src/EvaluateDerivative.jl:35-38,87-118,238-242,301-309`. One reading promises
false completion for any nonfinite primal or derivative, as the public return
documentation states. The other treats directional completion as a structural
success flag while only the full gradient evaluator checks finite values.
The mirror retains directional complete=true and the gradient's recursive
finite checks. The directional validity property uses the documented reading
and is refuted by both an Inf leaf and division by zero. Gradient completion
describes the returned child or final result: an invalid child exits before
a parent operator could turn it into a finite value.

## Q13 (Deriv): Empty sample pullbacks (answered: bug.)

`src/ChainRules.jl:71-73`. One reading permits any feature-by-sample matrix
accepted by evaluation, including zero sample columns. The other implicitly
requires at least one sample for reverse differentiation. The mirror retains
the zero-sample ArgumentError from sum without an initial vector. The refuted
property uses the first reading because the primal rule completes successfully
for both constant and feature leaves with zero columns.

## Q14 (Simplify): Repeated degree keys in OperatorEnum (answered: not a bug; repeated degrees behave like `Dict` with repeated keys, so the last one wins. Restate as last-write-wins and prove.)

`src/OperatorEnumConstruction.jl:409-427`. One reading treats
`OperatorEnum(1 => (sin,), 1 => (cos,))` as a user error that should raise or
merge the tuples. The other accepts last-write-wins. The mirror keeps the
overwrite. The refuted property `simplify-enum-duplicate-degree` uses the first
reading because `sin` silently disappears from the enum, the operator mapping
and the generated methods, with no warning.

## Q15 (Simplify): `empty_old_operators=false` and stale operator indices (answered: not a bug; keeping old mappings with empty_old_operators=false is intended. Restate as proven: the call follows the latest mapping.)

`src/OperatorEnumConstruction.jl:97-112,334-347`. One reading says
`empty_old_operators=false` only keeps old methods usable while the new enum is
the default. The other says the kept mapping is an intended feature and the
user must not build nodes with operators missing from the new enum. The mirror
keeps the old mapping. The refuted property `simplify-enum-stale-mapping` uses
the first reading: after `OperatorEnum(2 => (+, *))` then
`OperatorEnum(2 => (*,); empty_old_operators=false)`, `x1 + x2` silently builds
`x1 * x2` under the new enum, while the default keyword raises an error.

## Q16 (Simplify): `combine_operators` on ParametricExpression (answered: bug.)

`src/PatchMethods.jl:11-18`, `src/Simplify.jl:22-25`. One reading treats the
`ParametricExpression` wrapper method as intended to combine operators like the
`Expression` one. The other treats it as an intentional no-op because the tree
method is only specialised for `Node{T,2}`. The mirror dispatches exactly so.
The refuted property `simplify-patch-combine-parametric` uses the first
reading because the wrapper explicitly lists `ParametricExpression`.

## Q17 (Simplify): `combine_operators` mutates its input (answered: bug.)

`src/Simplify.jl:25-116`, `src/PatchMethods.jl:11-18`. One reading follows
Julia's `!` convention: `combine_operators` (no `!`) must leave its argument's
value unchanged. The other treats it as an in-place function whose input must
be discarded, like `simplify_tree!`. The mirror mutates in place. The refuted
property `simplify-combine-input-mutated` uses the first reading: after
`combine_operators((x1 + 1) + 2)` the input object denotes `(x1 + 3) + 2`.
The `Expression` wrapper (`src/PatchMethods.jl`) inherits the same effect.

## Q18 (StringsParse): Empty custom renderers and callable names (answered: not a bug; empty renderer output and empty operator names are unreasonable input. Make nonempty names a precondition and prove.)

`src/Strings.jl:76-82,111-134,154-155,198`. One reading permits any String
from the documented custom leaf renderers, including an empty String, and
any callable show method. The other requires nonempty renderings without
stating that condition. The mirrors retain the unguarded first/last accesses.
The refuted properties use the first reading because the signatures accept
these well-typed outputs and the documentation gives no nonempty restriction.

## Q19 (StringsParse): Float32 type preservation on text round trips (answered: not a bug; string_tree is display text. Restate type-agnostic: the value round-trips.)

`src/Strings.jl:92-98` and `src/Parse.jl:296,595-596`. One reading expects
rendering and reparsing a Float32 constant to retain its scalar type. The other
treats string_tree as display text and permits default Float64 inference. The
model follows Julia string, which prints 1.25f0 as 1.25, and refutes type
preservation. This counterexample does not change the numeric value of 1.25.

## Q20 (StringsParse): node_type for pre-built nodes (answered: bug, minor.)

`src/Parse.jl:258,593-594`. One reading expects node_type to constrain or
convert every parsed node. The other treats a pre-built node as an explicit
type override. The mirror returns it unchanged; the requested GraphNode
property is refuted by a caller-owned Node. Live-object exposure is permitted
under the settled ownership ruling; only the ignored type request is at issue.

## Q21 (StringsParse): Scope of floating-point textual semantics (answered: accepted; exact terminating decimals, no IEEE model.)

`src/Strings.jl:92-98` and `src/Parse.jl:296`. One reading requires bit-exact
IEEE shortest-digit rendering and parsing for every finite Float32/Float64.
The other uses the shared JF exact-rational abstraction for finite values.
The slice uses the second reading, with a defined decimal/scientific parser
and a printer restricted to exact terminating decimals of at most 40 digits.
The proven literal cases include scientific notation, negative decimals, and
f-suffixed input; signed zero and general IEEE rounding are outside this
runtime model. Float32 suffix loss and nonfinite rejection are retained and
checked in real Julia, rather than corrected in the mirror.


## Q22 (NodeBase): `set_children!` with more than `D` children (answered: bug.)

`src/Node.jl:234-251`. One reading treats more than `D` children as caller error
with unspecified results. The other expects an error, as the constructor asserts
`length(children) <= max_degree(N)` (`src/Node.jl:409`). The mirror keeps the
silent truncation to the first `D` children; the refuted property
(`nodebase-set-children-total`) uses the second reading because dropping a child
without any signal can only hide a bug. The proven `nodebase-set-children`
covers `length(cs) <= D`.

## Q23 (NodeBase): `set_node!` and inactive fields (answered: not a bug; inactive fields are undefined. Restate set_node! over the active fields and prove.)

`src/Node.jl:467-494`. The docstring says every field is copied; the code
copies only the fields active for `new_tree`'s kind, so a constant leaf
overwritten by a branch keeps `constant == true`. One reading treats inactive
fields as undefined (the `Node` docstring marks `val`/`feature`/`op` as
"only defined if ..."); the other follows the docstring literally. Modelled as
written; `nodebase-set-node-fields` is refuted on the `constant` flag, which the
docstrings never mark as undefined. The proven `nodebase-set-node` shows the
expression and children are copied correctly.

## Q24 (NodeBase): Abstract element types in `copy_node` (answered: Miles marked it a bug but asked what `copy(Real[1.0])` does: Base keeps the eltype (Vector{Real}). Treated as a bug by that analogy: copy_node should keep Node{Real}.)

`src/base.jl:501-510`. One reading supports only concrete element types, so
`copy_node(Node{Real}(val=1.0))` returning a `Node{Float64}` is acceptable. The
other expects `copy` to preserve the tree's type for any `T`. Refuted
(`nodebase-copy-type`) under the second reading, since `leaf_copy` passes `T`
for features but not for constants and the branch constructor ignores `T`.

## Q25 (NodeBase): Degree handling in `==` and in bare-wrapper constructors (answered: bug, low priority.)

`src/base.jl:193-195`, `src/Node.jl:403-416,457-465`. (a) `==` between nodes of
different maximum degree throws from `promote` instead of returning `false`.
(b) `Node(; op, children)` with `Node{T,3}` children and `convert(Node, t::Node{T,3})`
throw because the bare wrapper defaults `D` to 2. One reading restricts users to
`D = 2` with the bare wrapper and to same-degree comparisons; the other expects
`D` to follow the inputs (as `T` does) and `==` to be total. Refuted under the
second reading (`nodebase-eq-no-throw`, `nodebase-ctor-children-degree`,
`nodebase-convert-unparam`).

## Q26 (NodeBase): `Node{T}(; r=x)` without `l` (answered: bug.)

`src/Node.jl:350-363`. One reading treats `r` without `l` as unsupported; the
other expects either an error or a node containing `x`. The code silently returns
an uninitialised node (garbage degree, undefined children). Refuted
(`nodebase-ctor-child-arg`) under the second reading.

## Q27 (Eval): Fused kernels and non-finite feature inputs (answered: bug; fused and unfused paths must agree.)

`src/Evaluate.jl:875-934, 694-762, 26-32`. The unfused path stops with flag
false as soon as any child array (including a feature leaf read from `X`)
contains NaN/Inf. The fused kernels read feature leaves without that check, so an
operator that maps a non-finite input to a finite value completes: `1.0 / x1` at
`x1 = Inf` returns `([0.0], true)` fused and `([Inf], false)` unfused. One
reading: the flag means "no NaN/Inf at any step" (docstring of `early_exit`), so
the fused result is wrong. The other: only operator outputs matter and the
unfused leaf check is overly strict. Modelled as written; the property that the
flag is independent of `use_fused` is refuted (`eval-fused-flag-agree`), and the
unfused flag is proven to mean exactly "every intermediate valid"
(`eval-unfused-flag`).

## Q28 (Eval): `early_exit=false` and constant trees (answered: not a bug; constant trees may exit early. Restate with a non-constant-tree precondition and prove.)

`src/Evaluate.jl:348-355, 140-147`. `early_exit=false` is documented as
disabling early termination, but the constant-tree shortcut returns flag false
and uninitialised storage whenever an intermediate constant is invalid, even if
the final value is finite (`inv(inv(0.0))`). One reading: constant trees are
exempt. The other: `early_exit=false` should evaluate them like any other tree.
Modelled as written; refuted under the second reading (`eval-noearly-denote`).

PR #269 subsequently made constant trees and subtrees honor `early_exit=false`
(`src/Evaluate.jl:319-328,983-1025`). `eval-noearly-denote` is proven against
that implementation.

## Q29 (Eval): Feature indices beyond `size(X, 1)` on plain nodes (answered: bug; the fix must not cost performance, e.g. one up-front bounds check per call rather than per element.)

`src/Evaluate.jl:106-128`. Feature indices outside `1..size(X,1)` are outside
the reasonable-input contract, but the evaluator reads them under `@inbounds`
and silently returns other rows' values or memory past the matrix
(`x3 + 2.0` on a 2x3 matrix gives `[4.0, 5.0, 2.0]`). Expression wrappers
validate inputs; plain `Node` evaluation does not. The property "an
out-of-range feature raises BoundsError" is refuted (`eval-feature-oob`) as a
memory-safety finding; no in-contract property depends on it.

## Q30 (StringsParse): Shared GraphNode display and reparsing (answered: not a bug; brace markers are display-only. Restate with an unshared-graph precondition and prove.)

`src/Strings.jl:189-198` and `src/Parse.jl:386-391`. One reading treats
the brace sharing markers as human-readable display only. The other expects
string_tree output to be accepted by parse_expression with matching operators,
names, and GraphNode type. The mirrors retain the braces and parser rejection
of Expr(:braces, ...). The round-trip property uses the second reading and is
refuted on a finite, acyclic x1+x1 graph with one shared feature. Sharing is
legal for GraphNode under the settled ownership contract.

## Q31 (NodeUtils): Mutable constant payloads in recursive tree copies (answered: yes; tree copies must own independent copies of mutable constant values such as Vector constants. nodebase-copy-value-fresh and paramstruct-composite-copy stay refuted.)

`src/NodePreallocation.jl:52-54` copies a constant using `set_node!`;
`src/Node.jl:484` assigns its value object directly. A copied
`Node{Vector{Float64}}(val=[1.0,2.0])` therefore shares its vector with the
source. Does the recursive-copy promise include independently owned mutable
constant values, or only independently owned nodes? The best-guess reading
includes supported composite constant values. The parent retained the single
`nodebase-copy-value-fresh` finding and removed the duplicate NodeUtils finding.
`nodeutils-copy-immutable-values` proves the copy_into! guarantee when reachable
constant payloads are immutable scalar values.

The parent separately ruled that immutable enum copies retain their operator
objects, and that scalar getters retain their returned element objects. Those
ordinary shallow-copy and map behaviours are accepted, including mutable
callable and mutable Number objects; they are not bugs.

## Q32 (NodeBase): Signed zero and tree hashes (answered: not a bug; Julia's own floats have `0.0 == -0.0` but `hash(0.0) != hash(-0.0)`, so trees follow the same convention. Restate hash agreement over `isequal`-equal constants and prove.)

`nodebase-hash-eq` originally required `==`-equal trees to hash equally and was
refuted with `0.0` vs `-0.0` constants. Miles ruled this mirrors Julia's float
semantics. The property now quantifies over trees whose constants agree under
`isequal`, which matches Julia's hash contract, and is proven.

## Q33 (Simplify): Repeated degree keys and Dict semantics (answered: not a bug; repeated degrees behave like `Dict` with repeated keys, so the last one wins. Restate as last-write-wins and prove.)

`simplify-enum-duplicate-degree` originally required every supplied operator
to survive and was refuted with `OperatorEnum(1 => (sin,), 1 => (cos,))`.
Miles reversed Q14's ruling: repeated keys follow Julia's `Dict` convention.
The property now states successful construction for positive degrees, with
the last tuple at each supplied degree and empty tuples at missing degrees,
and is proven.

## Q34 (StringsParse): Macro keyword diagnostics and soft deprecation (answered: not a bug; omit soft-deprecated binary_operators and unary_operators from the diagnostic to recommend operators. Restate as the exact non-deprecated keyword list and prove.)

`stringsparse-macro-keywords` originally required the first invalid-keyword
diagnostic to list every accepted keyword and was refuted because it omits
`binary_operators` and `unary_operators`. Miles ruled that these keywords are
soft-deprecated and should remain accepted without appearing in the diagnostic.
The property now states the exact seven non-deprecated diagnostic keywords and
continued acceptance of both omitted keywords, and is proven.

## Q35 (NoAlias): Passing one tree twice to a node constructor (answered: not a bug; aliasing that the caller creates, as in `Node(op, x, x)` or `x * x`, is accepted. Restate as the constructor storing the caller's object in both slots and prove.)

`noalias-node-ctor-repeated-child` originally required `Node(; op,
children=(x, x))` to return an alias-free tree and was refuted because the
new node stores `x` in both slots (`src/Node.jl:407-430, 235-254`). Miles ruled
that this user-created aliasing is accepted (as in Q6, the package itself must
not create aliasing from disjoint inputs, which noalias-node-ctor and its
siblings prove). The property now states that the call succeeds, allocates one
new node whose two children are both `x`, keeps `x` alias-free, and changes no
existing object, and is proven.

## Q36 (NodeUtils): Composite round trip needs slot-local value protocols (modelling decision for PR #250; no ruling needed.)

`nodeutils-composite-empty` quantifies over every lawful numeric-vector value
protocol. After PR #250 the setter visits every ref (`src/NodeUtils.jl:134-139`),
but the statement is still false for a protocol whose `pack_scalar_constants!`
also overwrites slots of earlier values: each value round-trips on its own, yet
packing a later value clobbers an earlier one, so no setter can restore it. The
property therefore adds `VectorProtocolLocal` (pack writes only its own slots,
unpack reads only its own slots), which every real protocol, including the
reproducer's `Vector{Float64}` protocol (`emptyProtocolLocal_proven`),
satisfies. With that hypothesis it is proven.

## Q38 (Eval): Fused kernels and non-finite inputs under early exit (answered: documented behaviour, not fixed; PR #276 documents on `use_fused` that with `early_exit=true` fused kernels check only their outputs. Restate as that documented behaviour and prove.)

`eval-fused-flag-agree` originally required the completion flag to be the
same for `use_fused=true` and `use_fused=false` and was refuted with `1.0 / x1`
at `x1 = Inf`, which returns `([0.0], true)` fused and `([Inf], false)`
unfused. Miles ruled that this is intended and should be documented rather
than fixed. The property now states the documented behaviour: whenever the
unfused call completes with flag true, the fused call completes with the same
output and flag true (the fused flag is never stricter), and the two flags
agree when every input entry is finite. It is proven.

## Q47 (ParamStruct): Setter input that shares memory with the parameters (answered: documented precondition; PR #274 documents on `set_scalar_constants!` that `constants` must not share memory with the expression's own parameters, e.g. a view of them. Restate with that precondition and prove.)

`paramstruct-overlapping-parameter-input` and
`paramstruct-overlapping-structured-input` originally required the setters to
preserve the input snapshot for any overlapping view and were refuted with the
reversed view `view(vec(P), 2:-1:1)`, which yields `[20.0, 20.0]`. Miles ruled
this a documented precondition rather than a bug. Both properties now assume
that the input shares no memory with the destination parameters
(`src/NodeUtils.jl:123-124`) and are proven; the reversed-view reproducer lies
outside the precondition.

## Q48 (ParamStruct): What empty-class evaluation should return (modelling decision for PR #246; no ruling needed.)

`paramstruct-empty-classes` originally required evaluation on a zero-column
matrix with empty classes to return an empty array with flag `true`. PR #246
removes the `maximum(classes)` failure, so the call now reaches the ordinary
evaluator. That evaluator still reports flag `false` for zero-sample trees with
an invalid constant subtree (for example `inv(0.0)`), which the
eval-zero-samples-* properties cover. The property is restated as the fixed
behaviour: with empty classes and zero samples, `eval_tree_array` raises no
class-handling error and passes the converted tree and a
`(size(parameters, 1) + size(X, 1)) x 0` augmented matrix to the ordinary
evaluator. It is proven.

## Q40 (StringsParse): Unary `+` power bases after PR #228 (answered: not a bug; unary `+` is the identity, so `+(x1) ^ x2` and `+(x1 ^ x2)` have equal values and only the tree shape differs; printed constants never start with `+`.)

PR #228 brackets a `^` base whose rendering starts with `-`, so negative
constants and unary `-` calls now roundtrip exactly. A unary `+` base still
prints as `+(c) ^ b`, which Julia parses as `+(c ^ b)`. Following Miles's
ruling on #228, stringsparse-negative-power states that power trees without a
unary `+` base reparse to their expected tree, and that every clean tree keeps
its value when unary `+` operators are the identity. Both clauses are proven.

## Q41 (StringsParse): Variables named `NaN` or `Inf` (modelling decision by analogy with Q21.)

PR #229 normalizes the symbols `NaN` and `Inf` to constants unless they are
declared in `variable_names`. A declared `Inf` makes the printed `Inf` a feature
reference, and without a unary `-` operator the printed `-Inf` fails to parse.
As Q21 does for a variable named `im`, stringsparse-nonfinite requires the
names vector to exclude `NaN` and `Inf`. It is proven.

## Q42 (StringsParse): Partial `variable_names` and `x<i>` fallback names (answered: not a bug; partial variable_names fall back to xN.)

stringsparse-feature-collision now states the documented behaviour: supplied
names print within the names vector and `x<i>` beyond it, and all valid features
print distinctly when the supplied names are unique and none spells the fallback
of a later index. It is proven.

## Q43 (StringsParse): Complex constants with a variable named `im` (answered by Q21: not a bug.)

stringsparse-complex-variable now states that a declared `im` shadows the
imaginary unit while the nonfinite folds of PR #229 still apply, and that every
constant roundtrips when `NaN`, `Inf`, and `im` are undeclared. It is proven.

## Q44 (StringsParse): Operator-name cache after PR #231 (modelling decision; no ruling needed.)

PR #231 caches names by `objectid` only for singleton callable types. The model
takes as given that singleton callables with one `objectid` are one object and
so print one name; under that assumption every sequence of `get_op_name` calls
returns each callable's own name. stringsparse-cache-collision is proven.

## Q50 (Simplify): `combine_operators!` and the deprecated `combine_operators` after PR #251 (modelling decision following the Q17 ruling; no ruling needed.)

`src/Simplify.jl:32-129`, `src/PatchMethods.jl:11-18`. PR #251 renamed the
mutating function to `combine_operators!` and kept `combine_operators` as a
`Base.@deprecate` alias. Under the Q17 ruling the bug was the missing `!`, so
simplify-combine-input-mutated is restated as the contract the new name
promises: `combine_operators!` returns the combined tree, writes only to
objects of the input tree, and visibly mutates its argument on some inputs
(`(x1 + 1.0) + 2.0` afterwards denotes `(x1 + 3.0) + 2.0`), while every
deprecated form returns exactly what `combine_operators!` returns. The
deprecation warning is not modelled; with `--depwarn=error` the deprecated
calls throw instead. It is proven.

## Q51 (Simplify): `ParametricNode` contents in `combine_operators!` (modelling decision; no ruling needed.)

`src/Simplify.jl:32-35`. After PR #251 the tree method accepts every
`AbstractExpressionNode{T,2}` whose type does not preserve sharing, so
`ParametricExpression` contents get the same rewrites as `Expression`
contents (the Q16 reading). A parameter leaf has `constant == false`, so
`is_node_constant` is false and the rewrites never read or write it; the model
treats it as a feature leaf. simplify-patch-combine-parametric is proven, and
the companion simplify-patch-combine-parametric-identity (the old no-op) is
replaced by simplify-patch-combine-parametric-spec, the ParametricExpression
analogue of simplify-patch-combine-expression.

## Q55 (StringsParse): Input conditions of the broadcast roundtrip after PR #230 (modelling decision; no ruling needed.)

`src/Strings.jl:53-66,106-133`, `src/Parse.jl:304-345,389-394`. PR #230
rewrites the printed dot call `f.(args...)` into a call of the symbol `f.` and
matches a `Broadcast.BroadcastFunction` operator by its `get_op_name` spelling.
The earlier statement of stringsparse-broadcast assumed only identifier
operator and variable names, unique variable names, and well-formed trees.
Two readings:

1. Every such tree reparses. On master this fails for inputs outside the
   broadcast change: two broadcast callables whose functions share a name at
   one degree both print `cos.`, and `_find_operator_by_name` throws
   "Ambiguous operator" (a Lean `example` in `GeneralBroadcast.lean` shows
   it); a complex constant does not fold back into one constant, so its
   printed sum fails to parse, when `im` is a variable (Q43) or a nonfinite
   part is spelled by a variable named `NaN` or `Inf` (Q41); reserved words
   such as `end` and Unicode operator characters allowed by `identifier` are
   not plain symbols for `Meta.parse`.
2. These are unreasonable inputs, as already ruled for the other roundtrip
   properties: names follow `CleanNames` and operator names are plain and
   unique per degree (stringsparse-clean-serialization), and constants follow
   the stringsparse-nonfinite conditions (finite parts terminating decimals,
   `NaN` and `Inf` undeclared, `im` undeclared for complex constants).

The model uses reading 2, with an explicit `broadcast` flag on each operator
for `op isa Broadcast.BroadcastFunction`. stringsparse-broadcast is proven:
every such tree renders, and its text parses to some tree.
