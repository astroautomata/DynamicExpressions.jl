# DynamicExpressions.jl in Lean

This Lean 4 project models the Julia code at commit `65884b65794d014f140aa546736c0aa759dd674e`. In [the property registry](registry.tsv), **proven** means Lean checked a proof about the model under the stated assumptions. **Refuted** means Lean checked a counterexample to the property, with a Julia reproducer for the corresponding behaviour.

The Lean model is maintained separately from the Julia implementation. A Julia source change does not rebuild or recheck the model. Update the matching Lean definitions and proofs when changing modelled behaviour.

## Build and audit

Install [Elan](https://github.com/leanprover/elan) and Python 3. Elan selects the Lean version from `lean-toolchain`. From the repository root:

```sh
cd test/lean
lake build
./scripts/audit.sh
```

See [ARCHITECTURE.md](ARCHITECTURE.md) for the modelling rules and registry checks.

## Run the Julia reproducers

With Julia 1.12 or later, run from the repository root:

```sh
./test/lean/scripts/run-repros.sh
```

The runner uses this checkout of DynamicExpressions.jl and runs the scripts for refuted properties. To run an individual check in `test/lean/repro/`, instantiate with `./test/lean/scripts/run-repros.sh --instantiate`, then run, for example:

```sh
julia --project=test/lean/repro test/lean/repro/eval-alias-checks.jl
```
