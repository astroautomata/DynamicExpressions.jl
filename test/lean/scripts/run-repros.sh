#!/usr/bin/env bash
# Run the Julia reproducers listed as refuted in registry.tsv.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../.."

if [[ $# -gt 0 && ( $# != 1 || $1 != --instantiate ) ]]; then
    echo "usage: scripts/run-repros.sh [--instantiate]" >&2
    exit 2
fi
julia --startup-file=no --project=test/lean/repro -e '
    using Pkg
    Pkg.instantiate()
    using DynamicExpressions
    realpath(pkgdir(DynamicExpressions)) == realpath(".") || error("Expected the local DynamicExpressions checkout")
    println("RUNTIME julia=", VERSION, " de=", pkgversion(DynamicExpressions))
'
if [[ $# -eq 1 ]]; then exit 0; fi

ids=$(awk -F '\t' '$2 == "refuted" { print $1 }' test/lean/registry.tsv)
succeeded=0
count=0
while IFS= read -r id && [[ -n "$id" ]]; do
    count=$((count + 1))
    script="test/lean/repro/$id.jl"
    if [[ ! -f "$script" ]]; then
        echo "FAIL $id: missing $script" >&2
        continue
    fi
    status=0
    output=$(julia --startup-file=no --project=test/lean/repro "$script" </dev/null 2>&1) || status=$?
    printf '%s\n' "$output"
    if [[ $status -ne 0 ]]; then
        echo "FAIL $id: Julia exited $status" >&2
    elif grep -Fxq "REPRODUCED $id" <<<"$output"; then
        succeeded=$((succeeded + 1))
    else
        echo "FAIL $id: expected 'REPRODUCED $id'" >&2
    fi
done <<<"$ids"

echo "REPROS $succeeded/$count"
[[ $succeeded -eq $count ]]
