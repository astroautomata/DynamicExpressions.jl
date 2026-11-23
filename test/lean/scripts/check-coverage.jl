# Check that the property registry covers every src/*.jl file and every name
# exported by DynamicExpressions.jl.
#
# Usage: julia --project=test/lean/repro test/lean/scripts/check-coverage.jl test/lean/.lake/audit.out
using DynamicExpressions

audit_out = only(ARGS)
lines = readlines(audit_out)
covered_files = Set(
    chopprefix(l, "COVER-FILE ") for l in lines if startswith(l, "COVER-FILE ")
)
covered_fns = Set(chopprefix(l, "COVER-FN ") for l in lines if startswith(l, "COVER-FN "))

repo_root = realpath(joinpath(@__DIR__, "..", "..", ".."))
realpath(pkgdir(DynamicExpressions)) == repo_root ||
    error("Expected the local DynamicExpressions checkout")
src_dir = joinpath(repo_root, "src")
expected_files = sort(["src/" * f for f in readdir(src_dir) if endswith(f, ".jl")])
expected_fns = sort([
    String(n) for n in names(DynamicExpressions) if n != :DynamicExpressions
])

missing_files = setdiff(expected_files, covered_files)
missing_fns = setdiff(expected_fns, covered_fns)
unknown_files = setdiff(covered_files, expected_files)

for f in sort(collect(missing_files))
    println("MISSING-FILE ", f)
end
for f in sort(collect(missing_fns))
    println("MISSING-FN ", f)
end
for f in sort(collect(unknown_files))
    println("UNKNOWN-FILE ", f)
end
println(
    "FILES ", length(expected_files) - length(missing_files), "/", length(expected_files)
)
println("EXPORTS ", length(expected_fns) - length(missing_fns), "/", length(expected_fns))

if isempty(missing_files) && isempty(missing_fns) && isempty(unknown_files)
    println("COVERAGE OK")
else
    println("COVERAGE FAIL")
    exit(1)
end
