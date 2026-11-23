import DynExpr.Registry.Types
import DynExpr.Arena.Properties
import DynExpr.Arena.Simulation
import DynExpr.Arena.Any
import DynExpr.Arena.Copy

namespace DynExpr.Arena

open DynExpr.Registry in
def entries : List DynExpr.Registry.Entry := [
  { id := "arena-get-child"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["get_child", "get_children", "unsafe_get_children"]
    statement := "A valid parent returns a child handle in its own arena at the stored one-based index. An empty slot throws UndefRefError, and a slot outside the tuple throws BoundsError."
    preconditions := "Parent index names an initialized entry; slot number is nonnegative."
    status := .proven
    prop := ``child_bounds
    thm := some ``child_bounds_holds },
  { id := "arena-push-handles"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["Arena", "ArenaNode", "push!", "_reserve!"]
    statement := "Appending an entry preserves every old vector location even when the backing vector grows, so existing handles still name the same entries."
    preconditions := "Append succeeds; the appended index fits Int32."
    status := .proven
    prop := ``pushes_preserve_handles
    thm := some ``pushes_preserve_handles_holds },
  { id := "arena-scalar-write-frame"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["setproperty!", "getproperty"]
    statement := "Writing a scalar value is visible through every handle to that arena entry. The write leaves the compact flag and other entries unchanged."
    preconditions := "Handle names an initialized entry; assigned value already has the arena scalar type."
    status := .proven
    prop := ``scalar_frame
    thm := some ``scalar_frame_holds },
  { id := "arena-same-arena-child"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["_resolve_child_index!", "set_child!", "set_children!", "set_node!"]
    statement := "When the parent and child share an arena, resolving the child for attachment retains its exact index without copying or changing any entries."
    preconditions := "Parent and child handles have the same arena identifier and type parameters."
    status := .proven
    prop := ``same_arena_identity
    thm := some ``same_arena_identity_holds },
  { id := "arena-mapreduce-simulation"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["tree_mapreduce", "convert"]
    statement := "Tree reduction agrees with reduction on the converted plain Node, including errors returned by the callbacks."
    preconditions := "Finite acyclic tree convertible to Node. Callbacks observe only active leaf payloads or branch operator and degree and do not mutate the input."
    status := .proven
    prop := ``mapreduce_simulation
    thm := some ``mapreduce_simulation_holds },
  { id := "arena-hash-simulation"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["hash"]
    statement := "For any seed, ArenaNode and the corresponding Node submit the same tree data to the hash function and return the same hash."
    preconditions := "Finite acyclic tree convertible to Node."
    status := .proven
    prop := ``hash_simulation
    thm := some ``hash_simulation_holds },
  { id := "arena-compact-copy"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["copy_node", "copy"]
    statement := "Copying a compact root preserves the root index and every entry in its own vector, with capacity for D+1 extra nodes."
    preconditions := "The source is a compact root."
    status := .proven
    prop := ``compact_copy
    thm := some ``compact_copy_holds },
  { id := "arena-copy-into-metadata"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["copy_into!", "allocate_container"]
    statement := "After successful copy_into!, the destination is compact-marked and the reported count equals the destination's entry count."
    preconditions := "The copy succeeds; the optional count reference can represent the count."
    status := .proven
    prop := ``copy_into_metadata
    thm := some ``copy_into_metadata_holds },
  { id := "arena-any-pure"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["any"]
    statement := "For a pure predicate, the short-circuit Boolean result agrees with a root-first traversal."
    preconditions := "Reachable entries are initialized and acyclic. In compact storage each reachable entry occurs exactly once and there are no orphaned entries."
    status := .proven
    prop := ``any_pure
    thm := some ``any_pure_holds
    notes := "Compact storage visits children before the root; Node visits the root first. A root match can therefore take more predicate calls on the ArenaNode. Order is undocumented." },
  { id := "arena-mixed-child-type"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["ArenaNode", "node_factory", "set_children!"]
    statement := "Keyword branch construction accepts convertible constant children of different scalar types after promotion, as Node does."
    preconditions := "A binary branch; both numeric values are representable at the promoted type."
    status := .refuted
    prop := ``mixed_child_type
    thm := some ``mixed_child_type_fails
    notes := "P3. The factory accepts Float64 as the promoted type, then _resolve_child_index! rejects the Float32 child. Normal keyword construction can hit this. Verified at 465d0ec1 on Julia 1.12.6." },
  { id := "arena-copy-mutable-value"
    juliaFile := "src/ArenaNode.jl"
    juliaFns := ["copy", "copy_node"]
    statement := "Copying a constant with a mutable numeric value returns an independent scalar object, as Node copy does."
    preconditions := "A constant BigInt leaf."
    status := .refuted
    prop := ``copy_mutable_value
    thm := some ``copy_mutable_value_fails
    notes := "P3. A BigInt leaf and its copy hold the same object; an in-place GMP update through the copy changes the original. Node applies copy_value to detach mutable numeric values. Verified at 465d0ec1 on Julia 1.12.6." }
]

end DynExpr.Arena
