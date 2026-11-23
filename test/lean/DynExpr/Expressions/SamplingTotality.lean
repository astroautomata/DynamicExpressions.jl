import DynExpr.Expressions.Aliasing

namespace DynExpr.Expressions.SamplingTotality

/-- Filtering for NodeSampler is total on finite decoded source heaps,
src/Random.jl:54,63-65. Decoding is a source-memory validity condition;
no successful traversal, filtering or sampling result is assumed. -/
def matchingSuccessProperty : Prop := ∀ (s : Sampling.NodeSampler JF),
  (∃ tree, s.graph.unfold s.fuel s.root = some tree) →
  ∃ nodes, Sampling.matching s = .ok nodes

theorem matchingSuccess_proven : matchingSuccessProperty := by
  intro s decoded
  obtain ⟨⟨nodes, traversal⟩, _⟩ := Aliasing.scalarGetterSuccess_proven
    s.graph s.root s.fuel s.preserveSharing s.breakSharing Heap.empty decoded
  refine ⟨nodes.filter s.filter, ?_⟩
  simp [Sampling.matching, traversal, bind, Except.bind] <;> rfl

example : ∃ s : Sampling.NodeSampler JF,
    ∃ tree, s.graph.unfold s.fuel s.root = some tree := by
  let graph : Graph JF := (Heap.empty.alloc (⟨0, true, some (.fin 1), 0, 0, []⟩ : Cell JF)).2
  exact ⟨{ graph := graph, root := 0, fuel := 1 }, .const (.fin 1), rfl⟩

end DynExpr.Expressions.SamplingTotality
