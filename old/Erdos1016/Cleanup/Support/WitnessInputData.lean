import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.WitnessInputData

open Erdos1016 CleanupSpecification

/-- Witness data before connecting the ambient graph. Hub extension supplies
connectivity while preserving these exact witness labels and cycle states. -/
structure WitnessData (G : PhysicalGraph) where
  R : ℕ
  r : ℕ
  witnessEdges : Finset G.Edge
  witnessVertices : Finset G.Vertex
  rank_large : 2 ^ (8 * R) ≤ r
  graph_rank : G.cycleRank = r
  witness_nonempty : witnessEdges.Nonempty
  witness_endpoints : ∀ e ∈ witnessEdges, G.src e ∈ witnessVertices ∧ G.dst e ∈ witnessVertices
  witness_vertices_exact : ∀ v, v ∈ witnessVertices ↔ ∃ e ∈ witnessEdges, G.src e = v ∨ G.dst e = v
  witness_edges_active : ∀ e ∈ witnessEdges, ActiveEdge G e
  vertices_le_edges : witnessVertices.card ≤ witnessEdges.card
  witness_edges_budget : witnessEdges.card + 1 ≤ 2 ^ (4 * R)
  witness_components : witnessComponentCount G witnessVertices witnessEdges < 5 * R
  outside_probability : (1 / 2 : ℝ) + 1 / (R : ℝ) < G.outsideLinearForestProbability witnessEdges



end Erdos1016.Proof.WitnessInputData

end
