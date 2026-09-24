import Erdos1016.Cleanup.Transport.ConnectedHubForest
import Erdos1016.Cleanup.Support.WitnessInputData

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Erdos1016.Proof.ConnectedHubInput

open Erdos1016 PhysicalGraph CleanupSpecification WitnessInputData
open ConnectedHubForest

variable (G : PhysicalGraph)

abbrev vertices (V : Finset G.Vertex) : Finset (connectByHub G).Vertex := V.image (vertex G)

theorem witness_adj_iff (V : Finset G.Vertex) (E : Finset G.Edge) (u v : G.Vertex) :
    (witnessGraph (connectByHub G) (vertices G V) (witness G E)).Adj (vertex G u) (vertex G v) ↔
      (witnessGraph G V E).Adj u v := by
  classical
  constructor
  · rintro ⟨hu, hv, hne, e, he, hor⟩
    obtain ⟨u', hu', huu⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', hvv⟩ := Finset.mem_image.mp hv
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    refine ⟨vertex_injective G huu ▸ hu', vertex_injective G hvv ▸ hv',
      fun h => hne (congrArg (vertex G) h), f, hf, ?_⟩
    rw [src_edge, dst_edge] at hor
    exact hor.elim (fun h => Or.inl ⟨vertex_injective G h.1, vertex_injective G h.2⟩)
      (fun h => Or.inr ⟨vertex_injective G h.1, vertex_injective G h.2⟩)
  · rintro ⟨hu, hv, hne, e, he, hor⟩
    refine ⟨Finset.mem_image.mpr ⟨u, hu, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
      fun h => hne (vertex_injective G h), edge G e, Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    rw [src_edge, dst_edge]
    exact hor.elim (fun h => Or.inl ⟨congrArg (vertex G) h.1, congrArg (vertex G) h.2⟩)
      (fun h => Or.inr ⟨congrArg (vertex G) h.1, congrArg (vertex G) h.2⟩)

def witnessGraphIso (V : Finset G.Vertex) (E : Finset G.Edge) :
    (witnessGraph G V E).induce (↑V : Set G.Vertex) ≃g
      (witnessGraph (connectByHub G) (vertices G V) (witness G E)).induce
        (↑(vertices G V) : Set (connectByHub G).Vertex) where
  toEquiv := Equiv.ofBijective
    (fun v => ⟨vertex G v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩)
    ⟨fun _ _ h => Subtype.ext (vertex_injective G (congrArg Subtype.val h)), by
      intro v
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp v.2
      exact ⟨⟨u, hu⟩, Subtype.ext huv⟩⟩
  map_rel_iff' := by
    intro u v
    exact witness_adj_iff G V E u.1 v.1

theorem witness_components_eq (V : Finset G.Vertex) (E : Finset G.Edge) :
    witnessComponentCount (connectByHub G) (vertices G V) (witness G E) =
      witnessComponentCount G V E := by
  classical
  exact (Fintype.card_congr (witnessGraphIso G V E).connectedComponentEquiv).symm

/-- Connect a possibly disconnected witness input without changing its rank,
scale, probability, or witness component count. -/
def input (D : WitnessData G) : CleanupInput (connectByHub G) where
  R := D.R
  r := D.r
  witnessEdges := witness G D.witnessEdges
  witnessVertices := vertices G D.witnessVertices
  rank_large := D.rank_large
  graph_rank := (cycleRank_connectByHub G).trans D.graph_rank
  graph_connected := connectByHub_connected G
  witness_nonempty := D.witness_nonempty.image (edge G)
  witness_endpoints := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    rw [src_edge, dst_edge]
    exact ⟨Finset.mem_image.mpr ⟨G.src f, (D.witness_endpoints f hf).1, rfl⟩,
      Finset.mem_image.mpr ⟨G.dst f, (D.witness_endpoints f hf).2, rfl⟩⟩
  witness_vertices_exact := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨f, hf, hs | ht⟩ := (D.witness_vertices_exact u).mp hu
      · exact ⟨edge G f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, Or.inl ((src_edge G f).trans (congrArg (vertex G) hs))⟩
      · exact ⟨edge G f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, Or.inr ((dst_edge G f).trans (congrArg (vertex G) ht))⟩
    · rintro ⟨e, he, hor⟩
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
      rcases hor with hs | ht
      · exact Finset.mem_image.mpr ⟨G.src f, (D.witness_endpoints f hf).1, (src_edge G f).symm.trans hs⟩
      · exact Finset.mem_image.mpr ⟨G.dst f, (D.witness_endpoints f hf).2, (dst_edge G f).symm.trans ht⟩
  witness_edges_active := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨x, hx⟩ := D.witness_edges_active f hf
    exact ⟨hubCycleSpaceEquiv G x, by simpa only [cycle_coordinate_old] using hx⟩
  vertices_le_edges := by
    simpa only [vertices, witness, Finset.card_image_of_injective _ (vertex_injective G),
      Finset.card_image_of_injective _ (edge_injective G)] using D.vertices_le_edges
  witness_edges_budget := by
    simpa only [witness, Finset.card_image_of_injective _ (edge_injective G)] using D.witness_edges_budget
  witness_components := by
    rw [witness_components_eq]
    exact D.witness_components
  outside_probability := by
    rw [← outside_probability_eq]
    exact D.outside_probability

end Erdos1016.Proof.ConnectedHubInput

end
