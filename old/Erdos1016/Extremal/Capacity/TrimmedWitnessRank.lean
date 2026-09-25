import Erdos1016.Cleanup.Support.VertexSupportedWitness

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.TrimmedWitnessRankBridge

open Erdos1016
open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.Proof.Capacity

/-- Euler accounting isolates the only missing fact in comparing the literal
witness support with its endpoint-trimmed version: trimming `d` isolated host
vertices must lower the component count by exactly `d`. -/
theorem trimmedWitness_cycleRank_eq_of_componentCount_adjustment
    (G : PhysicalGraph) (F : Finset G.CycleWord)
    (hcomponents :
      Fintype.card (witnessSupportGraph G F).traceNetwork.Component =
        Fintype.card (trimmedWitnessGraph G F).traceNetwork.Component +
          (G.vertexCount - (witnessSupportVertices G F).card)) :
    (trimmedWitnessGraph G F).cycleRank = (witnessSupportGraph G F).cycleRank := by
  have hW := PhysicalGraph.cycleRank_euler_components (witnessSupportGraph G F)
  have hT := PhysicalGraph.cycleRank_euler_components (trimmedWitnessGraph G F)
  have hV : (witnessSupportGraph G F).vertexCount = G.vertexCount := rfl
  have hVT : (trimmedWitnessGraph G F).vertexCount =
      (witnessSupportVertices G F).card := rfl
  have hE : (witnessSupportGraph G F).edgeCount =
      (trimmedWitnessGraph G F).edgeCount := by rfl
  have hcard : (witnessSupportVertices G F).card ≤ G.vertexCount := by
    simpa [PhysicalGraph.Vertex] using
      (Finset.card_le_univ (witnessSupportVertices G F))
  omega


end Erdos1016.Proof.TrimmedWitnessRankBridge
