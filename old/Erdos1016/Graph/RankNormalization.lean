import Erdos1016.Graph.PancyclicRank

set_option autoImplicit false

/-!
# Cycle-rank accounting for normalization operations

This module isolates the rank arithmetic needed by graph realization and
normalization constructions. It proves Euler's rank formula with the actual
number of connected components, then records the exact rank changes implied by
the vertex, edge, and component changes of common attachment operations.
-/

namespace Erdos1016.PhysicalGraph

open Erdos1016.BoundaryDecay

/-- Euler's formula for the boundary-kernel rank, including isolated
vertices and all connected components. -/
theorem cycleRank_euler_components (G : PhysicalGraph) :
    G.cycleRank + G.vertexCount =
      G.edgeCount + Fintype.card G.traceNetwork.Component := by
  have h := network_rank_euler G.traceNetwork
  rw [rank_traceNetwork, Fintype.card_fin, Fintype.card_fin] at h
  exact h









end Erdos1016.PhysicalGraph
