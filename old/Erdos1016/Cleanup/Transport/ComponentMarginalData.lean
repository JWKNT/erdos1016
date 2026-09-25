import Erdos1016.Cleanup.Transport.SelectedComponentRoutes
import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

/-!
# Marginal/lift transfer for a selected active component

This scratch module packages the cycle-space fields needed by cleanup from
one component's finite series route decomposition. Corridor geometry and the
remaining root/event estimates are separate obligations.
-/

noncomputable section

namespace Erdos1016.Proof.ComponentMarginalData

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016.Proof.SelectedComponentRoutes

local notation "F₂" => ZMod 2

/-- The original edge coordinate corresponding to an edge of the chosen
active component's restricted physical graph. -/
def selectedComponentOriginalEdge (G : PhysicalGraph)
    (c : ActiveComponent G) (p : (selectedComponentRouteGraph G c).Edge) : G.Edge :=
  (G.restrictedEdgeEquiv (activeEdges G)
    (((activeSubgraph G).restrictedEdgeEquiv (componentEdges G c) p).1)).1

/-- Component projection preserves the physical coordinate attached to each
restricted edge label. -/
theorem projectToSelectedComponent_coordinate (G : PhysicalGraph)
    (c : ActiveComponent G) (x : G.CycleSpace)
    (p : (selectedComponentRouteGraph G c).Edge) :
    (selectedComponentToMultiGraphEquiv G c
      (projectToSelectedComponent G c x)).1 p =
      x.1 (selectedComponentOriginalEdge G c p) := by
  change (activeCycleSpaceProductEquiv G
      (cycleSpaceActiveSubgraphEquiv G x) c).1 p = _
  rw [activeCycleSpaceProductEquiv_apply_coordinate]
  simp [selectedComponentOriginalEdge, cycleSpaceActiveSubgraphEquiv,
    activeCycleSpaceRestriction, activeSubgraph, restrictWordLinear,
    PhysicalGraph.restrictPhysicalWordEquiv, PhysicalGraph.restrictWord,
    PhysicalGraph.restrictedEdgeEquiv, edgeSigmaEquiv]





end Erdos1016.Proof.ComponentMarginalData

end
