import Erdos1016.Graph.CutPacking
import Erdos1016.Probability.Cylinders.ZeroCoordinateCylinders
import Erdos1016.Probability.Cylinders.GraphicalThreshold

set_option autoImplicit false

/-!
# Cycle parity across a physical cut

The edge coordinates of a cycle cross every vertex shore an even number of
times. In particular, a cut of at most two edges contributes at most one
independent zero-coordinate constraint. This sharpens the general cut-size
cylinder estimate for two-edge regions.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.ActualCutCycleCylinder

open Erdos1016
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.GraphicalThreshold
open Erdos1016.Proof.ManyCyclicRegionCutCylinders

local notation "𝔽" => ZMod 2









/-- The event that every physical edge crossing `U` has zero coordinate. -/
def cutCoordinatesZero (G : PhysicalGraph) (U : Finset G.Vertex)
    (x : G.CycleSpace) : Prop :=
  ∀ e ∈ G.cutEdges U, x.1 e = 0





end Erdos1016.Proof.ActualCutCycleCylinder

end
