import Erdos1016.Cleanup.Paths.DegreeTwoCorridorRoutes
import Erdos1016.Cleanup.Compression.AssembledCorridorCompression
import Erdos1016.Graph.PathExpansion.InjectiveCycleEquivalence
import Erdos1016.Cleanup.CleanupSpecification
import Erdos1016.CycleSpace.EvenForestZero

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CorridorRouteEquivalence

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute


open Erdos1016.Proof.CleanupSpecification

local notation "F₂" => ZMod 2

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}





/-- The physical and route-graph cycle spaces use the same edge coordinates;
this equivalence only changes the graph wrapper. -/
noncomputable def physicalCycleRouteEquiv (G : PhysicalGraph) :
    G.CycleSpace ≃ₗ[F₂] (SingleCorridorRoute.routeGraph G).CycleSpace := by
  classical
  have hto (x : G.CycleSpace) : x.1 ∈
      (SingleCorridorRoute.routeGraph G).CycleSpace := by
    change G.boundary x.1 = 0
    exact x.2
  have hfrom (x : (SingleCorridorRoute.routeGraph G).CycleSpace) :
      x.1 ∈ G.CycleSpace := by
    change G.boundary x.1 = 0
    exact x.2
  refine
    { toFun := fun x => ⟨x.1, hto x⟩
      invFun := fun x => ⟨x.1, hfrom x⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; apply Subtype.ext; rfl
      map_smul' := by intro a x; apply Subtype.ext; rfl }





end Erdos1016.Proof.CorridorRouteEquivalence

end
