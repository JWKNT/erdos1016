import Erdos1016.CycleSpace.EmbeddedForestMarginals
import Erdos1016.Cleanup.Support.ComponentWitnessCorridorGeometry

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.SupportForestMarginal

open Erdos1016
open ActivePhysicalComponents
open CleanupSpecification SelectedComponentRoutes
open RestrictedComponentGraph
open SupportCycleSpaceEquivalence
open ComponentCorridorReindexing
open ComponentWitnessCorridorGeometry
open ComponentMarginalData

/-- The actual projection onto a component's support graph; its section
inserts the component cycle and assigns zero to all other active components. -/
def marginal (G : PhysicalGraph) (c : ActiveComponent G) :
    G.CycleSpace →ₗ[ZMod 2] (componentSupportPhysical G c).CycleSpace :=
  (componentSupportCycleSpaceEquiv G c).symm.toLinearMap.comp
    (projectToSelectedComponent G c)

theorem marginal_surjective (G : PhysicalGraph) (c : ActiveComponent G) :
    Function.Surjective (marginal G c) := by
  intro y
  refine ⟨includeSelectedComponent G c (componentSupportCycleSpaceEquiv G c y), ?_⟩
  simp [marginal, project_include_selected_component]

theorem marginal_coordinate (G : PhysicalGraph) (c : ActiveComponent G)
    (x : G.CycleSpace) (e : (componentSupportPhysical G c).Edge) :
    (marginal G c x).1 e =
      x.1 (componentCorridorEdgeToOriginal G c (componentSupportEdgeEquiv G c e)) := by
  exact projectToSelectedComponent_coordinate G c x (componentSupportEdgeEquiv G c e)

/-- Restricting to the selected support component raises the outside-forest
probability. In particular it preserves the full `1/2+1/R` cutoff. -/
theorem outside_probability_le (G : PhysicalGraph) (I : CleanupInput G)
    (c : ActiveComponent G) :
    G.outsideLinearForestProbability I.witnessEdges ≤
      (componentSupportPhysical G c).outsideLinearForestProbability
        (componentLocalWitnessPullback G c I) := by
  classical
  apply PhysicalEmbeddingForestProbability.outside_probability_le_of_surjective_marginal
    (componentSupportPhysical G c) G (componentSupportVertexMap G c)
    (fun e => componentCorridorEdgeToOriginal G c (componentSupportEdgeEquiv G c e))
    (componentSupportVertexMap_injective G c)
    ((componentCorridorEdgeToOriginal_injective G c).comp
      (componentSupportEdgeEquiv G c).injective)
    (fun e => (src_componentCorridorEdgeToOriginal G c _).trans
      (componentSupportEdgeEquiv_src G c e))
    (fun e => (dst_componentCorridorEdgeToOriginal G c _).trans
      (componentSupportEdgeEquiv_dst G c e))
    I.witnessEdges (componentLocalWitnessPullback G c I)
    (fun e => by simp [componentLocalWitnessPullback])
    (marginal G c) (marginal_surjective G c) (marginal_coordinate G c)

theorem outside_probability_gt_cutoff (G : PhysicalGraph) (I : CleanupInput G)
    (c : ActiveComponent G) :
    (1 / 2 : ℝ) + 1 / (I.R : ℝ) <
      (componentSupportPhysical G c).outsideLinearForestProbability
        (componentLocalWitnessPullback G c I) :=
  I.outside_probability.trans_le (outside_probability_le G I c)

end Erdos1016.Proof.SupportForestMarginal

end
