import Erdos1016.Cleanup.Transport.PortSelectedDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortExpansionMarginal

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PortExpansion
open Erdos1016.Proof.PortExpansionCycleSpace
open Erdos1016.Proof.PortSelectedDegree


variable {G : PhysicalGraph} {I : CleanupInput G}











/-- The source cleanup probability is bounded by the forest probability of
its exact root-port expansion. The proof composes the output marginal's
uniform law with the root-port cycle-space isomorphism. -/
theorem probability_domination_rootPortExpansion (O : CleanupOutput I) :
    G.outsideLinearForestProbability I.witnessEdges ≤
      regionForestProbability (Physical O.Γ O.root O.root_structure)
        (oldVertexImage O.Γ O.root O.root_structure O.root) := by
  calc
    G.outsideLinearForestProbability I.witnessEdges ≤
        regionForestProbability O.Γ O.root := O.probability_domination
    _ = regionForestProbability (Physical O.Γ O.root O.root_structure)
        (oldVertexImage O.Γ O.root O.root_structure O.root) :=
      regionForestProbability_rootPort_eq O.Γ O.root O.root O.root_structure
        (Finset.Subset.refl _)

end Erdos1016.Proof.PortExpansionMarginal

end
