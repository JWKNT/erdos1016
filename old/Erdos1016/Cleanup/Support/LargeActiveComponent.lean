import Erdos1016.Extremal.Capacity.ComponentRankExtraction
import Erdos1016.Extremal.Capacity.TrimmedWitnessNetwork

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.LargeActiveComponent

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.Capacity
open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.Proof.ActivePhysicalComponents

/-- The canonical witness support has fewer than `5R` endpoint-trimmed
components. The rank screen is transported across the verified trimming
isomorphism, and the minimum degree-two property gives vertices ≤ edges. -/
theorem canonical_trimmed_component_screen
    (G : PhysicalGraph) (R : ℕ) (hR : 6 ≤ R)
    (hr : 5 * R + 2 ≤ G.cycleRank)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1))
    (hcycleCount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank) :
    Fintype.card
      (trimmedWitnessGraph G
        (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).traceNetwork.Component <
      5 * R := by
  let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
  let H := trimmedWitnessGraph G F
  apply WitnessComponentScreen.canonical_trimmed_component_screen
    G H R hR hr hcov hcycleCount
  · exact TrimmedWitnessNetworkIso.trimmedWitness_cycleRank_eq G F
  · exact trimmed_vertexCount_le_edgeCount G F



end Erdos1016.Proof.LargeActiveComponent

end
