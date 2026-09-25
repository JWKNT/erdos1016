import Erdos1016.Extremal.Capacity.RankScreenArithmetic
import Erdos1016.Graph.RankNormalization

set_option autoImplicit false

/-!
# Section 10 vertex-supported witness screen

The canonical screen currently applies to `witnessSupportGraph`, which keeps
all host vertices. The source's support graph should instead retain only
vertices incident to selected witness edges. This file isolates the exact
Euler/count consequence needed after that trimming operation, without
identifying the two graphs or asserting an unproved rank-preservation fact.
-/

noncomputable section

namespace Erdos1016.Proof.WitnessComponentScreen

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.Capacity
open Erdos1016.Proof.CapacityCalibrationShortcut
open Erdos1016.Proof.WitnessRankScreenArithmetic

/-- Euler's formula turns the canonical `< 5R` rank screen into a component
bound as soon as the trimmed graph has no isolated vertices (`V ≤ E`). -/
theorem componentCount_lt_fiveR_of_screen
    (H : PhysicalGraph) (R : ℕ)
    (hrank : H.cycleRank < 5 * R)
    (hvertex_edge : H.vertexCount ≤ H.edgeCount) :
    Fintype.card H.traceNetwork.Component < 5 * R := by
  have heuler := H.cycleRank_euler_components
  omega

/-- The exact local Section 10 reduction for a proposed trimmed support graph.
The remaining graph-construction obligations are explicit: preserve the
canonical witness rank under vertex trimming and prove `V ≤ E`. -/
theorem canonical_trimmed_component_screen
    (G H : PhysicalGraph) (R : ℕ)
    (hR : 6 ≤ R)
    (hr : 5 * R + 2 ≤ G.cycleRank)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1))
    (hcycleCount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank)
    (hrankTrim : H.cycleRank =
      (witnessSupportGraph G
        (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov)).cycleRank)
    (hvertex_edge : H.vertexCount ≤ H.edgeCount) :
    Fintype.card H.traceNetwork.Component < 5 * R := by
  have hscreen := canonicalWitness_rank_screen G R hR hr hcov hcycleCount
  apply componentCount_lt_fiveR_of_screen H R
  · rw [hrankTrim]
    exact hscreen.2
  · exact hvertex_edge

end Erdos1016.Proof.WitnessComponentScreen
