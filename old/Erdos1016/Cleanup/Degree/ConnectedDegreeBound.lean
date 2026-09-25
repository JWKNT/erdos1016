import Erdos1016.Cleanup.Degree.HighDegreeCardinality
import Erdos1016.CycleSpace.Graphical.ConnectedStarBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.HighActiveConnectedBridge

open Erdos1016
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalTripleStarBoundGraphConnected
open Erdos1016.Proof.BadVertexCardinalityBound



local notation "F₂" => ZMod 2



/-- The bad-vertex cardinality estimate also follows for connected graphs
without a separate triple-star hypothesis. -/
theorem badVertexSet_card_lt_520_mul_of_connected
    (G : PhysicalGraph) (E : Finset G.Edge) (R : ℕ)
    (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E)
    (hconn : G.IsConnected) :
    (badVertexSet G E).card < 520 * R := by
  apply BadVertexCardinalityBound.badVertexSet_card_lt_520_mul_of_tripleStarBound
    G E R hR hprob
  intro u v w huv huw hvw
  exact tripleStar_finrank_le_one_of_connected G u v w hconn huv huw hvw

end Erdos1016.Proof.HighActiveConnectedBridge
