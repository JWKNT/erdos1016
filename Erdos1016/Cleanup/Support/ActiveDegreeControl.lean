import Erdos1016.Cleanup.Degree.ConnectedDegreeBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActiveDegreeControl

open Erdos1016
open Erdos1016.Proof.ActiveDegreeExtraction
open Erdos1016.Proof.BadVertexCardinalityBound

/-- The first two local conclusions in the Section 10 cleanup: high outside
forest probability bounds every active outside star by `R + 1`, and bounds
the number of vertices with four or more such incidences linearly in `R`.
The second statement uses connectedness to discharge the triple-star rank
condition in the selected-triple estimate. -/
theorem active_degree_and_bad_vertex_bounds
    (G : PhysicalGraph) (E : Finset G.Edge) (R : ℕ)
    (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E)
    (hconn : G.IsConnected) :
    (∀ v : G.Vertex,
        (activeOutsideIncidentEdges G E v).card ≤ R + 1) ∧
      (badVertexSet G E).card < 520 * R := by
  constructor
  · intro v
    exact activeOutsideIncidentEdges_card_le G E v R (by omega) hprob
  · exact Erdos1016.Proof.HighActiveConnectedBridge.badVertexSet_card_lt_520_mul_of_connected
      G E R hR hprob hconn

end Erdos1016.Proof.ActiveDegreeControl

end
