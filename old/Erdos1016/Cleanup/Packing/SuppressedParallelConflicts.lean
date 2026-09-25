import Erdos1016.Cleanup.Packing.GreedyConflictExtraction

set_option autoImplicit false

/-!
# Conflict control for cubic suppressed parallel-pair regions

In a series-suppressed multigraph, a double edge uses two incidences at each
endpoint.  If distinct double-edge pairs use disjoint labelled edges, cubic
incidence capacity forces their endpoint regions to be disjoint.  A later
route-expansion step must additionally preserve disjointness of corridor
interiors; this file isolates the compressed-graph incidence argument.
-/

noncomputable section

namespace Erdos1016.Proof.SuppressedParallelConflicts

open Erdos1016
open Erdos1016.Proof.GreedyConflictExtraction

variable {ι V E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V] [Fintype E]

/-- Labels incident to a vertex in a finite endpoint-labelled graph. -/
def incidentLabels (src dst : E → V) (v : V) : Finset E :=
  Finset.univ.filter fun e => src e = v ∨ dst e = v

/-- Two edge labels whose endpoints are the two vertices of a pair region. -/
structure SuppressedParallelPair (src dst : E → V) where
  endpointLeft : V
  endpointRight : V
  endpoints_ne : endpointLeft ≠ endpointRight
  edges : Finset E
  edges_card : edges.card = 2
  edges_incident_left : edges ⊆ incidentLabels src dst endpointLeft
  edges_incident_right : edges ⊆ incidentLabels src dst endpointRight

def pairEndpointRegion (src dst : E → V)
    (P : SuppressedParallelPair src dst) : Finset V :=
  {P.endpointLeft, P.endpointRight}





end Erdos1016.Proof.SuppressedParallelConflicts

end
