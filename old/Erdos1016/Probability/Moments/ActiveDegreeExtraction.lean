import Erdos1016.Probability.Moments.SelectedDegree

set_option autoImplicit false

/-!
# Active outside degree under the forest-probability assumption

This specializes the finite mean bound to all active edges in the outside
star of one vertex. It formalizes the first local reduction in the Section 10
cleanup argument without assuming independence between edge coordinates.
-/

namespace Erdos1016.Proof.ActiveDegreeExtraction

open Erdos1016
open Erdos1016.PhysicalGraph
open Erdos1016.Proof.ActiveEdgeUniform
open Erdos1016.Proof.ActiveDegreeMoment

/-- Active edges outside the witness support and incident to one vertex. -/
noncomputable def activeOutsideIncidentEdges (G : PhysicalGraph) (E : Finset G.Edge)
    (v : G.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => ActiveEdge G e ∧ e ∉ E ∧ G.incident e v

/-- If the outside linear-forest event has probability above `1/2+1/R`,
then each vertex has at most `R+1` active outside incident edges. -/
theorem activeOutsideIncidentEdges_card_le
    (G : PhysicalGraph) (E : Finset G.Edge) (v : G.Vertex) (R : ℕ)
    (hR : 0 < R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability E) :
    (activeOutsideIncidentEdges G E v).card ≤ R + 1 := by
  classical
  let F := activeOutsideIncidentEdges G E v
  have hactive : ∀ e ∈ F, ActiveEdge G e := by
    intro e he
    exact (Finset.mem_filter.mp he).2.1
  have hsmall : ∀ x ∈ G.outsideLinearForestStates E,
      selectedFamilyCount G F x ≤ 2 := by
    intro x hx
    have hforest : G.IsRestrictedLinearForest Eᶜ
        (G.restrictWord Eᶜ x.1) := (Finset.mem_filter.mp hx).2
    have hfamily := selectedFamilyCount_le_restrictedDegree G E F v x (by
      intro e he
      rcases (Finset.mem_filter.mp he).2 with ⟨_, hnot, hinc⟩
      exact ⟨Finset.mem_compl.mpr hnot, hinc⟩)
    have hdegree :
        (G.restrictedSelectedDegree Eᶜ (G.restrictWord Eᶜ x.1) v : ℝ) ≤ 2 := by
      exact_mod_cast hforest.2 v
    exact hfamily.trans hdegree
  exact activeFamily_card_le_of_outsideForest_probability_gt
    G E F R hR hactive hsmall hprob

end Erdos1016.Proof.ActiveDegreeExtraction
