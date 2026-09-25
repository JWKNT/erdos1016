import Erdos1016.Cleanup.Root.ProtectedDeletionRankLedger
import Erdos1016.Cleanup.Root.ComponentVertexEdgeSums

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActiveComponentSurvival

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.ProtectedDeletionRankLedger
open Erdos1016.Proof.ComponentVertexEdgeSums

/-- A protected vertex deletion cannot exhaust the rank of a connected
auxiliary graph when fewer edge labels are incident to the protected set
than the graph's cycle rank. This is the rank-survival form needed before
selecting a positive-rank component of the complement. -/
theorem exists_positive_rank_outsideComponent_of_strict_rank_budget
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hbudget : (protectedIncidentEdges Γ P).card < Γ.cycleRank) :
    ∃ c : OutsideComponent Γ P, 0 < outsideComponentRank Γ P c := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hcomponent : ∀ c : OutsideComponent Γ P,
      (componentInternalGraph Γ P c).toSimpleGraph.Connected := by
    intro c
    exact componentInternalGraph_connected Γ P c
  have hvertices := outsideComponentVertices_card_sum Γ P
  have hedges :
      (∑ c : OutsideComponent Γ P,
        (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
          (unprotectedEdges Γ P).card := by
    rw [outsideComponent_internalEdges_card_sum]
    congr 1
    ext e
    simp [unprotectedEdges, internalEdges, Finset.mem_compl]
  have hsumLower := outside_rank_sum_lower_of_partition
    hcomponent hconn hP hvertices hedges
  have hsumPos :
      0 < ∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c := by
    by_contra hnot
    have hzero :
        (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have hle := hsumLower
    rw [hzero] at hle
    omega
  by_contra hnone
  have hzero :
      (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) = 0 :=
    Finset.sum_eq_zero (fun c _ => Nat.eq_zero_of_not_pos (fun hc => hnone ⟨c, hc⟩))
  rw [hzero] at hsumPos
  omega



/-- The number of edge coordinates incident to a protected region is at
most the sum of the ambient degrees on that region. Internal edges contribute
two incidences and crossing edges one. -/
theorem protectedIncidentEdges_card_le_degree_sum
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (protectedIncidentEdges Γ P).card ≤ ∑ v ∈ P, ambientDegree Γ v := by
  classical
  let I := internalEdges Γ P
  let C := cutEdges Γ P
  have hdisj : Disjoint I C := by
    apply Finset.disjoint_left.mpr
    intro e heI heC
    simp [I, C, internalEdges, cutEdges, Finset.mem_filter] at heI heC
    tauto
  have hunion : I ∪ C = protectedIncidentEdges Γ P := by
    ext e
    simp [I, C, internalEdges, cutEdges, protectedIncidentEdges,
      Finset.mem_filter]
    tauto
  have hcard : (protectedIncidentEdges Γ P).card = I.card + C.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  rw [hcard]
  calc
    I.card + C.card ≤ 2 * I.card + C.card := by omega
    _ = ∑ v ∈ P, ambientDegree Γ v := by
      simpa [I, C] using (ambientDegree_sum_region Γ P).symm



end Erdos1016.Proof.ActiveComponentSurvival

end
