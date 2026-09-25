import Erdos1016.Graph.Cubicization.IncidenceCycleWitness
import Erdos1016.Graph.Cubicization.IncidenceForestTransport
import Erdos1016.Graph.Suppression.MarkedCorridorForest

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The marked subcubic reduction

An actual union of cycle witnesses is expanded into marked incidence prefixes,
pruned to the full two-core, and suppressed along unmarked degree-two corridors.
The constructed multigraph retains the binary cycle rank. Its marked set has
twice the original witness edge count and no more connected components than
the original witness support. Each construction transports the actual forest
event in the direction needed for an upper bound.
-/

noncomputable section

namespace Erdos1016.ShortProof

open Nonbacktracking.FiniteTwoCore
local instance markedReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The full graph preprocessing construction, with no input certificate for
the auxiliary graph or its probability law. -/
theorem exists_marked_subcubic_reduction (G : PhysicalGraph) (hG : G.IsConnected)
    (F : Finset G.CycleWord) (hF : F.Nonempty) :
    ∃ (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex),
      Γ.toSimpleGraph.Connected ∧
      Γ.cycleRank = G.cycleRank ∧
      (∀ v, 2 ≤ Γ.degree v ∧ Γ.degree v ≤ 3) ∧
      (∀ v, v ∉ P → Γ.degree v = 3) ∧
      P.Nonempty ∧ P.card = 2 * (witnessSupportEdges G F).card ∧
      Nat.card (Γ.toSimpleGraph.induce (↑P : Set Γ.Vertex)).ConnectedComponent ≤
        Nat.card (cycleUnionGraph G F).ConnectedComponent ∧
      outsideForestProbability G (witnessSupportEdges G F) ≤
        Γ.regionForestProbability Pᶜ := by
  let W := witnessSupportEdges G F
  let A := IncidencePaths.physical G W
  let PA := IncidencePaths.markedVertices G W
  have hW : W.Nonempty := by
    obtain ⟨C, hC⟩ := hF
    have hex : ∃ e, C.1 e ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact C.2.1 (funext hn)
    obtain ⟨e, he⟩ := hex
    exact ⟨e, witnessSupport_edge_mem G F hC
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)⟩
  have hAconn : A.IsConnected := IncidencePaths.physical_connected G W hG
  have hAmax : ∀ v, A.degree v ≤ 3 := IncidencePaths.physical_degree_le_three G W
  have hPAcard : PA.card = 2 * W.card := IncidencePaths.markedVertices_card G W
  have hPAne : PA.Nonempty := Finset.card_pos.mp (by
    rw [hPAcard]
    exact Nat.mul_pos (by decide) hW.card_pos)
  have hPAmin : MinTwo A.toSimpleGraph PA := by
    intro v hv
    rw [← induce_degree_eq_degreeWithin A.toSimpleGraph PA v hv]
    exact IncidencePaths.cycleWitness_marked_min_degree_two G F ⟨v, hv⟩
  have hPAcomp : Nat.card (A.toSimpleGraph.induce (↑PA : Set A.Vertex)).ConnectedComponent ≤
      Nat.card (cycleUnionGraph G F).ConnectedComponent := by
    calc
      _ ≤ Nat.card (IncidencePaths.supportGraph G W).ConnectedComponent :=
        IncidencePaths.marked_physical_component_count_le G W
      _ = _ := Nat.card_congr (IncidencePaths.supportCycleUnionIso G F).connectedComponentEquiv
  let H := CycleCore.corePhysical A
  let PH := CycleCore.marks A PA
  have hHconn : H.IsConnected := CycleCore.physical_connected A hAconn
    (hPAne.mono (CycleCore.marked_subset_core A PA hPAmin))
  have hHmin : ∀ v, 2 ≤ H.degree v := maximalPhysicalCore_minDegree A
  have hHmax : ∀ v, H.degree v ≤ 3 := maximalPhysicalCore_degree_le_three A hAmax
  have hPHcard : PH.card = PA.card := CycleCore.marks_card A PA hPAmin
  have hPHne : PH.Nonempty := Finset.card_pos.mp (by rw [hPHcard]; exact hPAne.card_pos)
  have hHdegree : ∀ v, v ∉ PH → H.degree v = 2 ∨ H.degree v = 3 := by
    intro v _
    have hlo := hHmin v
    have hhi := hHmax v
    omega
  let Γ := MarkedCorridors.graph H PH hHconn hPHne hHdegree
  let P := MarkedCorridors.marks H PH hHconn hPHne hHdegree
  have hΓconn : Γ.toSimpleGraph.Connected :=
    MarkedCorridors.connected H PH hHconn hPHne hHdegree
  have hΓrank : Γ.cycleRank = G.cycleRank := by
    calc
      _ = H.cycleRank := MarkedCorridors.cycleRank_preserved H PH hHconn hPHne hHdegree
      _ = A.cycleRank := CycleCore.cycleRank_preserved A
      _ = G.cycleRank := IncidencePaths.physical_cycleRank G W
  have hPcard : P.card = 2 * W.card := by
    calc
      _ = PH.card := MarkedCorridors.marks_card H PH hHconn hPHne hHdegree
      _ = PA.card := hPHcard
      _ = _ := hPAcard
  refine ⟨Γ, P, hΓconn, hΓrank, ?_, ?_, ?_, hPcard, ?_, ?_⟩
  · intro v
    rw [MarkedCorridors.degree_preserved]
    exact ⟨hHmin _, hHmax _⟩
  · exact MarkedCorridors.degree_eq_three_outside_marks H PH hHconn hPHne hHdegree
  · exact Finset.card_pos.mp (by rw [hPcard]; exact Nat.mul_pos (by decide) hW.card_pos)
  · calc
      _ ≤ Nat.card (H.toSimpleGraph.induce (↑PH : Set H.Vertex)).ConnectedComponent :=
        MarkedCorridors.marked_component_count_le H PH hHconn hPHne hHdegree
      _ = Nat.card (A.toSimpleGraph.induce (↑PA : Set A.Vertex)).ConnectedComponent :=
        CycleCore.marked_component_count A PA hPAmin
      _ ≤ _ := hPAcomp
  · calc
      _ ≤ (CycleCore.asMultigraph A).regionForestProbability PAᶜ :=
        IncidencePaths.outsideForestProbability_le_region G W
      _ ≤ (CycleCore.asMultigraph H).regionForestProbability PHᶜ :=
        CycleCore.regionForestProbability_le_core A PA
      _ ≤ Γ.regionForestProbability Pᶜ :=
        MarkedCorridors.regionForestProbability_le_suppressed H PH hHconn hPHne hHdegree

end Erdos1016.ShortProof
