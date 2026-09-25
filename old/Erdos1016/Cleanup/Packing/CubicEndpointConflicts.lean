import Erdos1016.Cleanup.Packing.SuppressedParallelConflicts

set_option autoImplicit false

/-!
# Bounded conflict packing for unordered parallel pairs

The endpoint regions need not be globally disjoint: several distinct pairs
may come from one triple edge bundle.  If the pair index is deduplicated and
intersecting endpoint regions have the same endpoint set, cubic incidence
gives at most three possible two-label supports at a fixed endpoint.  Greedy
packing therefore keeps at least one third of the candidates.
-/

noncomputable section

namespace Erdos1016.Proof.CubicEndpointConflicts

open Erdos1016.Proof.GreedyConflictExtraction
open Erdos1016.Proof.SuppressedParallelConflicts

variable {ι V E : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [Fintype E] [DecidableEq E]

local instance : DecidableEq V := Classical.decEq V

private theorem pair_edge_connects (src dst : E → V)
    (P : SuppressedParallelPair src dst) {e : E} (he : e ∈ P.edges) :
    (src e = P.endpointLeft ∧ dst e = P.endpointRight) ∨
      (src e = P.endpointRight ∧ dst e = P.endpointLeft) := by
  have hl : src e = P.endpointLeft ∨ dst e = P.endpointLeft := by
    simpa [incidentLabels] using P.edges_incident_left he
  have hr : src e = P.endpointRight ∨ dst e = P.endpointRight := by
    simpa [incidentLabels] using P.edges_incident_right he
  rcases hl with hsl | hdl <;> rcases hr with hsr | hdr
  · exact (P.endpoints_ne (hsl.symm.trans hsr)).elim
  · exact Or.inl ⟨hsl, hdr⟩
  · exact Or.inr ⟨hsr, hdl⟩
  · exact (P.endpoints_ne (hdl.symm.trans hdr)).elim

/-- In a cubic endpoint-labelled multigraph, two unordered pairs of parallel
labels that share an endpoint must have the same two endpoints. -/
theorem pairEndpointRegion_intersection_eq_of_cubic_local
    (src dst : E → V) (P Q : SuppressedParallelPair src dst)
    (hdegree : ∀ v ∈ pairEndpointRegion src dst P,
      (incidentLabels src dst v).card ≤ 3)
    (hoverlap : ¬ Disjoint (pairEndpointRegion src dst P)
      (pairEndpointRegion src dst Q)) :
    pairEndpointRegion src dst P = pairEndpointRegion src dst Q := by
  classical
  obtain ⟨v, hvP, hvQ⟩ := Finset.not_disjoint_iff.mp hoverlap
  have hvP' : v = P.endpointLeft ∨ v = P.endpointRight := by
    simpa [pairEndpointRegion] using hvP
  have hvQ' : v = Q.endpointLeft ∨ v = Q.endpointRight := by
    simpa [pairEndpointRegion] using hvQ
  let x := if v = P.endpointLeft then P.endpointRight else P.endpointLeft
  let y := if v = Q.endpointLeft then Q.endpointRight else Q.endpointLeft
  have hPset : pairEndpointRegion src dst P = {v, x} := by
    rcases hvP' with h | h
    · ext z
      simp [pairEndpointRegion, x, h]
    · have h' : v ≠ P.endpointLeft := by
        intro heq
        exact P.endpoints_ne (heq.symm.trans h)
      ext z
      simp [pairEndpointRegion, x, h, h', P.endpoints_ne, P.endpoints_ne.symm]
      <;> tauto
  have hQset : pairEndpointRegion src dst Q = {v, y} := by
    rcases hvQ' with h | h
    · ext z
      simp [pairEndpointRegion, y, h]
    · have h' : v ≠ Q.endpointLeft := by
        intro heq
        exact Q.endpoints_ne (heq.symm.trans h)
      ext z
      simp [pairEndpointRegion, y, h, h', Q.endpoints_ne, Q.endpoints_ne.symm]
      <;> tauto
  have hvx : x ≠ v := by
    dsimp [x]
    split
    · intro heq
      exact P.endpoints_ne.symm (heq.trans ‹v = P.endpointLeft›)
    · intro heq
      exact ‹v ≠ P.endpointLeft› heq.symm
  have hvy : y ≠ v := by
    dsimp [y]
    split
    · intro heq
      exact Q.endpoints_ne.symm (heq.trans ‹v = Q.endpointLeft›)
    · intro heq
      exact ‹v ≠ Q.endpointLeft› heq.symm
  by_cases hxy : x = y
  · rw [hPset, hQset, hxy]
  · have hEi : P.edges ⊆ incidentLabels src dst v := by
      rcases hvP' with h | h
      · simpa [h] using P.edges_incident_left
      · simpa [h] using P.edges_incident_right
    have hEj : Q.edges ⊆ incidentLabels src dst v := by
      rcases hvQ' with h | h
      · simpa [h] using Q.edges_incident_left
      · simpa [h] using Q.edges_incident_right
    have hedgesDisjoint : Disjoint P.edges Q.edges := by
      apply Finset.disjoint_left.mpr
      intro e heP heQ
      have hconnP := pair_edge_connects src dst P heP
      have hconnQ := pair_edge_connects src dst Q heQ
      rcases hvP' with h | h <;> rcases hvQ' with k | k
      · simp [x, y, h, k] at hxy
        rcases hconnP with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
          rcases hconnQ with ⟨hs', ht'⟩ | ⟨hs', ht'⟩ <;> simp_all
      · simp [x, y, h, k] at hxy
        rcases hconnP with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
          rcases hconnQ with ⟨hs', ht'⟩ | ⟨hs', ht'⟩ <;> simp_all
      · simp [x, y, h, k] at hxy
        rcases hconnP with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
          rcases hconnQ with ⟨hs', ht'⟩ | ⟨hs', ht'⟩ <;> simp_all
      · simp [x, y, h, k] at hxy
        rcases hconnP with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
          rcases hconnQ with ⟨hs', ht'⟩ | ⟨hs', ht'⟩ <;> simp_all
    have hUnion : P.edges ∪ Q.edges ⊆ incidentLabels src dst v :=
      Finset.union_subset hEi hEj
    have hcard : (P.edges ∪ Q.edges).card = 4 := by
      rw [Finset.card_union_of_disjoint hedgesDisjoint, P.edges_card, Q.edges_card]
    have hle := Finset.card_le_card hUnion
    rw [hcard] at hle
    have := hdegree v hvP
    omega

/-- Under cubic incidence and a unique index for each edge support, endpoint
conflicts have bounded closed degree.  `hstable` is the route/endpoint
geometry input: any two candidate endpoint regions that meet have the same
two endpoints.  The canonical corridor partition should discharge this for
its compressed parallel-pair family. -/
theorem endpoint_closed_conflicts_card_le_three_local
    (src dst : E → V) (U : ι → Finset V)
    (P : ι → SuppressedParallelPair src dst)
    (hU : ∀ i, U i = pairEndpointRegion src dst (P i))
    (hdegree : ∀ i v, v ∈ pairEndpointRegion src dst (P i) →
      (incidentLabels src dst v).card ≤ 3)
    (hinj : Function.Injective (fun i => (P i).edges))
    (i : ι) :
    (closedConflicts U Finset.univ i).card ≤ 3 := by
  classical
  let v := (P i).endpointLeft
  let S := closedConflicts U Finset.univ i
  have hstable : ∀ j, ¬ Disjoint (U i) (U j) → U i = U j := by
    intro j hoverlap
    have hoverlap' : ¬ Disjoint (pairEndpointRegion src dst (P i))
        (pairEndpointRegion src dst (P j)) := by
      simpa [hU i, hU j] using hoverlap
    have heq := pairEndpointRegion_intersection_eq_of_cubic_local src dst (P i) (P j)
      (hdegree i) hoverlap'
    simpa [hU i, hU j] using heq
  have hsub : ∀ j ∈ S,
      (P j).edges ∈ Finset.powersetCard 2 (incidentLabels src dst v) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have heq : U i = U j := by
      rcases hj' with hEq | hnd
      · exact (congrArg U hEq).symm
      · exact hstable j hnd
    have hv : v ∈ U j := by
      have hvi : v ∈ U i := by simp [v, hU i, pairEndpointRegion]
      simpa [heq] using hvi
    rw [hU j] at hv
    have hv' : v = (P j).endpointLeft ∨ v = (P j).endpointRight := by
      simpa [pairEndpointRegion] using hv
    have hedge : (P j).edges ⊆ incidentLabels src dst v := by
      rcases hv' with h | h
      · simpa [v, h] using (P j).edges_incident_left
      · simpa [v, h] using (P j).edges_incident_right
    exact Finset.mem_powersetCard.mpr ⟨hedge, (P j).edges_card⟩
  have hcardS : S.card ≤ (Finset.powersetCard 2 (incidentLabels src dst v)).card := by
    apply Finset.card_le_card_of_injOn (fun j => (P j).edges)
    · intro j hj
      exact hsub j hj
    · intro j hj k hk hEq
      exact hinj hEq
  have hpowerset : (Finset.powersetCard 2 (incidentLabels src dst v)).card ≤ 3 := by
    rw [Finset.card_powersetCard]
    have hle : (incidentLabels src dst v).card ≤ 3 := hdegree i v (by simp [v, pairEndpointRegion])
    have hchoose : (incidentLabels src dst v).card.choose 2 ≤ 3 := by
      interval_cases n : (incidentLabels src dst v).card <;> norm_num [n] at hle ⊢
    exact hchoose
  change S.card ≤ 3
  exact hcardS.trans hpowerset



/-- Physical route regions may live in a different vertex type from the
compressed endpoint graph.  If route intersection forces endpoint-region
intersection, and cubic incidence plus support injectivity bounds endpoint
conflicts as above, greedy extraction applies directly to the physical
regions.  The bridge premise is exactly the geometric input to check against
the canonical corridor partition. -/
theorem exists_disjoint_physical_route_subfamily_local
    {W : Type*} [Fintype W]
    (src dst : E → V) (R : ι → Finset W)
    (P : ι → SuppressedParallelPair src dst)
    (hdegree : ∀ i v, v ∈ pairEndpointRegion src dst (P i) →
      (incidentLabels src dst v).card ≤ 3)
    (hinj : Function.Injective (fun i => (P i).edges))
    (hrouteBridge : ∀ i j, ¬ Disjoint (R i) (R j) →
      ¬ Disjoint (pairEndpointRegion src dst (P i))
        (pairEndpointRegion src dst (P j)))
    (threshold : ℕ)
    (hsize : 3 * threshold ≤ Fintype.card ι) :
    ∃ T : Finset ι, T ⊆ Finset.univ ∧ PairwiseDisjointOn R T ∧
      threshold ≤ T.card := by
  classical
  have hconflict : ∀ i ∈ Finset.univ,
      (closedConflicts R Finset.univ i).card ≤ 3 := by
    intro i hi
    let Ei : ι → Finset V := fun j => pairEndpointRegion src dst (P j)
    have hsub : closedConflicts R Finset.univ i ⊆
        closedConflicts Ei Finset.univ i := by
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      simp only [closedConflicts, Finset.mem_filter, Finset.mem_univ,
        true_and] at hj ⊢
      rcases hj' with hEq | hroute
      · exact Or.inl hEq
      · exact Or.inr (hrouteBridge i j hroute)
    have hcard := Finset.card_le_card hsub
    have hEbound : (closedConflicts Ei Finset.univ i).card ≤ 3 := by
      exact endpoint_closed_conflicts_card_le_three_local src dst Ei P
        (fun j => rfl) hdegree hinj i
    exact hcard.trans hEbound
  exact exists_disjoint_subfamily_of_threshold R 3 threshold (by norm_num)
    hconflict hsize









end Erdos1016.Proof.CubicEndpointConflicts

end
