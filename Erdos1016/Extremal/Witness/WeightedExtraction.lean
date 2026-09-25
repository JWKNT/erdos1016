import Erdos1016.Extremal.Witness.LeastMissing
import Erdos1016.Graph.ConnectedCover

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Erdos1016.ShortProof
open PhysicalGraph RestrictedCycles

/-- Simultaneous integer and real budgets for the same stopped witness.
The real charge can use the actual-rank tail, without a rank-padding argument. -/
theorem extend_to_rank_with_weights (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) (b : ℕ → ℝ)
    (hb : ∀ s, 0 ≤ b s)
    (hcost : ∀ E : Finset G.Edge, G.restrictedCycleRank E < K →
      ∀ C : G.CycleWord, SupportedPrefix G E (G.wordLength C.1 - 1) →
      (G.wordLength C.1 : ℝ) ≤ b (G.restrictedCycleRank E))
    (E : Finset G.Edge) :
    ∃ F : Finset G.CycleWord,
      K ≤ G.restrictedCycleRank (E ∪ witnessSupportEdges G F) ∧
      F.card ≤ K - G.restrictedCycleRank E ∧
      (E ∪ witnessSupportEdges G F).card ≤ E.card +
        ∑ s ∈ Finset.Ico (G.restrictedCycleRank E) K, (initialCapacity s + 1) ∧
      ((E ∪ witnessSupportEdges G F).card : ℝ) ≤ (E.card : ℝ) +
        ∑ s ∈ Finset.Ico (G.restrictedCycleRank E) K, b s := by
  classical
  generalize hd : K - G.restrictedCycleRank E = d
  induction d using Nat.strong_induction_on generalizing E with
  | h d ih =>
    by_cases hp : K ≤ G.restrictedCycleRank E
    · refine ⟨∅, ?_, ?_, ?_, ?_⟩
      · simpa [witnessSupportEdges] using hp
      · simp
      · simp [witnessSupportEdges]
      · simpa [witnessSupportEdges] using Finset.sum_nonneg (fun s _ => hb s)
    · have hpK : G.restrictedCycleRank E < K := by omega
      obtain ⟨C, hnew, hprefix⟩ := exists_least_missing_cycle_with_prefix G K hcov E hpK
      have hlenR := hcost E hpK C hprefix
      have hi := coverage_le_initialCapacity (G.restrictPhysical E)
        (show (G.restrictPhysical E).cycleRank ≤ G.restrictedCycleRank E by
          rw [G.restrictPhysical_cycleRank]) (initialCoverage_of_prefix G E _ hprefix)
      have hlen : G.wordLength C.1 ≤ initialCapacity (G.restrictedCycleRank E) + 1 := by omega
      let E' := E ∪ G.edgeSupport C.1
      have hpq : G.restrictedCycleRank E < G.restrictedCycleRank E' :=
        restrictedCycleRank_lt_of_new_cycle G E E' C
          Finset.subset_union_left Finset.subset_union_right hnew
      have hdiff : K - G.restrictedCycleRank E' < d := by omega
      obtain ⟨F, hr, hc, he, heR⟩ := ih _ hdiff E' rfl
      have hunion : E ∪ witnessSupportEdges G (insert C F) =
          E' ∪ witnessSupportEdges G F := by
        simp [witnessSupportEdges, E', Finset.union_assoc]
      have hsub : Finset.Ico (G.restrictedCycleRank E') K ⊆
          Finset.Ico (G.restrictedCycleRank E + 1) K := by
        intro s hs
        rcases Finset.mem_Ico.mp hs with ⟨hs, hsK⟩
        exact Finset.mem_Ico.mpr ⟨by omega, hsK⟩
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun s => initialCapacity s + 1)
        hsub (fun _ _ _ => Nat.zero_le _)
      have hsumR := Finset.sum_le_sum_of_subset_of_nonneg (f := b) hsub (fun s _ _ => hb s)
      dsimp only at hsum hsumR
      have he' : E'.card ≤ E.card + G.wordLength C.1 := Finset.card_union_le _ _
      have he'R : (E'.card : ℝ) ≤ (E.card : ℝ) + b (G.restrictedCycleRank E) := by
        have hcast : (E'.card : ℝ) ≤ (E.card : ℝ) + (G.wordLength C.1 : ℝ) := by exact_mod_cast he'
        linarith
      refine ⟨insert C F, ?_, ?_, ?_, ?_⟩
      · rw [hunion]
        exact hr
      · have hcard := Finset.card_insert_le C F
        omega
      · rw [hunion, Finset.sum_eq_sum_Ico_succ_bot hpK]
        omega
      · rw [hunion, Finset.sum_eq_sum_Ico_succ_bot hpK]
        linarith

/-- A single union satisfies the rank target, the few-components condition,
and both edge budgets. This statement counts components on edge support. -/
theorem exists_weighted_few_cycle_witness (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) (b : ℕ → ℝ)
    (hb : ∀ s, 0 ≤ b s)
    (hcost : ∀ E : Finset G.Edge, G.restrictedCycleRank E < K →
      ∀ C : G.CycleWord, SupportedPrefix G E (G.wordLength C.1 - 1) →
      (G.wordLength C.1 : ℝ) ≤ b (G.restrictedCycleRank E)) :
    ∃ F : Finset G.CycleWord,
      K ≤ G.restrictedCycleRank (witnessSupportEdges G F) ∧ F.card ≤ K ∧
      Nat.card (cycleUnionGraph G F).ConnectedComponent ≤ K ∧
      (witnessSupportEdges G F).card ≤ ∑ s ∈ Finset.range K, (initialCapacity s + 1) ∧
      ((witnessSupportEdges G F).card : ℝ) ≤ ∑ s ∈ Finset.range K, b s := by
  obtain ⟨F, hr, hc, he, hbF⟩ := extend_to_rank_with_weights G K hcov b hb hcost ∅
  have hc' : F.card ≤ K := by simpa [empty_restricted_rank] using hc
  refine ⟨F, by simpa using hr, hc', (cycleUnion_component_count_le G F).trans hc', ?_, ?_⟩
  · simpa [empty_restricted_rank, Nat.Ico_zero_eq_range] using he
  · simpa [empty_restricted_rank, Nat.Ico_zero_eq_range] using hbF

end Erdos1016.ShortProof
