import Erdos1016.Graph.RestrictedCycles
import Erdos1016.Extremal.Capacity.WitnessSupport

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.ShortProof
open PhysicalGraph RestrictedCycles

/-- The cycle supports chosen so far represent every length up to `k`. -/
def SupportedPrefix (G : PhysicalGraph) (E : Finset G.Edge) (k : ℕ) : Prop :=
  ∀ ℓ, 3 ≤ ℓ → ℓ ≤ k →
    ∃ C : G.CycleWord, G.wordLength C.1 = ℓ ∧ G.edgeSupport C.1 ⊆ E

lemma initialCoverage_of_prefix (G : PhysicalGraph) (E : Finset G.Edge) (k : ℕ)
    (h : SupportedPrefix G E k) : (G.restrictPhysical E).InitialCoverage k := by
  intro ℓ hℓ
  obtain ⟨C, hlen, hsupp⟩ := h ℓ (Finset.mem_Icc.mp hℓ).1 (Finset.mem_Icc.mp hℓ).2
  obtain ⟨D, hD⟩ := restrictCycleWord_isCycle G E C hsupp
  apply Finset.mem_image.mpr
  refine ⟨D, Finset.mem_univ _, ?_⟩
  change (G.restrictPhysical E).wordLength D.1 = ℓ
  rw [hD, restrictCycleWord_length G E C hsupp, hlen]

/-- Until rank `K` is reached, the least absent length supplies a new cycle
whose length is charged to the preceding rank. No rank-jump bound is assumed. -/
theorem exists_least_missing_cycle_with_prefix (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) (E : Finset G.Edge)
    (hrank : G.restrictedCycleRank E < K) :
    ∃ C : G.CycleWord, ¬ G.edgeSupport C.1 ⊆ E ∧
      SupportedPrefix G E (G.wordLength C.1 - 1) := by
  classical
  let Missing : ℕ → Prop := fun ℓ => 3 ≤ ℓ ∧ ℓ ≤ 2 ^ K + 1 ∧
    ¬ ∃ C : G.CycleWord, G.wordLength C.1 = ℓ ∧ G.edgeSupport C.1 ⊆ E
  have hex : ∃ ℓ, Missing ℓ := by
    by_contra hn
    have hp : SupportedPrefix G E (2 ^ K + 1) := by
      intro ℓ h3 hL
      by_contra hno
      exact hn ⟨ℓ, h3, hL, hno⟩
    have hb := (G.restrictPhysical E).coverage_bound (initialCoverage_of_prefix G E _ hp)
    rw [G.restrictPhysical_cycleRank] at hb
    have hpow : 2 ^ G.restrictedCycleRank E < 2 ^ K :=
      Nat.pow_lt_pow_right (by decide) hrank
    omega
  let k := Nat.find hex
  have hk : Missing k := Nat.find_spec hex
  have hp : SupportedPrefix G E (k - 1) := by
    intro ℓ h3 hlt
    by_contra hno
    have hℓk : ℓ < k := by have := hk.1; omega
    exact Nat.find_min hex hℓk ⟨h3, by have := hk.2.1; omega, hno⟩
  obtain ⟨C, _, hlen⟩ := Finset.mem_image.mp (hcov (Finset.mem_Icc.mpr ⟨hk.1, hk.2.1⟩))
  refine ⟨C, fun hs => hk.2.2 ⟨C, hlen, hs⟩, ?_⟩
  simpa [hlen] using hp

/-- The least missing length is at most one beyond the rank's capacity. -/
theorem exists_least_missing_cycle (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) (E : Finset G.Edge)
    (hrank : G.restrictedCycleRank E < K) :
    ∃ C : G.CycleWord, ¬ G.edgeSupport C.1 ⊆ E ∧
      G.wordLength C.1 ≤ initialCapacity (G.restrictedCycleRank E) + 1 := by
  obtain ⟨C, hn, hp⟩ := exists_least_missing_cycle_with_prefix G K hcov E hrank
  have hi := coverage_le_initialCapacity (G.restrictPhysical E)
    (show (G.restrictPhysical E).cycleRank ≤ G.restrictedCycleRank E by
      rw [G.restrictPhysical_cycleRank]) (initialCoverage_of_prefix G E _ hp)
  exact ⟨C, hn, by omega⟩

/-- Stop at the first rank crossing. The selected family has at most one
cycle per preceding rank, even if a cycle creates several new independent cycles. -/
theorem extend_to_rank (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) (E : Finset G.Edge) :
    ∃ F : Finset G.CycleWord,
      K ≤ G.restrictedCycleRank (E ∪ witnessSupportEdges G F) ∧
      F.card ≤ K - G.restrictedCycleRank E ∧
      (E ∪ witnessSupportEdges G F).card ≤ E.card +
        ∑ s ∈ Finset.Ico (G.restrictedCycleRank E) K, (initialCapacity s + 1) := by
  classical
  generalize hd : K - G.restrictedCycleRank E = d
  induction d using Nat.strong_induction_on generalizing E with
  | h d ih =>
    by_cases hp : K ≤ G.restrictedCycleRank E
    · refine ⟨∅, ?_, ?_, ?_⟩
      · simpa [witnessSupportEdges] using hp
      · simp
      · simp [witnessSupportEdges]
    · have hpK : G.restrictedCycleRank E < K := by omega
      obtain ⟨C, hnew, hlen⟩ := exists_least_missing_cycle G K hcov E hpK
      let E' := E ∪ G.edgeSupport C.1
      have hpq : G.restrictedCycleRank E < G.restrictedCycleRank E' :=
        restrictedCycleRank_lt_of_new_cycle G E E' C
          Finset.subset_union_left Finset.subset_union_right hnew
      have hdiff : K - G.restrictedCycleRank E' < d := by omega
      obtain ⟨F, hr, hc, he⟩ := ih _ hdiff E' rfl
      have hunion : E ∪ witnessSupportEdges G (insert C F) =
          E' ∪ witnessSupportEdges G F := by
        simp [witnessSupportEdges, E', Finset.union_assoc]
      have hsum : (∑ s ∈ Finset.Ico (G.restrictedCycleRank E') K,
          (initialCapacity s + 1)) ≤
          ∑ s ∈ Finset.Ico (G.restrictedCycleRank E + 1) K, (initialCapacity s + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          rcases Finset.mem_Ico.mp hs with ⟨hs, hsK⟩
          exact Finset.mem_Ico.mpr ⟨by omega, hsK⟩
        · intro s hs hnot
          exact Nat.zero_le _
      have he' : E'.card ≤ E.card + (initialCapacity (G.restrictedCycleRank E) + 1) := by
        calc
          E'.card ≤ E.card + (G.edgeSupport C.1).card := Finset.card_union_le _ _
          _ ≤ E.card + (initialCapacity (G.restrictedCycleRank E) + 1) :=
            Nat.add_le_add_left hlen _
      refine ⟨insert C F, ?_, ?_, ?_⟩
      · rw [hunion]
        exact hr
      · have hcard := Finset.card_insert_le C F
        omega
      · rw [hunion, Finset.sum_eq_sum_Ico_succ_bot hpK]
        omega

lemma empty_restricted_rank (G : PhysicalGraph) : G.restrictedCycleRank ∅ = 0 := by
  haveI : Subsingleton (G.RestrictedWord ∅) := inferInstance
  haveI : Subsingleton (G.RestrictedCycleSpace ∅) := inferInstance
  exact Module.finrank_zero_of_subsingleton

/-- A union of at most `K` cycles reaches rank `K`, with an edge budget indexed
only by ranks below `K`. This is the few-component witness used by the new proof. -/
theorem exists_few_cycle_witness (G : PhysicalGraph) (K : ℕ)
    (hcov : G.InitialCoverage (2 ^ K + 1)) :
    ∃ F : Finset G.CycleWord,
      K ≤ G.restrictedCycleRank (witnessSupportEdges G F) ∧ F.card ≤ K ∧
      (witnessSupportEdges G F).card ≤
        ∑ s ∈ Finset.range K, (initialCapacity s + 1) := by
  obtain ⟨F, hr, hc, he⟩ := extend_to_rank G K hcov ∅
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa using hr
  · simpa [empty_restricted_rank] using hc
  · simpa [empty_restricted_rank, Nat.Ico_zero_eq_range] using he

end Erdos1016.ShortProof
