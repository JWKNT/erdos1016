import Erdos1016.PolynomialBound.ParallelLinks

set_option autoImplicit false

/-!
# Parallel cyclic links at the two-fifths threshold

The independent-region probability bound gives at most `3 * 2 ^ t + 1`
small cyclic links. This includes the one component reserved to connect the
two shores. The source paper uses the weaker bound `5 * 2 ^ t`.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open FiniteMultiGraph FiniteMultiGraph.ExteriorComponents
open PolynomialBound.ParallelLinks

local instance parallelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (A B : Finset G.Vertex)

/-- A forest probability of at least two fifths bounds the actual cyclic
components joining two connected shores, including the reserved connector. -/
theorem smallCyclicPart_card_le_two_fifths (hG : G.toSimpleGraph.Connected)
    (hA : (G.toSimpleGraph.induce (↑A : Set G.Vertex)).Connected)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (P : Finset G.Vertex) (t : ℕ) (S : Finset (Component G (A ∪ B)ᶜ))
    (hS : ∀ c ∈ S, SeedPairCorrelation.BothAttached G A B c)
    (hforest : (2 / 5 : ℝ) ≤ G.regionForestProbability Pᶜ) :
    (smallCyclicPart G (A ∪ B)ᶜ P t S).card ≤ 3 * 2 ^ t + 1 := by
  classical
  by_cases hne : (smallCyclicPart G (A ∪ B)ᶜ P t S).Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hc₀S : c₀ ∈ S := (Finset.mem_filter.mp hc₀).1
    have hmem (c : Component G (A ∪ B)ᶜ)
        (hc : c ∈ (smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀) :=
      Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    have hbound := independent_regions_forest_le G (vertices G (A ∪ B)ᶜ) hG
      ((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀)
      (fun c _ => vertices_connected G _ c)
      (fun c _ d _ hcd => vertices_disjoint G _ hcd)
      (fun c hc d hd hcd => links_card_le_one G A B hG hA hB c₀ c d (hS c₀ hc₀S)
        (Finset.ne_of_mem_erase hc).symm (Finset.ne_of_mem_erase hd).symm hcd)
      t (fun c hc => (hmem c hc).2.2.1)
      (fun c hc => G.internalCycleSpace_nontrivial_of_not_forest _ (hmem c hc).2.2.2)
      (G.internalEdges Pᶜ) (by
        intro c hc e he
        have hP := (hmem c hc).2.1
        have hends := (Finset.mem_filter.mp he).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, Finset.mem_compl.mpr ?_, Finset.mem_compl.mpr ?_⟩
        · exact fun hs => hP ⟨G.src e, hs, hends.1⟩
        · exact fun ht => hP ⟨G.dst e, ht, hends.2⟩)
    rw [G.regionForestProbability_eq_density] at hforest
    have hratio : (((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card : ℝ) /
        2 ^ (t + 1) ≤ 3 / 2 := by
      have hpos : (0 : ℝ) < 1 +
          (((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card : ℝ) / 2 ^ (t + 1) := by
        positivity
      have h := (le_div_iff₀ hpos).mp (hforest.trans hbound)
      linarith
    have hle : ((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card ≤ 3 * 2 ^ t := by
      have h := (div_le_iff₀ (show (0 : ℝ) < 2 ^ (t + 1) by positivity)).mp hratio
      rw [pow_succ] at h
      have h' : (((smallCyclicPart G (A ∪ B)ᶜ P t S).erase c₀).card : ℝ) ≤
          3 * 2 ^ t := by nlinarith
      exact_mod_cast h'
    have hcard := Finset.card_erase_add_one hc₀
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Erdos1016.ExactMaximumSupport.LargeGirth
