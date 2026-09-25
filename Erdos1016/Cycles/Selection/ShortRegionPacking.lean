import Erdos1016.Graph.PackingCover
import Erdos1016.Probability.Moments.SmallCutRegionBound

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

local instance shortRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Actual small connected cyclic regions outside the marked set. The cut
condition is satisfied by short cycles in a subcubic graph. -/
structure ShortCyclicRegion (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ)
    (U : Finset G.Vertex) : Prop where
  outside : U ⊆ Pᶜ
  size : U.card ≤ D
  connected : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected
  cyclic : ∃ z : G.internalCycleSpace U, z ≠ 0
  cut : (G.cutEdges U).card ≤ D

def shortCyclicRegions (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ) :
    Finset (Finset G.Vertex) := Finset.univ.filter (G.ShortCyclicRegion P D)

theorem regionForestProbability_eq_density (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    G.regionForestProbability U = Finite.density (fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U) x.1)) := by
  unfold regionForestProbability Finite.density Finite.count
  have hc : (Fintype.card G.CycleSpace : ℝ) = (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.cycleSpace_card
  rw [hc]
  simp only [Finset.sum_boole]

/-- If the forest probability exceeds one half by `ε`, no disjoint family
of these regions reaches the small-cut contradiction threshold. -/
theorem short_region_packing_card_lt (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D B : ℕ) (ε : ℝ) (hG : G.toSimpleGraph.Connected) (hB : 0 < B)
    (hthreshold : ((D : ℝ) + 1) * (2 : ℝ) ^ D / (2 * B) ≤ ε)
    (hforest : (1 / 2 : ℝ) + ε < G.regionForestProbability Pᶜ)
    (F : Finset (Finset G.Vertex)) (hF : F ⊆ G.shortCyclicRegions P D)
    (hdisj : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → Disjoint U V) : F.card < B := by
  by_contra hn
  have hBF : B ≤ F.card := by omega
  have hFpos : 0 < F.card := lt_of_lt_of_le hB hBF
  have hspec (U : F) : G.ShortCyclicRegion P D U.1 := (Finset.mem_filter.mp (hF U.2)).2
  let U : F → Finset G.Vertex := Subtype.val
  have hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected :=
    fun i => (hspec i).connected
  have hd : Pairwise (fun i j : F => Disjoint (U i) (U j)) := by
    intro i j hij
    exact hdisj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
  have hnonempty : (Finset.univ : Finset F).Nonempty := by
    obtain ⟨S, hS⟩ := Finset.card_pos.mp hFpos
    exact ⟨⟨S, hS⟩, Finset.mem_univ _⟩
  have hbound := G.smallCut_forest_bound U hG hd hconn Finset.univ hnonempty D
    (fun i _ => (hspec i).cut) (fun i _ => (hspec i).cyclic)
    (G.internalEdges Pᶜ) (by
      intro i hi e he
      have hh := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hspec i).outside hh.1, (hspec i).outside hh.2⟩)
  rw [← G.regionForestProbability_eq_density] at hbound
  simp only [Finset.card_univ, Fintype.card_coe] at hbound
  have hden : (0 : ℝ) < 2 * B := by positivity
  have hratio : ((D : ℝ) + 1) * (2 : ℝ) ^ D / (2 * F.card) ≤
      ((D : ℝ) + 1) * (2 : ℝ) ^ D / (2 * B) := by
    apply div_le_div_of_nonneg_left (by positivity) hden
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hBF) (by norm_num)
  linarith

/-- Choose a maximal short-region packing. Its union has bounded size and
meets every eligible region, so the complement has none left. -/
theorem exists_short_region_packing (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D B : ℕ) (ε : ℝ) (hG : G.toSimpleGraph.Connected) (hB : 0 < B)
    (hthreshold : ((D : ℝ) + 1) * (2 : ℝ) ^ D / (2 * B) ≤ ε)
    (hforest : (1 / 2 : ℝ) + ε < G.regionForestProbability Pᶜ) :
    ∃ F : Finset (Finset G.Vertex),
      (∀ U ∈ F, G.ShortCyclicRegion P D U) ∧
      (∀ U ∈ F, ∀ V ∈ F, U ≠ V → Disjoint U V) ∧ F.card < B ∧
      (F.biUnion id).card ≤ B * D ∧ (F.biUnion id) ⊆ Pᶜ ∧
      ∀ U, G.ShortCyclicRegion P D U → ((F.biUnion id) ∩ U).Nonempty := by
  have hne : ∀ U ∈ G.shortCyclicRegions P D, (id U).Nonempty := by
    intro U hU
    have h := (Finset.mem_filter.mp hU).2
    obtain ⟨v⟩ := h.connected.nonempty
    exact ⟨v.1, v.2⟩
  obtain ⟨F, hF, hdisj, hhit⟩ := PackingCover.exists_maximal_disjoint_family
    (G.shortCyclicRegions P D) id hne
  have hspec (U) (hU : U ∈ F) : G.ShortCyclicRegion P D U :=
    (Finset.mem_filter.mp (hF hU)).2
  have hc := G.short_region_packing_card_lt P D B ε hG hB hthreshold hforest F hF hdisj
  refine ⟨F, hspec, hdisj, hc, ?_, ?_, ?_⟩
  · calc
      (F.biUnion id).card ≤ ∑ U ∈ F, U.card := Finset.card_biUnion_le
      _ ≤ ∑ _U ∈ F, D := Finset.sum_le_sum fun U hU => (hspec U hU).size
      _ = F.card * D := by simp
      _ ≤ B * D := Nat.mul_le_mul_right D hc.le
  · intro v hv
    obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
    exact (hspec U hU).outside hv
  · intro U hU
    exact hhit U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)

end Erdos1016.FiniteMultiGraph
