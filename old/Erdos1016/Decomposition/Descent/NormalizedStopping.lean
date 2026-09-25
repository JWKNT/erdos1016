import Erdos1016.Probability.Avoidance.UniformCoreBound
import Erdos1016.Decomposition.Descent.StoppingThreshold
import Erdos1016.Probability.Conditional.RegionForestMonotonicity
import Erdos1016.Probability.Conditional.PhysicalMultigraphForestLaw
import Erdos1016.Decomposition.Descent.CleanupRootDescent

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

namespace Erdos1016.Proof.NormalizedAnalyticStopping

open Erdos1016 SafeCore CleanupSpecification SingleCorridorRoute
open AnalyticStoppingThreshold

/-- Negative expanding regions of a cubic owner stop at the explicit analytic
threshold. Normalization occurs in the unchanged owner, and its actual
exterior count is retained throughout the conditioning estimate. -/
theorem negative_region_stops {N₀ : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hdecay : UniformCoreDecay.Estimate N₀ γ)
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hproper : Uᶜ.Nonempty) (hcubic : ∀ v ∈ U, G.degree v = 3)
    (hprob : (1 / 2 : ℝ) < regionForestProbability (routeGraph G) U)
    (L : Finset G.Vertex) (hLU : L ⊆ U) (hconn : ConnectedRegion G L)
    (hexp : Expanded G canonicalParameters L) (hneg : potential G canonicalParameters L < 0) :
    L.card < stoppingThreshold N₀ γ (G.originalExteriorComponents L) := by
  classical
  have hlow : Low G canonicalParameters L := by
    change (cutSize G L : ℝ) ≤ budget G canonicalParameters L
    change (cutSize G L : ℝ) - budget G canonicalParameters L < 0 at hneg
    linarith
  obtain ⟨K, hKL, hK, hsize, hext, _⟩ := normalize_good_region G canonicalParameters
    (fun v hv => hcubic v (hLU hv)) ⟨hconn, hexp, hlow⟩
  have hKU : K ⊆ U := hKL.trans hLU
  have hproperL : Lᶜ.Nonempty := proper_of_subset G hproper hLU
  have hc : 0 < G.originalExteriorComponents L := by
    rw [← exteriorCount_eq_original]
    exact exteriorCount_pos G hproperL
  by_contra hnot
  have hlarge := Nat.le_of_not_gt hnot
  have hsize' : (15 / 16 : ℝ) * (L.card : ℝ) ≤ (K.card : ℝ) := by
    norm_num [canonicalParameters] at hsize ⊢
    exact hsize
  obtain ⟨hN, hcutoff⟩ := core_onsets_le N₀ γ hc hlarge hsize'
  have hdec := UniformCoreDecay.normalized_oneApex_bound hdecay G K
    (fun v hv => hcubic v (hKU hv)) hK hN
  have hKext : G.originalExteriorComponents K ≤ G.originalExteriorComponents L := by
    simpa only [exteriorCount_eq_original] using hext
  have hfactor : (2 : ℝ) ^ (G.originalExteriorComponents K - 1) ≤
      (2 : ℝ) ^ (G.originalExteriorComponents L - 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hKext 1)
  obtain ⟨v₀, hv₀⟩ := proper_of_subset G hproper hKU
  have htrace := G.originalExteriorTraceBound K v₀ (Finset.mem_compl.mp hv₀)
  have hhalf : G.originalForestFraction K ≤ (1 / 2 : ℝ) := by
    calc
      G.originalForestFraction K ≤
          (2 : ℝ) ^ (G.originalExteriorComponents K - 1) * G.oneApexForestFraction K := htrace
      _ ≤ (2 : ℝ) ^ (G.originalExteriorComponents K - 1) *
          (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (K.card : ℝ))) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
      _ ≤ (2 : ℝ) ^ (G.originalExteriorComponents L - 1) *
          (2 : ℝ) ^ (-γ * Real.sqrt (Real.logb 2 (K.card : ℝ))) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ 1 / 2 := exterior_conditioning_factor_le_half hγ hc hcutoff
  have hmono := RegionForestMonotonicity.regionForestProbability_mono (routeGraph G) hKU
  have hacyclic := PhysicalMultigraphForestLaw.regionForestProbability_le_originalForestFraction G K
  exact (not_lt_of_ge (hmono.trans (hacyclic.trans hhalf))) hprob

/-- The uniform decay estimate discharges every analytic leaf premise in the
full forest descent on a cleanup output's actual port-expanded owner. -/
theorem cleanup_root_additive_bound {N₀ : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hdecay : UniformCoreDecay.Estimate N₀ γ)
    {G : PhysicalGraph} {I : CleanupInput G} (O : CleanupOutput I) (hR : 5 ≤ I.R) :
    (O.root.card : ℝ) ^ (7 / 8 : ℝ) ≤ 16 * (cutEdges O.Γ O.root).card +
      (exteriorComponentCount O.Γ O.root +
        2 * FiniteForestDescent.leafPackingThreshold (stoppingThreshold N₀ γ) I.R : ℝ) *
        (stoppingThreshold N₀ γ (exteriorComponentCount O.Γ O.root +
          FiniteForestDescent.leafPackingThreshold (stoppingThreshold N₀ γ) I.R) : ℝ) ^ (7 / 8 : ℝ) := by
  apply CleanupRootDescent.root_additive_bound O hR _ (stoppingThreshold_monotone N₀ hγ)
  apply negative_region_stops hγ hdecay _ _ (CleanupRootDescent.root_proper O)
  · intro v hv
    rw [CleanupRootDescent.rootRegion_eq_image] at hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    exact PortExpansionDegree.cleanup_expanded_root_degree_eq_three O hq
  · have hpositive : (0 : ℝ) < 1 / (I.R : ℝ) := by positivity
    have h := I.outside_probability.trans_le
      (PortExpansionMarginal.probability_domination_rootPortExpansion O)
    change (1 / 2 : ℝ) < regionForestProbability
      (PortExpansionCycleSpace.Physical O.Γ O.root O.root_structure)
      (PortExpansion.rootRegion O.Γ O.root O.root_structure)
    rw [CleanupRootDescent.rootRegion_eq_image]
    linarith

end Erdos1016.Proof.NormalizedAnalyticStopping

end
