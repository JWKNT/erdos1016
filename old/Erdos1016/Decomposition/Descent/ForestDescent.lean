import Erdos1016.Decomposition.Descent.GraphDescentTree
import Erdos1016.Probability.Regions.TripleCutPackingBound
import Erdos1016.Probability.Regions.FixedCutPackingThreshold

set_option autoImplicit false

/-!
# The actual finite forest descent

The expanding-leaf stopping theorem is the analytic input. All other inputs
to the signed-credit root estimate, including the fixed-cut packing of the
small negative leaves, follow here from the actual graph decomposition.
-/

noncomputable section

namespace Erdos1016.Proof.FiniteForestDescent

open scoped BigOperators
open SafeCore
open GraphDescentTree
open PhysicalManyRegionProbabilityBridge

/-- The fixed cut cap is chosen before the scale parameter `R`. -/
def fixedCutCap (T₀ : ℕ → ℕ) : ℕ :=
  max 3 (Nat.ceil ((1 / 16 : ℝ) * (T₀ 2 : ℝ) ^ (7 / 8 : ℝ)))

/-- The existing finite many-region estimate's explicit threshold. -/
def leafPackingThreshold (T₀ : ℕ → ℕ) (R : ℕ) : ℕ :=
  8 * R * 2 ^ fixedCutCap T₀ * (2 ^ (2 * fixedCutCap T₀) + dyadicRegionCutoffExponent R)

/-- The small-leaf threshold is quadratic with a coefficient chosen before
the rank scale varies. The ceiling logarithm is bounded by the existing
integer logarithmic cutoff. -/
theorem leafPackingThreshold_le_quadratic (T₀ : ℕ → ℕ) (R : ℕ) (hR : 5 ≤ R) :
    leafPackingThreshold T₀ R ≤
      ManyRegionsLogCutoff.fixedCutCoefficient (fixedCutCap T₀) * R ^ 2 := by
  have hlog : dyadicRegionCutoffExponent R ≤ ManyRegionsLogCutoff.cutoff R := by
    apply (Nat.le_pow_iff_clog_le Nat.one_lt_two).mp
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two (4 * R)).le
  apply le_trans _ (ManyRegionsLogCutoff.movingRegionThreshold_le_quadratic
    R (fixedCutCap T₀) hR)
  unfold leafPackingThreshold ManyRegionsLogCutoff.movingRegionThreshold
  exact Nat.mul_le_mul_left _ (by omega)

private theorem actualCut_eq_cutSize (G : PhysicalGraph) (U : Finset G.Vertex) :
    G.actualCut U = cutSize G U := by
  unfold PhysicalGraph.actualCut cutSize
  congr 1
  ext e
  simp only [PhysicalGraph.cutEdges, ownerCut, crossing, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_compl]

/-- The small negative leaves form a genuine packing of connected cyclic
regions with cut bounded by the fixed two-exterior stopping threshold. -/
theorem small_negative_leaves_card_lt
    (G : PhysicalGraph) (hG : G.IsConnected) (U : Finset G.Vertex)
    (hcubic : ∀ v ∈ U, G.degree v = 3)
    (E : Finset G.Edge) (houtside : internalEdges G U ⊆ Eᶜ)
    (R : ℕ) (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) < G.outsideLinearForestProbability E)
    (T₀ : ℕ → ℕ) (hTmono : Monotone T₀)
    (t : Decomposition G canonicalParameters U)
    (hstop : ∀ L ∈ t.leaves, potential G canonicalParameters L < 0 →
      L.card < T₀ (G.originalExteriorComponents L)) :
    (smallNegativeLeaves G t).card < leafPackingThreshold T₀ R := by
  classical
  apply PhysicalActualCutTriplePackingAdapter.card_lt_manyRegionThreshold_of_connectedRegions
    G E R (fixedCutCap T₀) hR (smallNegativeLeaves G t) hG
  · intro L hL e he
    have hleaf := (Finset.mem_filter.mp hL).1
    have hsub := t.leaf_subset L hleaf
    apply houtside
    have hed := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub hed.1, hsub hed.2⟩
  · intro L hL
    obtain ⟨hleaf, hneg, hext⟩ := Finset.mem_filter.mp hL
    have hconn := t.leaf_connected L hleaf
    have hlow : (cutSize G L : ℝ) ≤ (1 / 16 : ℝ) * (L.card : ℝ) ^ (7 / 8 : ℝ) := by
      change (cutSize G L : ℝ) - (1 / 16 : ℝ) * (L.card : ℝ) ^ (7 / 8 : ℝ) < 0 at hneg
      linarith
    have hcyclic := low_cut_is_cyclic G
      (fun v hv => hcubic v (t.leaf_subset L hleaf hv)) hconn
      (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num : (1 / 16 : ℝ) < 1)
      (by norm_num : (7 / 8 : ℝ) ≤ 1) hlow
    refine ⟨⟨(connectedRegion_iff_induce_connected G L).mp hcyclic.1, hcyclic.2⟩, ?_⟩
    have hsize : L.card ≤ T₀ 2 := (hstop L hleaf hneg).le.trans (hTmono hext)
    have hpow : (L.card : ℝ) ^ (7 / 8 : ℝ) ≤ (T₀ 2 : ℝ) ^ (7 / 8 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsize) (by norm_num)
    have hcut : (cutSize G L : ℝ) ≤
        Nat.ceil ((1 / 16 : ℝ) * (T₀ 2 : ℝ) ^ (7 / 8 : ℝ)) :=
      (hlow.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))).trans (Nat.le_ceil _)
    rw [actualCut_eq_cutSize]
    exact (show cutSize G L ≤ Nat.ceil ((1 / 16 : ℝ) * (T₀ 2 : ℝ) ^ (7 / 8 : ℝ))
      by exact_mod_cast hcut).trans (le_max_right _ _)
  · intro A hA B hB hne
    exact t.leaves_pairwise (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hB).1 hne
  · exact hprob

/-- Proposition 7.5 for an actual simple owner. The complete additive term
is retained. No existence of a negative leaf is assumed. -/
theorem root_additive_bound
    (G : PhysicalGraph) (hG : G.IsConnected) (U : Finset G.Vertex)
    (hU : ConnectedRegion G U) (hproper : Uᶜ.Nonempty)
    (hcubic : ∀ v ∈ U, G.degree v = 3)
    (E : Finset G.Edge) (houtside : internalEdges G U ⊆ Eᶜ)
    (R : ℕ) (hR : 5 ≤ R)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) < G.outsideLinearForestProbability E)
    (T₀ : ℕ → ℕ) (hTmono : Monotone T₀)
    (hstop : ∀ L ⊆ U, ConnectedRegion G L → Expanded G canonicalParameters L →
      potential G canonicalParameters L < 0 → L.card < T₀ (G.originalExteriorComponents L)) :
    (U.card : ℝ) ^ (7 / 8 : ℝ) ≤ 16 * cutSize G U +
      (G.originalExteriorComponents U + 2 * leafPackingThreshold T₀ R : ℝ) *
        (T₀ (G.originalExteriorComponents U + leafPackingThreshold T₀ R) : ℝ) ^ (7 / 8 : ℝ) := by
  classical
  obtain ⟨t⟩ := exists_decomposition G canonicalParameters hU
  have hleafStop : ∀ L ∈ t.leaves, potential G canonicalParameters L < 0 →
      L.card < T₀ (G.originalExteriorComponents L) :=
    fun L hL => hstop L (t.leaf_subset L hL) (t.leaf_connected L hL) (t.leaf_expanded L hL)
  have hsmall := small_negative_leaves_card_lt G hG U hcubic E houtside R hR hprob
    T₀ hTmono t hleafStop
  by_cases hnegative : ∃ L ∈ t.leaves, potential G canonicalParameters L < 0
  · have hrootPos : 1 ≤ G.originalExteriorComponents U := by
      rw [← exteriorCount_eq_original]
      exact exteriorCount_pos G hproper
    have hleafPos : ∀ L ∈ t.leaves, 1 ≤ G.originalExteriorComponents L := by
      intro L hL
      rw [← exteriorCount_eq_original]
      exact exteriorCount_pos G (proper_of_subset G hproper (t.leaf_subset L hL))
    have hM : 1 ≤ leafPackingThreshold T₀ R := by omega
    have h := general_root_additive_inequality_of_decomposition G hG t
      (leafPackingThreshold T₀ R) T₀ hnegative hsmall.le hleafPos hrootPos hM hleafStop hTmono
    simpa [Additive.sizePow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  · have hnonnegative : 0 ≤ potential G canonicalParameters U := by
      apply le_trans _ t.potential_sum_le
      exact Finset.sum_nonneg fun L hL => le_of_not_gt (fun hn => hnegative ⟨L, hL, hn⟩)
    change 0 ≤ (cutSize G U : ℝ) - (1 / 16 : ℝ) * (U.card : ℝ) ^ (7 / 8 : ℝ)
      at hnonnegative
    have hrest : 0 ≤
        (G.originalExteriorComponents U + 2 * leafPackingThreshold T₀ R : ℝ) *
          (T₀ (G.originalExteriorComponents U + leafPackingThreshold T₀ R) : ℝ) ^ (7 / 8 : ℝ) := by
      positivity
    linarith

end Erdos1016.Proof.FiniteForestDescent
