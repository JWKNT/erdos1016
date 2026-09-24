import Erdos1016.Decomposition.TwoCore.PruningNormalization

set_option autoImplicit false

/-!
# Growing full two-cores with the source's quantitative geometry

Combines the constructed safe-sibling extraction with actual leaf pruning.
The proof retains all labels in the original owner and never assumes
SafeCoreExtraction as an input.
-/
noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.SafeCore
local instance instSafeCoreNormalizedExtractionPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- epsilon*(1-B)^(1-p), written without a negative-exponent rewrite. -/
def coreExpansion (P : CutParameters) : ℝ := P.epsilon / (1 - P.B) ^ (P.p - 1)

/-- B*(1-B)^(-p). -/
def coreBudget (P : CutParameters) : ℝ := P.B / (1 - P.B) ^ P.p

theorem coreExpansion_pos (P : CutParameters) : 0 < coreExpansion P :=
  div_pos P.epsilon_pos (Real.rpow_pos_of_pos (sub_pos.2 P.B_lt_one) _)

theorem coreBudget_pos (P : CutParameters) : 0 < coreBudget P :=
  div_pos P.B_pos (Real.rpow_pos_of_pos (sub_pos.2 P.B_lt_one) _)

/-- The scalar rescaling in source (16.2), proved at finite sizes. -/
theorem rescale_twoCore (P : CutParameters) {u k b : ℝ}
    (hu : 0 < u) (hk : 0 < k) (hsize : (1 - P.B) * u ≤ k)
    (hcut : b ≤ P.B * u ^ P.p) :
    b ≤ coreBudget P * k ^ P.p ∧
      coreExpansion P * k ^ (P.p - 1) ≤ P.epsilon * u ^ (P.p - 1) := by
  have hq : 0 < 1 - P.B := sub_pos.2 P.B_lt_one
  have hur : u ≤ k / (1 - P.B) := (le_div_iff₀ hq).2 (by nlinarith only [hsize])
  have hp := Real.rpow_le_rpow hu.le hur P.p_pos.le
  have hr := Real.rpow_le_rpow_of_nonpos hu hur (sub_nonpos.mpr P.p_lt_one.le)
  rw [Real.div_rpow hk.le hq.le] at hp hr
  constructor
  · calc
      b ≤ P.B * u ^ P.p := hcut
      _ ≤ P.B * (k ^ P.p / (1 - P.B) ^ P.p) := mul_le_mul_of_nonneg_left hp P.B_pos.le
      _ = coreBudget P * k ^ P.p := by unfold coreBudget; ring
  · calc
      coreExpansion P * k ^ (P.p - 1) =
          P.epsilon * (k ^ (P.p - 1) / (1 - P.B) ^ (P.p - 1)) := by
            unfold coreExpansion; ring
      _ ≤ P.epsilon * u ^ (P.p - 1) := mul_le_mul_of_nonneg_left hr P.epsilon_pos.le

/-- The extracted object has all degree and geometric properties required
by the local theorem, before identifying it with a reindexed graph. -/
structure NormalizedRegion (G : PhysicalGraph) (P : CutParameters)
    (K : Finset G.Vertex) : Prop where
  connected : ConnectedRegion G K
  minTwo : MinTwo G K
  maxThree : ∀ v ∈ K, G.traceInsideDegree K v ≤ 3
  expansion : HasExpansion G K (coreExpansion P * (K.card : ℝ) ^ (P.p - 1))
  boundary : (cutSize G K : ℝ) ≤ coreBudget P * (K.card : ℝ) ^ P.p

theorem normalize_good_region (G : PhysicalGraph) (P : CutParameters)
    {J : Finset G.Vertex} (hc : ∀ v ∈ J, G.degree v = 3) (hj : GoodRegion G P J) :
    ∃ K ⊆ J, NormalizedRegion G P K ∧
      (1 - P.B) * (J.card : ℝ) ≤ K.card ∧
      exteriorCount G K ≤ exteriorCount G J ∧
      (∀ A ⊆ J, MinTwo G A → A ⊆ K) := by
  obtain ⟨K, hsize, hmax⟩ := low_region_full_twoCore G P hc hj.1 hj.2.2 hj.2.1
  have hu : 0 < (J.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hj.1.1
  have hk : 0 < (K.vertices.card : ℝ) := by exact_mod_cast Finset.card_pos.2 K.connected.1
  have hb : (cutSize G K.vertices : ℝ) ≤ P.B * (J.card : ℝ) ^ P.p :=
    (by exact_mod_cast K.cut_le : (cutSize G K.vertices : ℝ) ≤ cutSize G J).trans hj.2.2
  have hrescale := rescale_twoCore P hu hk hsize hb
  refine ⟨K.vertices, K.subset, ⟨K.connected, K.minTwo, hmax, ?_, hrescale.1⟩,
    hsize, K.exterior_le, K.maximal⟩
  intro A hA
  exact (mul_le_mul_of_nonneg_right hrescale.2 (Nat.cast_nonneg _)).trans (K.expansion A hA)





end Erdos1016.SafeCore
