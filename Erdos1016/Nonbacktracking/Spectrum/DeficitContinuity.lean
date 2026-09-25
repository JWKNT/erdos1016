import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

/-! A continuous symmetric matrix path acquires a kernel between a
nonpositive Rayleigh test and a positive semidefinite endpoint. -/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Nonbacktracking

private theorem real_quadratic_smul {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    dotProduct (c • u) (A.mulVec (c • u)) =
      c ^ 2 * dotProduct u (A.mulVec u) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- The conclusion is an actual nonzero kernel vector. The proof takes the
minimum quadratic form on one fixed sphere and applies the intermediate
value theorem to that minimum. No eigenvalue-continuity premise is used. -/
theorem exists_kernel_on_continuous_symmetric_path
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ) (hM : Continuous M)
    (hsymm : ∀ t, (M t).IsHermitian)
    {a b : ℝ} (hab : a ≤ b) (hb : (M b).PosSemidef)
    (x : ι → ℝ) (hx : x ≠ 0)
    (ha : dotProduct x ((M a).mulVec x) ≤ 0) :
    ∃ t ∈ Set.Icc a b, ∃ u : ι → ℝ, u ≠ 0 ∧ (M t).mulVec u = 0 := by
  let q : ℝ → (ι → ℝ) → ℝ := fun t u => dotProduct u ((M t).mulVec u)
  let K : Set (ι → ℝ) := Metric.sphere 0 ‖x‖
  have hK : IsCompact K := isCompact_sphere 0 ‖x‖
  have hxK : x ∈ K := by simp [K, Metric.mem_sphere]
  have hKne : K.Nonempty := ⟨x, hxK⟩
  have hq : Continuous (Function.uncurry q) := by
    unfold q Matrix.mulVec dotProduct
    fun_prop
  have hqt (t : ℝ) : Continuous (q t) :=
    hq.comp (continuous_const.prodMk continuous_id)
  let m : ℝ → ℝ := fun t => sInf (q t '' K)
  have hm : Continuous m := hK.continuous_sInf hq
  have hmin (t : ℝ) : ∃ u ∈ K, q t u = m t := by
    obtain ⟨u, hu, hmu⟩ := hK.exists_isMinOn hKne (hqt t).continuousOn
    refine ⟨u, hu, ?_⟩
    apply le_antisymm
    · exact le_csInf (hKne.image (q t)) (by rintro z ⟨v, hv, rfl⟩; exact hmu hv)
    · exact csInf_le (hK.bddBelow_image (hqt t).continuousOn) ⟨u, hu, rfl⟩
  have hma : m a ≤ 0 := by
    exact (csInf_le (hK.bddBelow_image (hqt a).continuousOn)
      ⟨x, hxK, rfl⟩).trans ha
  have hmb : 0 ≤ m b := by
    obtain ⟨u, hu, hmu⟩ := hmin b
    rw [← hmu]
    simpa [q] using hb.2 u
  obtain ⟨t, ht, hmt⟩ := intermediate_value_Icc hab hm.continuousOn ⟨hma, hmb⟩
  obtain ⟨u, hu, hmu⟩ := hmin t
  have hu_ne : u ≠ 0 := by
    intro h
    have hnorm : ‖u‖ = ‖x‖ := by simpa [K, Metric.mem_sphere] using hu
    rw [h, norm_zero] at hnorm
    exact hx (norm_eq_zero.mp hnorm.symm)
  have hnonneg : ∀ v : ι → ℝ, 0 ≤ q t v := by
    intro v
    by_cases hv : v = 0
    · simp [hv, q]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let c : ℝ := ‖x‖ / ‖v‖
    have hc : 0 < c := div_pos hxnorm hvnorm
    have hvK : c • v ∈ K := by
      simp only [K, Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hc]
      dsimp [c]
      exact div_mul_cancel₀ ‖x‖ hvnorm.ne'
    have h := csInf_le (hK.bddBelow_image (hqt t).continuousOn)
      (show q t (c • v) ∈ q t '' K from ⟨c • v, hvK, rfl⟩)
    change m t ≤ _ at h
    rw [hmt] at h
    change 0 ≤ dotProduct (c • v) ((M t).mulVec (c • v)) at h
    rw [real_quadratic_smul] at h
    exact nonneg_of_mul_nonneg_right h (sq_pos_of_pos hc)
  have hpsd : (M t).PosSemidef := ⟨hsymm t, by simpa [q] using hnonneg⟩
  refine ⟨t, ht, u, hu_ne, (hpsd.dotProduct_mulVec_zero_iff u).mp ?_⟩
  simpa only [star_trivial] using hmu.trans hmt

end Erdos1016.Nonbacktracking
