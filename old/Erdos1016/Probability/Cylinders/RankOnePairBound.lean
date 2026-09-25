import Erdos1016.Probability.Cylinders.ZeroCoordinateCylinders

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ManyCyclicRegionCutCylinders

/-- If two zero-cylinder constraint spaces overlap in dimension at most one,
the pair cylinder costs at most one factor of two beyond independence. This
is a purely finite-dimensional linear-algebra estimate. -/
theorem zeroCylinder_pair_probability_le_twice_product
    {W : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] [Fintype W] [Fintype F₂]
    (L M : Submodule F₂ (Module.Dual F₂ W))
    (hoverlap : Module.finrank F₂ ↥(L ⊓ M) ≤ 1) :
    vectorProbability (fun x => zeroCylinder L x ∧ zeroCylinder M x) ≤
      2 * vectorProbability (zeroCylinder L) *
        vectorProbability (zeroCylinder M) := by
  have hpair := zeroCylinder_pair_probability L M
  rw [hpair.1, zeroCylinder_probability L, zeroCylinder_probability M]
  let dL := Module.finrank F₂ L
  let dM := Module.finrank F₂ M
  let dS := Module.finrank F₂ ↥(L ⊔ M)
  let dI := Module.finrank F₂ ↥(L ⊓ M)
  have hdim : dL + dM = dS + dI := by
    simpa [dL, dM, dS, dI] using hpair.2
  have hpow : (2 : ℝ) ^ dL * (2 : ℝ) ^ dM =
      (2 : ℝ) ^ dS * (2 : ℝ) ^ dI := by
    rw [← pow_add, ← pow_add, hdim]
  have hpowI : (2 : ℝ) ^ dI ≤ 2 := by
    calc
      (2 : ℝ) ^ dI ≤ (2 : ℝ) ^ 1 :=
        pow_le_pow_right₀ (by norm_num) (by simpa [dI] using hoverlap)
      _ = 2 := by norm_num
  have hprod : (2 : ℝ) ^ dL * (2 : ℝ) ^ dM ≤ 2 * (2 : ℝ) ^ dS := by
    rw [hpow]
    nlinarith [hpowI, (show 0 ≤ (2 : ℝ) ^ dS by positivity)]
  have hSpos : 0 < (2 : ℝ) ^ dS := by positivity
  have hABpos : 0 < (2 : ℝ) ^ dL * (2 : ℝ) ^ dM := by positivity
  calc
    1 / (2 : ℝ) ^ dS ≤
        2 / ((2 : ℝ) ^ dL * (2 : ℝ) ^ dM) := by
      apply (div_le_div_iff₀ hSpos hABpos).2
      nlinarith [hprod]
    _ = 2 * (1 / (2 : ℝ) ^ dL) * (1 / (2 : ℝ) ^ dM) := by
      field_simp

end Erdos1016.Proof.ManyCyclicRegionCutCylinders
