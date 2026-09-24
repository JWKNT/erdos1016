import Erdos1016.Nonbacktracking.Spectrum.EvenSpectrum
import Erdos1016.Nonbacktracking.Spectrum.SpectralWitness
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

set_option autoImplicit false

/-!
# Algebraic multiplicities in the actual nonbacktracking trace

We take the roots of `charpoly (B ^ ell)` **with their multiplicities**.
Their sum is the trace. Polynomial spectral mapping identifies each root
with an ell-th power of a spectral value of the original matrix. This avoids
choosing a simultaneous Jordan basis, and does not assert diagonalizability.

This is an alternative formal implementation of the trace step in source
Lemma 5.1. It is not a claim that the distinct spectrum can be summed without
multiplicity. All matrices and eigenvectors below are the actual dart ones.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance algebraicTraceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Matrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pinned-mathlib adapter: characteristic roots and the algebraic spectrum.
The determinant criterion works for nonnormal and nondiagonalizable matrices. -/
theorem mem_matrix_spectrum_iff_charpoly_root (M : Matrix ι ι ℂ) (z : ℂ) :
    z ∈ spectrum ℂ M ↔ M.charpoly.IsRoot z := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  change (Matrix.scalar ι z - M).det = 0 ↔ M.charpoly.IsRoot z
  simp only [Polynomial.IsRoot, Matrix.charpoly, Matrix.eval_det,
    Matrix.matPolyEquiv_charmatrix, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]

/-- The list being summed is a multiset, including all algebraic repetitions. -/
theorem trace_eq_root_multiset_sum (M : Matrix ι ι ℂ) :
    Matrix.trace M = M.charpoly.roots.sum :=
  Matrix.trace_eq_sum_roots_charpoly M

/-- Roots of the characteristic polynomial of a positive power come from
spectral values of the ORIGINAL matrix. This makes no statement that the
spectrum set records their multiplicities: those remain in `roots`. -/
theorem powered_charpoly_root_origin (M : Matrix ι ι ℂ) (ell : ℕ)
    (hell : 0 < ell) {w : ℂ} (hw : w ∈ (M ^ ell).charpoly.roots) :
    ∃ z ∈ spectrum ℂ M, z ^ ell = w := by
  have hs : w ∈ spectrum ℂ (M ^ ell) :=
    (mem_matrix_spectrum_iff_charpoly_root (M ^ ell) w).2
      (Polynomial.isRoot_of_mem_roots hw)
  rw [spectrum.map_pow_of_pos M hell] at hs
  exact hs

/-- A distinguished spectral value survives as a root of every matrix power.
In particular its algebraic multiplicity is at least one. -/
theorem powered_spectral_value_mem_roots (M : Matrix ι ι ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ M) (ell : ℕ) :
    z ^ ell ∈ (M ^ ell).charpoly.roots := by
  apply (Polynomial.mem_roots ((Matrix.charpoly_monic (M ^ ell)).ne_zero)).2
  apply (mem_matrix_spectrum_iff_charpoly_root (M ^ ell) _).1
  exact spectrum.pow_image_subset M ell ⟨z, hz, rfl⟩

/-- The algebraic root list has at most the actual matrix dimension.
For complex matrices equality also holds; only this inequality is needed. -/
theorem powered_roots_card_le (M : Matrix ι ι ℂ) (ell : ℕ) :
    (M ^ ell).charpoly.roots.card ≤ Fintype.card ι := by
  simpa only [Matrix.charpoly_natDegree_eq_dim] using
    Polynomial.card_roots' (M ^ ell).charpoly

end Matrices

private theorem multiset_re_sum_lower (s : Multiset ℂ) (a : ℝ)
    (h : ∀ z ∈ s, a ≤ z.re) : (s.card : ℝ) * a ≤ s.sum.re := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      have hz := h z (by simp)
      have hs := ih (fun w hw => h w (by simp [hw]))
      simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one,
        Multiset.sum_cons, Complex.add_re]
      nlinarith

/-- One distinguished occurrence is kept separately; all remaining algebraic
occurrences, not only the distinct roots, are charged individually. -/
private theorem multiset_re_sum_lower_of_mem (s : Multiset ℂ) (z : ℂ)
    (hz : z ∈ s) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ w ∈ s, -a ≤ w.re) :
    z.re - (s.card : ℝ) * a ≤ s.sum.re := by
  classical
  have hs : ∀ w ∈ s.erase z, -a ≤ w.re :=
    fun w hw => h w (Multiset.mem_of_mem_erase hw)
  have hb := multiset_re_sum_lower (s.erase z) (-a) hs
  have hc : (s.erase z).card ≤ s.card := Multiset.card_le_card (Multiset.erase_le _ _)
  have hc' : ((s.erase z).card : ℝ) ≤ s.card := by exact_mod_cast hc
  have heq : s.sum = z + (s.erase z).sum := by
    conv_lhs => rw [← Multiset.cons_erase hz]
    rw [Multiset.sum_cons]
  rw [heq, Complex.add_re]
  nlinarith

/-- Algebraic multiplicity version of the even-trace inequality. Each root of
`charpoly (M^(2*k))` is pulled back by spectral mapping before its real part is
estimated. No list of original eigenvalues is an input. -/
theorem even_matrix_trace_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (hsmall : ∀ z ∈ spectrum ℂ M, z.im ≠ 0 → Complex.normSq z ≤ 2)
    (z₀ : ℂ) (hz₀ : z₀ ∈ spectrum ℂ M) (hreal : z₀.im = 0)
    (k : ℕ) (hk : 0 < k) :
    z₀.re ^ (2 * k) - (Fintype.card ι : ℝ) * 2 ^ k ≤
      (Matrix.trace (M ^ (2 * k))).re := by
  let roots := (M ^ (2 * k)).charpoly.roots
  have hroot : z₀ ^ (2 * k) ∈ roots := powered_spectral_value_mem_roots M hz₀ _
  have hterm : ∀ w ∈ roots, -(2 : ℝ) ^ k ≤ w.re := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := powered_charpoly_root_origin M (2 * k) (by omega) hw
    by_cases hr : z.im = 0
    · exact (neg_nonpos.2 (by positivity)).trans (even_power_re_nonneg_of_real hr k)
    · exact even_power_re_ge_neg (hsmall z hz hr) k
  have hsum := multiset_re_sum_lower_of_mem roots (z₀ ^ (2 * k)) hroot
    ((2 : ℝ) ^ k) (by positivity) hterm
  have hc : (roots.card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast powered_roots_card_le M (2 * k)
  have hzre : (z₀ ^ (2 * k)).re = z₀.re ^ (2 * k) := by
    have hz : z₀ = (z₀.re : ℂ) := by apply Complex.ext <;> simp [hreal]
    rw [hz, ← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  rw [hzre] at hsum
  rw [trace_eq_root_multiset_sum]
  change _ ≤ roots.sum.re
  nlinarith [mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ (2 : ℝ) ^ k)]

section Physical
variable (G : PhysicalGraph)

/-- The matrix-to-linear-endomorphism equivalence is applied to the standard
basis of the actual dart space. -/
def matrixEndEquiv : Matrix (Dart G) (Dart G) ℂ ≃ₐ[ℂ]
    ((Dart G → ℂ) →ₗ[ℂ] (Dart G → ℂ)) :=
  Matrix.toLinAlgEquiv'

@[simp] theorem matrixEndEquiv_apply_actual :
    matrixEndEquiv G (matrix G : Matrix _ _ ℂ) = (operatorCLM G).toLinearMap := by
  ext f d
  rfl

/-- Matrix and continuous-operator spectral laws agree for the actual matrix. -/
theorem actual_matrix_spectrum_eq :
    spectrum ℂ (matrix G : Matrix _ _ ℂ) = spectrum ℂ (operatorCLM G) := by
  have hm := AlgEquiv.spectrum_eq (matrixEndEquiv G) (matrix G : Matrix _ _ ℂ)
  have hc := AlgEquiv.spectrum_eq (linearEndEquiv G) (operatorCLM G)
  rw [matrixEndEquiv_apply_actual] at hm
  exact hm.symm.trans hc

/-- The earlier physical nonreal-eigenvector estimate applies to every
algebraic spectral value used by the characteristic-root trace argument. -/
theorem actual_spectrum_nonreal_bound (hmax : ∀ v, G.degree v ≤ 3)
    (z : ℂ) (hz : z ∈ spectrum ℂ (matrix G : Matrix _ _ ℂ))
    (him : z.im ≠ 0) : Complex.normSq z ≤ 2 := by
  rw [actual_matrix_spectrum_eq] at hz
  obtain ⟨f, hf⟩ := exists_eigenvector_of_mem_operator_spectrum G z hz
  exact nonreal_nonbacktracking_normSq_le_two G hmax hf him

/-- An actual physical eigenvector gives actual matrix spectral membership. -/
theorem physical_eigenvector_mem_matrix_spectrum {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) : z ∈ spectrum ℂ (matrix G : Matrix _ _ ℂ) := by
  have hv : Module.End.HasEigenvector ((operatorCLM G).toLinearMap) z f := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, hf.1⟩
    funext d
    change (operatorCLM G f) d = z * f d
    rw [operatorCLM_apply_step]
    exact hf.2 d
  have hs := (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  have heq := AlgEquiv.spectrum_eq (matrixEndEquiv G) (matrix G : Matrix _ _ ℂ)
  rw [matrixEndEquiv_apply_actual] at heq
  rwa [heq] at hs

/-- Source trace estimate prior to normalizing, in the high-entropy case.
The entropy witness may be a negative real number; even powers suffice. -/
theorem actual_even_trace_lower_high_entropy
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount) (hb : 2 * degreeTwoCount G < G.vertexCount)
    (k : ℕ) (hk : 0 < k) :
    ((2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)) ^ (2 * k) -
      2 * (G.edgeCount : ℝ) * 2 ^ k ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) := by
  obtain ⟨z, f, hf, hzreal, hz⟩ := exists_real_degreeTwo_eigenvector G hmin hmax hn hb
  have ht := even_matrix_trace_lower (matrix G : Matrix _ _ ℂ)
    (actual_spectrum_nonreal_bound G hmax) z
    (physical_eigenvector_mem_matrix_spectrum G hf) hzreal k hk
  have heq : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzreal]
  have hnorm : ‖z‖ ^ (2 * k) = z.re ^ (2 * k) := by
    rw [heq, Complex.norm_real, Real.norm_eq_abs, ← abs_pow]
    exact abs_of_nonneg (by rw [Nat.mul_comm 2 k, pow_mul]; exact sq_nonneg _)
  have hpow : ((2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount)) ^ (2 * k) ≤
      z.re ^ (2 * k) := by
    rw [← hnorm]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hz _
  rw [card_dart, Nat.cast_mul, Nat.cast_ofNat, complex_trace_pow_re] at ht
  linarith

end Physical
end Erdos1016.Nonbacktracking
