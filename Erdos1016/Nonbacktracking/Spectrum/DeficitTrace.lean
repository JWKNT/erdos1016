import Erdos1016.Nonbacktracking.Spectrum.DeficitSpectralBound
import Erdos1016.Nonbacktracking.Spectrum.EvenSpectrum
import Erdos1016.Nonbacktracking.Trace.WalkTrace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

set_option autoImplicit false

/-! Even trace bounds from the full cubic deficit, independent of the old
 minimum-degree-two entropy chain. Algebraic multiplicities are retained. -/

noncomputable section
namespace Erdos1016.Nonbacktracking.DeficitTrace
open scoped BigOperators
local instance deficitTraceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

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


/-- Spectral values of the actual dart matrix have actual dart eigenvectors. -/
theorem exists_eigenvector_of_matrix_spectrum (G : PhysicalGraph) (z : ℂ)
    (hz : z ∈ spectrum ℂ (matrix G : Matrix _ _ ℂ)) :
    ∃ f : Dart G → ℂ, IsEigenvector G z f := by
  let e : Matrix (Dart G) (Dart G) ℂ ≃ₐ[ℂ]
      ((Dart G → ℂ) →ₗ[ℂ] (Dart G → ℂ)) := Matrix.toLinAlgEquiv'
  have heq := AlgEquiv.spectrum_eq e (matrix G : Matrix _ _ ℂ)
  have hz' : z ∈ spectrum ℂ (e (matrix G : Matrix _ _ ℂ)) := by rwa [heq]
  obtain ⟨f, hf⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz').exists_hasEigenvector
  refine ⟨f, hf.2, ?_⟩
  intro d
  have hd := congrFun hf.apply_eq_smul d
  change (matrix G : Matrix _ _ ℂ).mulVec f d = z * f d at hd
  rwa [matrix_mulVec] at hd

theorem eigenvector_mem_matrix_spectrum (G : PhysicalGraph) {z : ℂ}
    {f : Dart G → ℂ} (hf : IsEigenvector G z f) :
    z ∈ spectrum ℂ (matrix G : Matrix _ _ ℂ) := by
  let e : Matrix (Dart G) (Dart G) ℂ ≃ₐ[ℂ]
      ((Dart G → ℂ) →ₗ[ℂ] (Dart G → ℂ)) := Matrix.toLinAlgEquiv'
  have hv : Module.End.HasEigenvector (e (matrix G : Matrix _ _ ℂ)) z f := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hf.1⟩
    funext d
    change (matrix G : Matrix _ _ ℂ).mulVec f d = z * f d
    rw [matrix_mulVec]
    exact hf.2 d
  have hz := (Module.End.hasEigenvalue_of_hasEigenvector hv).mem_spectrum
  rwa [AlgEquiv.spectrum_eq e (matrix G : Matrix _ _ ℂ)] at hz

/-- The unnormalized even trace lower bound, with the actual full degree
 deficit in the leading eigenvalue. -/
theorem actual_even_trace_lower (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount) (k : ℕ) (hk : 0 < k) :
    (2 - degreeDeficit G / G.vertexCount) ^ (2 * k) -
      2 * (G.edgeCount : ℝ) * 2 ^ k ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) := by
  obtain ⟨t, ht, ht2, ht1, f, hf⟩ :=
    exists_real_eigenvector_ge_two_sub_deficit G hmax hn hd
  have hsmall : ∀ z ∈ spectrum ℂ (matrix G : Matrix _ _ ℂ),
      z.im ≠ 0 → Complex.normSq z ≤ 2 := by
    intro z hz him
    obtain ⟨u, hu⟩ := exists_eigenvector_of_matrix_spectrum G z hz
    exact nonreal_nonbacktracking_normSq_le_two G hmax hu him
  have htrace := even_matrix_trace_lower (matrix G : Matrix _ _ ℂ) hsmall
    (t : ℂ) (eigenvector_mem_matrix_spectrum G hf) (by simp) k hk
  rw [card_dart, Nat.cast_mul, Nat.cast_ofNat, complex_trace_pow_re,
    Complex.ofReal_re] at htrace
  have hnR : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hlower : 0 ≤ 2 - degreeDeficit G / G.vertexCount := by
    have hdiv := (div_lt_one hnR).mpr hd
    linarith
  have hpow := pow_le_pow_left₀ hlower ht (2 * k)
  linarith

/-- The exact form used in the shorter proof, for every positive even
 length, including graphs with leaves or isolated vertices. -/
theorem normalized_even_trace_lower (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount) (k : ℕ) (hk : 0 < k) :
    (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) -
      3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ k ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) /
        (2 : ℝ) ^ (2 * k) := by
  have hmain := actual_even_trace_lower G hmax hn hd k hk
  have hdiv := div_le_div_of_nonneg_right hmain
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k))
  have hlead : (2 - degreeDeficit G / G.vertexCount) ^ (2 * k) /
      (2 : ℝ) ^ (2 * k) =
      (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) := by
    rw [← div_pow]
    congr 1
    ring
  have herr : 2 * (G.edgeCount : ℝ) * (2 : ℝ) ^ k / (2 : ℝ) ^ (2 * k) =
      2 * (G.edgeCount : ℝ) / (2 : ℝ) ^ k := by
    rw [two_mul k, pow_add]
    field_simp
    ring
  rw [sub_div, hlead, herr] at hdiv
  have hcounts : 2 * (G.edgeCount : ℝ) ≤ 3 * G.vertexCount := by
    have h := degreeDeficit_nonneg G hmax
    rw [degreeDeficit_eq_counts] at h
    linarith
  have herrle := div_le_div_of_nonneg_right hcounts
    (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
  linarith

end Erdos1016.Nonbacktracking.DeficitTrace
