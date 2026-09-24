import Erdos1016.Nonbacktracking.Spectrum.SpectralGrowth
import Erdos1016.Nonbacktracking.Spectrum.NonrealSpectrum

set_option autoImplicit false

/-!
# An actual eigenvector witnessing entropy-scale spectral growth

Gelfand's formula gives a bound on the spectral radius. Compactness of the
spectrum supplies a scalar attaining it, and finite-dimensional algebra
identifies that scalar with an eigenvalue of the *actual* dart operator.

This does not invoke a Perron theorem or claim that the chosen scalar is
positive real. Realness follows when its squared entropy lower bound exceeds
2. That distinction matters when later taking even powers.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped Topology
local instance spectralWitnessDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- Forgetting continuity is an algebra equivalence in this finite-dimensional
space. The inverse is not an arbitrary algebra homomorphism. -/
def linearEndEquiv :
    ((Dart G → ℂ) →L[ℂ] (Dart G → ℂ)) ≃ₐ[ℂ]
      ((Dart G → ℂ) →ₗ[ℂ] (Dart G → ℂ)) where
  toFun f := f.toLinearMap
  invFun f := f.toContinuousLinearMap
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_mul' f g := by ext x; rfl
  map_add' f g := by ext x; rfl
  commutes' z := by ext x; rfl

/-- Spectral membership really supplies the labelled edge eigenvector used in
the quadratic proof, not a separate abstract list of scalars. -/
theorem exists_eigenvector_of_mem_operator_spectrum (z : ℂ)
    (hz : z ∈ spectrum ℂ (operatorCLM G)) :
    ∃ f : Dart G → ℂ, IsEigenvector G z f := by
  have heq : spectrum ℂ ((operatorCLM G).toLinearMap) =
      spectrum ℂ (operatorCLM G) :=
    AlgEquiv.spectrum_eq (linearEndEquiv G) (operatorCLM G)
  have hlin : z ∈ spectrum ℂ ((operatorCLM G).toLinearMap) := by
    rwa [heq]
  have heig : Module.End.HasEigenvalue ((operatorCLM G).toLinearMap) z :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hlin
  obtain ⟨f, hf⟩ := heig.exists_hasEigenvector
  refine ⟨f, hf.2, ?_⟩
  intro d
  have hd := congrFun hf.apply_eq_smul d
  change (operatorCLM G f) d = z * f d at hd
  rwa [operatorCLM_apply_step] at hd

/-- Existence of an entropy-scale eigenvalue and its physical eigenvector,
including reducible or periodic nonbacktracking matrices. -/
theorem exists_entropy_eigenvector
    (hmin : ∀ v, 2 ≤ G.degree v) (hm : 0 < G.edgeCount) :
    ∃ (z : ℂ) (f : Dart G → ℂ),
      IsEigenvector G z f ∧ (2 : ℝ) ^ meanLogBranching G ≤ ‖z‖ ∧
      (‖z‖₊ : ENNReal) = spectralRadius ℂ (operatorCLM G) := by
  letI : Nonempty (Dart G) := dart_nonempty_of_edgeCount_pos G hm
  obtain ⟨z, hz, hrad⟩ := spectrum.exists_nnnorm_eq_spectralRadius (operatorCLM G)
  obtain ⟨f, hf⟩ := exists_eigenvector_of_mem_operator_spectrum G z hz
  have hb := entropy_le_spectralRadius G hmin hm
  rw [← hrad] at hb
  have hq : 0 ≤ (2 : ℝ) ^ meanLogBranching G := Real.rpow_nonneg (by norm_num) _
  have hreal := ENNReal.toReal_mono (by simp : (‖z‖₊ : ENNReal) ≠ ⊤) hb
  have hnorm : (2 : ℝ) ^ meanLogBranching G ≤ ‖z‖ := by
    simpa [ENNReal.toReal_ofReal hq] using hreal
  exact ⟨z, f, hf, hnorm, hrad⟩

/-- Once the entropy radius exceeds sqrt(2), a maximizing spectral witness
must be real by the already written graph-specific nonreal bound. -/
theorem exists_real_entropy_eigenvector
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hm : 0 < G.edgeCount)
    (hlarge : 2 < ((2 : ℝ) ^ meanLogBranching G) ^ 2) :
    ∃ (z : ℂ) (f : Dart G → ℂ), IsEigenvector G z f ∧
      z.im = 0 ∧ (2 : ℝ) ^ meanLogBranching G ≤ ‖z‖ := by
  obtain ⟨z, f, hf, hb, _⟩ := exists_entropy_eigenvector G hmin hm
  refine ⟨z, f, hf, ?_, hb⟩
  by_contra hz
  have hnorm := nonreal_nonbacktracking_normSq_le_two G hmax hf hz
  have hs : ‖z‖ ^ 2 = Complex.normSq z := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]
  have hq : 0 ≤ (2 : ℝ) ^ meanLogBranching G := Real.rpow_nonneg (by norm_num) _
  have hsq : ((2 : ℝ) ^ meanLogBranching G) ^ 2 ≤ ‖z‖ ^ 2 := by
    gcongr
  nlinarith

/-- A concrete graph defect bound suffices for the real spectral witness.
No positivity of the real eigenvalue is asserted or needed for even powers. -/
theorem exists_real_degreeTwo_eigenvector
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (hn : 0 < G.vertexCount)
    (hb : 2 * degreeTwoCount G < G.vertexCount) :
    ∃ (z : ℂ) (f : Dart G → ℂ), IsEigenvector G z f ∧ z.im = 0 ∧
      (2 : ℝ) ^ (1 - (degreeTwoCount G : ℝ) / G.vertexCount) ≤ ‖z‖ := by
  have hn' : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hb' : 2 * (degreeTwoCount G : ℝ) < G.vertexCount := by exact_mod_cast hb
  have hf : (degreeTwoCount G : ℝ) / G.vertexCount < 1 / 2 := by
    apply (div_lt_iff₀ hn').mpr
    nlinarith
  have hH := meanLogBranching_lower G hmin hmax hn
  have hhalf : (1 / 2 : ℝ) < meanLogBranching G := by linarith
  have hpow : ((2 : ℝ) ^ meanLogBranching G) ^ 2 =
      (2 : ℝ) ^ (2 * meanLogBranching G) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hlarge : 2 < ((2 : ℝ) ^ meanLogBranching G) ^ 2 := by
    rw [hpow]
    calc
      2 = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ < (2 : ℝ) ^ (2 * meanLogBranching G) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨z, f, heig, hzreal, hz⟩ := exists_real_entropy_eigenvector G hmin hmax
    (edgeCount_pos_of_min_two G hmin hn) hlarge
  refine ⟨z, f, heig, hzreal, le_trans ?_ hz⟩
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hH

end Erdos1016.Nonbacktracking
