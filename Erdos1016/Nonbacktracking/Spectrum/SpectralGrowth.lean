import Erdos1016.Nonbacktracking.Entropy.EntropyGrowth
import Mathlib.Analysis.Normed.Algebra.Spectrum

set_option autoImplicit false

/-!
# Entropy implies spectral-radius growth

We realize the *actual* dart matrix as an operator on the finite complex
sup-norm space. The sum of all physical walk counts bounds its norm below.
Gelfand's formula then proves the source entropy/spectral-radius inequality.

No positive eigenvector, Perron eigenvalue, matrix mixing property, or
spectral growth estimate is assumed. Reducible and periodic graphs are
permitted. The subsequent algebraic-multiplicity trace step remains separate.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open Filter
open scoped BigOperators Topology
local instance spectralGrowthDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : PhysicalGraph)

/-- The operator norm is the standard norm on continuous endomorphisms of
`Dart G → ℂ`. This avoids making a global choice of norm on matrices. -/
def operatorCLM : (Dart G → ℂ) →L[ℂ] (Dart G → ℂ) :=
  ContinuousLinearMap.mk (Matrix.mulVecLin (matrix G : Matrix _ _ ℂ))

@[simp] theorem operatorCLM_apply (f : Dart G → ℂ) :
    operatorCLM G f = (matrix G : Matrix _ _ ℂ).mulVec f := rfl

theorem operatorCLM_apply_step (f : Dart G → ℂ) :
    operatorCLM G f = step G f := matrix_mulVec G f

/-- Powers act on the same labelled physical darts as `Run`. -/
theorem operatorCLM_pow_apply (k : ℕ) (f : Dart G → ℂ) :
    (operatorCLM G ^ k) f = ((matrix G : Matrix _ _ ℂ) ^ k).mulVec f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, operatorCLM_apply,
        Matrix.mulVec_mulVec, ← pow_succ']

theorem operatorCLM_pow_one (k : ℕ) (d : Dart G) :
    ((operatorCLM G ^ k) (fun _ => 1)) d =
      (∑ e : Dart G, Fintype.card (Run G k d e) : ℕ) := by
  rw [operatorCLM_pow_apply]
  simp only [Matrix.mulVec, dotProduct, mul_one, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact (card_run_cast (K := ℂ) G k d e).symm

/-- A pointwise nonnegative row count is bounded by the actual operator norm. -/
theorem row_count_le_operator_norm (hm : 0 < G.edgeCount) (k : ℕ) (d : Dart G) :
    ((∑ e : Dart G, Fintype.card (Run G k d e) : ℕ) : ℝ) ≤
      ‖operatorCLM G ^ k‖ := by
  letI : Nonempty (Dart G) := dart_nonempty_of_edgeCount_pos G hm
  have hconst : ‖(fun _ : Dart G => (1 : ℂ))‖ = 1 := by
    change ‖(1 : Dart G → ℂ)‖ = 1
    exact norm_one
  calc
    _ = ‖((operatorCLM G ^ k) (fun _ => 1)) d‖ := by
      rw [operatorCLM_pow_one, Complex.norm_natCast]
    _ ≤ ‖(operatorCLM G ^ k) (fun _ => 1)‖ := norm_le_pi_norm _ d
    _ ≤ ‖operatorCLM G ^ k‖ * ‖(fun _ : Dart G => (1 : ℂ))‖ :=
      (operatorCLM G ^ k).le_opNorm _
    _ = ‖operatorCLM G ^ k‖ := by rw [hconst, mul_one]

theorem allRunCount_le_card_mul_operator_norm (hm : 0 < G.edgeCount) (k : ℕ) :
    (allRunCount G k : ℝ) ≤ (2 * (G.edgeCount : ℝ)) * ‖operatorCLM G ^ k‖ := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun d _ => row_count_le_operator_norm G hm k d)
  simpa only [allRunCount, Nat.cast_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, card_dart, Nat.cast_mul, Nat.cast_ofNat] using hs

/-- Exponential entropy lower bound on every power of the actual operator. -/
theorem entropy_pow_le_operator_norm
    (hmin : ∀ v, 2 ≤ G.degree v) (hm : 0 < G.edgeCount) (k : ℕ) :
    ((2 : ℝ) ^ meanLogBranching G) ^ k ≤ ‖operatorCLM G ^ k‖ := by
  have hm' : (0 : ℝ) < 2 * G.edgeCount := by exact_mod_cast (by omega : 0 < 2 * G.edgeCount)
  have hl := allRunCount_entropy_lower G hmin hm k
  have hu := allRunCount_le_card_mul_operator_norm G hm k
  have hpow : (2 : ℝ) ^ ((k : ℝ) * meanLogBranching G) =
      ((2 : ℝ) ^ meanLogBranching G) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hpow] at hl
  exact (mul_le_mul_left hm').mp (hl.trans hu)

/-- The entropy lower bound on the spectral radius, using Gelfand's formula.
This is an unconditional graph theorem under the displayed degree/nonempty
hypotheses; it has no supplied spectral or walk-growth certificate. -/
theorem entropy_le_spectralRadius
    (hmin : ∀ v, 2 ≤ G.degree v) (hm : 0 < G.edgeCount) :
    ENNReal.ofReal ((2 : ℝ) ^ meanLogBranching G) ≤
      spectralRadius ℂ (operatorCLM G) := by
  let q : ℝ := (2 : ℝ) ^ meanLogBranching G
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hk (k : ℕ) (hk : 0 < k) : q ≤ ‖operatorCLM G ^ k‖ ^ (1 / (k : ℝ)) := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h := Real.rpow_le_rpow (pow_nonneg hq.le k)
      (entropy_pow_le_operator_norm G hmin hm k) (le_of_lt (div_pos zero_lt_one hk'))
    have heq : (q ^ k) ^ (1 / (k : ℝ)) = q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      simp [hk'.ne']
    rw [heq] at h
    exact h
  have hlim := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (operatorCLM G)
  have hevent : ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal q ≤ ENNReal.ofReal (‖operatorCLM G ^ k‖ ^ (1 / (k : ℝ))) := by
    filter_upwards [eventually_ge_atTop 1] with k hk₁
    exact ENNReal.ofReal_le_ofReal (hk k (by omega))
  exact isClosed_Ici.mem_of_tendsto hlim hevent



end Erdos1016.Nonbacktracking
