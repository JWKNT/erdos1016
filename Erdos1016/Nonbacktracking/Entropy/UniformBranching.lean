import Erdos1016.Nonbacktracking.Entropy.FiniteEntropy

set_option autoImplicit false

/-!
# Stationary entropy lower bounds for finite branching systems

A system consists of actual finite successor sets. At each step a successor is
chosen uniformly. Column stochasticity is the precise finite stationarity
hypothesis; no mixing, irreducibility, or Perron theorem occurs in the proof.

We prove the walk lower bound by propagating the logarithm of the continuation
count. This is a finite Jensen proof of the stationary path-entropy bound and
avoids introducing a measure on dependent path types.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure UniformBranching (ι : Type*) [Fintype ι] [DecidableEq ι] where
  successors : ι → Finset ι
  successors_nonempty : ∀ i, (successors i).Nonempty
  column_sum : ∀ j, ∑ i, (if j ∈ successors i then
    1 / ((successors i).card : ℝ) else 0) = 1

namespace UniformBranching
variable (S : UniformBranching ι)

abbrev degree (i : ι) : ℕ := (S.successors i).card

def kernel (i j : ι) : ℝ :=
  if j ∈ S.successors i then 1 / (S.degree i : ℝ) else 0

theorem degree_pos (i : ι) : 0 < S.degree i :=
  Finset.card_pos.mpr (S.successors_nonempty i)

theorem degree_cast_pos (i : ι) : (0 : ℝ) < S.degree i := by
  exact_mod_cast S.degree_pos i

theorem kernel_nonneg (i j : ι) : 0 ≤ S.kernel i j := by
  unfold kernel
  split_ifs <;> positivity

theorem kernel_row_sum (i : ι) : ∑ j, S.kernel i j = 1 := by
  have hp := S.degree_cast_pos i
  simp [kernel, ← Finset.sum_filter, hp.ne']

theorem kernel_column_sum (j : ι) : ∑ i, S.kernel i j = 1 :=
  S.column_sum j

theorem kernel_average (i : ι) (f : ι → ℝ) :
    (∑ j, S.kernel i j * f j) = (∑ j ∈ S.successors i, f j) / S.degree i := by
  simp only [kernel, ite_mul, zero_mul, one_div, ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  rw [Finset.sum_mul]

/-- `k` transitions, with only the initial state prescribed. -/
def walkCount (S : UniformBranching ι) : ℕ → ι → ℕ
  | 0, _ => 1
  | k + 1, i => ∑ j ∈ S.successors i, walkCount S k j

@[simp] theorem walkCount_zero (i : ι) : S.walkCount 0 i = 1 := rfl

@[simp] theorem walkCount_succ (k : ℕ) (i : ι) :
    S.walkCount (k + 1) i = ∑ j ∈ S.successors i, S.walkCount k j := rfl

theorem walkCount_pos (k : ℕ) (i : ι) : 0 < S.walkCount k i := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      obtain ⟨j, hj⟩ := S.successors_nonempty i
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
        ⟨j, hj, ih j⟩

theorem walkCount_cast_pos (k : ℕ) (i : ι) : (0 : ℝ) < S.walkCount k i := by
  exact_mod_cast S.walkCount_pos k i

def totalWalkCount (k : ℕ) : ℕ := ∑ i, S.walkCount k i

theorem totalWalkCount_pos [Nonempty ι] (k : ℕ) : 0 < S.totalWalkCount k := by
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨i₀, Finset.mem_univ _, S.walkCount_pos k i₀⟩

theorem totalWalkCount_cast_pos [Nonempty ι] (k : ℕ) :
    (0 : ℝ) < S.totalWalkCount k := by
  exact_mod_cast S.totalWalkCount_pos k

def logBranchSum : ℝ := ∑ i, Real.log (S.degree i : ℝ)

def entropyRate : ℝ := S.logBranchSum / Fintype.card ι

/-- One transition pays its actual logarithmic branching factor. -/
theorem logarithmic_step (k : ℕ) (i : ι) :
    Real.log (S.degree i : ℝ) +
      (∑ j, S.kernel i j * Real.log (S.walkCount k j : ℝ)) ≤
      Real.log (S.walkCount (k + 1) i : ℝ) := by
  have hd := S.degree_cast_pos i
  have hw := S.walkCount_cast_pos (k + 1) i
  have h := FiniteEntropy.sum_mul_log_le_log_sum
    (S.kernel i) (fun j => (S.walkCount k j : ℝ))
    (S.kernel_nonneg i) (S.kernel_row_sum i) (S.walkCount_cast_pos k)
  rw [S.kernel_average i (fun j => (S.walkCount k j : ℝ))] at h
  have hc : (∑ j ∈ S.successors i, (S.walkCount k j : ℝ)) =
      (S.walkCount (k + 1) i : ℝ) := by
    simp only [walkCount_succ, Nat.cast_sum]
  rw [hc, Real.log_div hw.ne' hd.ne'] at h
  linarith

/-- The stationary sum of logarithmic continuation counts grows at least
linearly. This is the entropy argument before exponentiation. -/
theorem sum_log_walkCount_lower (k : ℕ) :
    (k : ℝ) * S.logBranchSum ≤ ∑ i, Real.log (S.walkCount k i : ℝ) := by
  induction k with
  | zero => simp [walkCount]
  | succ k ih =>
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => S.logarithmic_step k i)
      rw [Finset.sum_add_distrib,
        FiniteEntropy.sum_transition_average S.kernel S.kernel_column_sum] at h
      have : (∑ i, Real.log (S.degree i : ℝ)) = S.logBranchSum := rfl
      rw [this] at h
      push_cast
      nlinarith

/-- Exact stationary walk-growth bound in logarithmic form. -/
theorem log_totalWalkCount_lower [Nonempty ι] (k : ℕ) :
    Real.log (Fintype.card ι : ℝ) + (k : ℝ) * S.entropyRate ≤
      Real.log (S.totalWalkCount k : ℝ) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : (0 : ℝ) < S.totalWalkCount k := by
    have hp : 0 < S.totalWalkCount k := by
      let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
      exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
        ⟨i₀, Finset.mem_univ _, S.walkCount_pos k i₀⟩
    exact_mod_cast hp
  have hj := FiniteEntropy.average_log_le_log_average
    (fun i => (S.walkCount k i : ℝ)) (S.walkCount_cast_pos k)
  have hc : (∑ i, (S.walkCount k i : ℝ)) = (S.totalWalkCount k : ℝ) := by
    simp [totalWalkCount]
  rw [hc, Real.log_div hw.ne' hn.ne'] at hj
  have hl := div_le_div_of_nonneg_right (S.sum_log_walkCount_lower k) hn.le
  have he : (k : ℝ) * S.logBranchSum / (Fintype.card ι : ℝ) =
      (k : ℝ) * S.entropyRate := by
    simp [entropyRate, mul_div_assoc]
  rw [he] at hl
  linarith

/-- Cardinality of physical walks, not a chosen subfamily or a typical count. -/
theorem totalWalkCount_lower [Nonempty ι] (k : ℕ) :
    (Fintype.card ι : ℝ) * Real.exp ((k : ℝ) * S.entropyRate) ≤
      S.totalWalkCount k := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw := S.totalWalkCount_cast_pos k
  have h := Real.exp_le_exp.mpr (S.log_totalWalkCount_lower k)
  simpa [Real.exp_add, Real.exp_log hn, Real.exp_log hw] using h





end UniformBranching
end Erdos1016.Nonbacktracking
