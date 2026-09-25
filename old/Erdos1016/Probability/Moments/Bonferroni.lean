import Erdos1016.Probability.Moments.SecondMoments
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

private theorem alternating_partial_choose (n K : ℕ) (hK : K < n) :
    (∑ j ∈ Finset.range (K + 1),
      ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ))) =
        (-1 : ℤ) ^ K * (Nat.choose (n - 1) K : ℤ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hKn : K < n := by omega
      have hsum :
          (∑ j ∈ Finset.range (K + 2),
            ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ))) =
            (∑ j ∈ Finset.range (K + 1),
              ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ))) +
              ((-1 : ℤ) ^ (K + 1) * (Nat.choose n (K + 1) : ℤ)) := by
        simpa [Nat.add_assoc] using
          (Finset.sum_range_succ
            (fun j : ℕ => ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ))) (K + 1))
      have hchoose : Nat.choose n (K + 1) =
          Nat.choose (n - 1) K + Nat.choose (n - 1) (K + 1) := by
        have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        calc
          Nat.choose n (K + 1) = Nat.choose (n - 1 + 1) (K + 1) := by rw [hn1]
          _ = Nat.choose (n - 1) K + Nat.choose (n - 1) (K + 1) :=
            Nat.choose_succ_succ' (n - 1) K
      rw [hsum, ih hKn, hchoose, pow_succ]
      push_cast
      ring

/-- The even-order pointwise Bonferroni inequality for a finite event count.
No independence or probability model is required for this combinatorial step. -/
theorem alternating_choose_bonferroni (K n : ℕ) (hK : Even K) :
    (if n = 0 then (1 : ℝ) else 0) ≤
      ∑ j ∈ Finset.range (K + 1),
        ((-1 : ℝ) ^ j * (Nat.choose n j : ℝ)) := by
  have hInt : (if n = 0 then (1 : ℤ) else 0) ≤
      ∑ j ∈ Finset.range (K + 1),
        ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ)) := by
    by_cases hn : n = 0
    · subst n
      have hsum : (∑ j ∈ Finset.range (K + 1),
          ((-1 : ℤ) ^ j * (Nat.choose 0 j : ℤ))) = 1 := by
        apply Finset.sum_eq_single 0
        · intro j hj hne
          have hjpos : 0 < j := Nat.pos_of_ne_zero hne
          simp [Nat.choose_eq_zero_of_lt hjpos]
        · simp
      rw [hsum]
      norm_num
    · by_cases hKn : K < n
      · rw [alternating_partial_choose n K hKn]
        rw [if_neg hn]
        rw [hK.neg_one_pow]
        positivity
      · have hsub : Finset.range (n + 1) ⊆ Finset.range (K + 1) := by
          intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega
        have hextra : ∀ j ∈ Finset.range (K + 1),
            j ∉ Finset.range (n + 1) →
              ((-1 : ℤ) ^ j * (Nat.choose n j : ℤ)) = 0 := by
          intro j hj hjnot
          have hjlt : j < K + 1 := Finset.mem_range.mp hj
          have hjge : ¬ j < n + 1 := by
            intro h
            exact hjnot (Finset.mem_range.mpr h)
          have hjn : n < j := by omega
          rw [Nat.choose_eq_zero_of_lt hjn]
          exact mul_zero _
        have heq := Finset.sum_subset hsub hextra
        rw [Int.alternating_sum_range_choose_of_ne hn] at heq
        rw [if_neg hn]
        rw [← heq]
  exact_mod_cast hInt

private theorem iteratedDerivWithin_exp_neg (s : Set ℝ)
    (hs : UniqueDiffOn ℝ s) (x : ℝ) (hx : x ∈ s) (n : ℕ) :
    iteratedDerivWithin n (fun y : ℝ => Real.exp (-y)) s x =
      (-1 : ℝ) ^ n * Real.exp (-x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      have hdiffExp : DifferentiableWithinAt ℝ
          (fun y : ℝ => Real.exp (-y)) s x := by
        fun_prop
      have hcongr :
          derivWithin (iteratedDerivWithin n (fun y : ℝ => Real.exp (-y)) s) s x =
            derivWithin (fun y : ℝ => (-1 : ℝ) ^ n * Real.exp (-y)) s x := by
        apply derivWithin_congr
        · intro y hy
          exact ih y hy
        · exact ih x hx
      rw [hcongr, derivWithin_const_mul _ hdiffExp]
      have hdiff : DifferentiableWithinAt ℝ (fun y : ℝ => -y) s x := by
        fun_prop
      rw [derivWithin_exp hdiff (hs x hx)]
      have hneg : derivWithin (fun y : ℝ => -y) s x = -1 := by
        simp [derivWithin_neg (𝕜 := ℝ) (s := s) (x := x) (hs x hx)]
      rw [hneg]
      ring

/-- Finite Taylor remainder bound for the real exponential. This follows from
Mathlib's Lagrange form of Taylor's theorem; in particular, it holds at every
order (evenness is needed only by Bonferroni). -/
theorem finite_alternating_exp_taylor_remainder
    (lambdaVar : ℝ) (K : ℕ) (hlambda : 0 ≤ lambdaVar) :
    (∑ j ∈ Finset.range (K + 1),
      ((-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ))) ≤
        Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
          ((K + 1).factorial : ℝ) := by
  by_cases hzero : lambdaVar = 0
  · subst lambdaVar
    have hsum : (∑ j ∈ Finset.range (K + 1),
        ((-1 : ℝ) ^ j * (0 : ℝ) ^ j / (j.factorial : ℝ))) = 1 := by
      induction K with
      | zero => simp
      | succ K ih =>
          rw [show K + 2 = (K + 1) + 1 by omega,
            Finset.sum_range_succ, ih]
          simp
    simp [hsum]
  have hpos : 0 < lambdaVar := lt_of_le_of_ne hlambda (Ne.symm hzero)
  let s : Set ℝ := Set.Icc 0 lambdaVar
  let f : ℝ → ℝ := fun y => Real.exp (-y)
  have hs : UniqueDiffOn ℝ s := by
    simpa [s] using uniqueDiffOn_Icc hpos
  have hf : ContDiffOn ℝ (K + 1) f s := by
    dsimp [f, s]
    fun_prop
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin K f s) (Set.Ioo 0 lambdaVar) := by
    have h' : DifferentiableOn ℝ (iteratedDerivWithin K f s) s :=
      hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self K) hs
    apply h'.mono
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hfK : ContDiffOn ℝ K f s := hf.of_le (by exact_mod_cast Nat.le_succ K)
  have hlag := taylor_mean_remainder_lagrange (n := K) hpos hfK hf'
  obtain ⟨y, hy, hrem⟩ := hlag
  have hyIcc : y ∈ s := by
    rw [Set.mem_Ioo] at hy
    exact Set.mem_Icc.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hderiv : iteratedDerivWithin (K + 1) f s y =
      (-1 : ℝ) ^ (K + 1) * Real.exp (-y) := by
    exact iteratedDerivWithin_exp_neg s hs y hyIcc (K + 1)
  have hExp : Real.exp (-y) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (le_trans (le_of_lt hy.1) (le_rfl))
  have habsDeriv : |iteratedDerivWithin (K + 1) f s y| ≤ 1 := by
    rw [hderiv]
    have habs : |(-1 : ℝ) ^ (K + 1)| = 1 := by simp
    have habs' : |Real.exp (-y)| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact hExp
    have : |(-1 : ℝ) ^ (K + 1) * Real.exp (-y)| ≤ 1 := by
      rw [abs_mul, habs]
      simpa using habs'
    exact this
  have hderiv_bounds := abs_le.mp habsDeriv
  have hderiv_le : iteratedDerivWithin (K + 1) f s y ≤ 1 := hderiv_bounds.2
  have hderiv_ge : -1 ≤ iteratedDerivWithin (K + 1) f s y := hderiv_bounds.1
  have hpoly : taylorWithinEval f K s 0 lambdaVar =
      ∑ j ∈ Finset.range (K + 1),
        ((-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ)) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, iteratedDerivWithin_exp_neg s hs 0 (by simp [s, hlambda]) j,
      Real.exp_zero, smul_eq_mul]
    ring
  have hfac : (0 : ℝ) < ((K + 1).factorial : ℝ) := by positivity
  have hpow : 0 ≤ lambdaVar ^ (K + 1) := by positivity
  change Real.exp (-lambdaVar) - taylorWithinEval f K s 0 lambdaVar =
    iteratedDerivWithin (K + 1) f s y * (lambdaVar - 0) ^ (K + 1) /
      ((K + 1).factorial : ℝ) at hrem
  rw [hpoly, sub_zero] at hrem
  have hrem_le :
      iteratedDerivWithin (K + 1) f s y *
        lambdaVar ^ (K + 1) / ((K + 1).factorial : ℝ) ≤
        lambdaVar ^ (K + 1) / ((K + 1).factorial : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hderiv_le
      (div_nonneg hpow (le_of_lt hfac))
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hrem_ge :
      -(lambdaVar ^ (K + 1) / ((K + 1).factorial : ℝ)) ≤
        iteratedDerivWithin (K + 1) f s y *
          lambdaVar ^ (K + 1) / ((K + 1).factorial : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hderiv_ge
      (div_nonneg hpow (le_of_lt hfac))
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  linarith

/-- The number of events from a finite family that hold at a state. -/
noncomputable def finiteEventCount {Ω ι : Type*} [Fintype Ω] (s : Finset ι)
    (P : ι → Ω → Prop) (ω : Ω) : ℕ := by
  classical
  exact (s.filter fun i => P i ω).card

/-- The normalized factorial moment `E[choose(Z,j)]` of the finite event count. -/
noncomputable def finiteFactorialMoment {Ω ι : Type*} [Fintype Ω]
    (s : Finset ι) (P : ι → Ω → Prop) (j : ℕ) : ℝ :=
  Erdos1016.BoundaryDecay.average
    (fun ω => (Nat.choose (finiteEventCount s P ω) j : ℝ))


/-- Averaging the pointwise even-order Bonferroni inequality gives the finite
event avoidance bound in terms of factorial moments. This makes no independence
assumptions; all probability is the uniform average over the stated finite
state space. -/
theorem finite_avoidance_le_alternating_factorial_moments
    {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (P : ι → Ω → Prop)
    (K : ℕ) (hK : Even K) :
    Finite.density (fun ω => finiteEventCount s P ω = 0) ≤
      ∑ j ∈ Finset.range (K + 1),
        ((-1 : ℝ) ^ j * finiteFactorialMoment s P j) := by
  classical
  have hpoint (ω : Ω) :
      Erdos1016.BoundaryDecay.indicator
          (fun ω => finiteEventCount s P ω = 0) ω ≤
        ∑ j ∈ Finset.range (K + 1),
            ((-1 : ℝ) ^ j *
              (Nat.choose (finiteEventCount s P ω) j : ℝ)) := by
    have hbonf := alternating_choose_bonferroni K
      (finiteEventCount s P ω) hK
    by_cases hz : finiteEventCount s P ω = 0
    · simpa [Erdos1016.BoundaryDecay.indicator, hz] using hbonf
    · simpa [Erdos1016.BoundaryDecay.indicator, hz] using hbonf
  have havg := Erdos1016.BoundaryDecay.average_mono hpoint
  rw [Erdos1016.BoundaryDecay.average_indicator,
    Erdos1016.BoundaryDecay.average_sum] at havg
  simpa [finiteFactorialMoment,
    Erdos1016.BoundaryDecay.average_mul_left] using havg

/-- Moment comparison plus the finite Taylor remainder yields an explicit
upper bound for the probability that none of a finite family of events holds.
The pointwise signed error and Taylor bound are hypotheses so callers can plug
in the precise conditional factorial-moment estimate from their application. -/
theorem finite_avoidance_le_exp_taylor_errors
    {Ω ι : Type*} [Fintype Ω] (s : Finset ι) (P : ι → Ω → Prop)
    (K : ℕ) (hK : Even K) (lambdaVar : ℝ) (hlambda : 0 ≤ lambdaVar)
    (err : ℕ → ℝ)
    (hMoment : ∀ j ∈ Finset.range (K + 1),
      (-1 : ℝ) ^ j * finiteFactorialMoment s P j ≤
        (-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ) + err j) :
    Finite.density (fun ω => finiteEventCount s P ω = 0) ≤
      Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
        ((K + 1).factorial : ℝ) +
          ∑ j ∈ Finset.range (K + 1), err j := by
  have hsum := Finset.sum_le_sum hMoment
  have havoid := finite_avoidance_le_alternating_factorial_moments s P K hK
  have hTaylor := finite_alternating_exp_taylor_remainder lambdaVar K hlambda
  calc
    Finite.density (fun ω => finiteEventCount s P ω = 0) ≤
        ∑ j ∈ Finset.range (K + 1),
          ((-1 : ℝ) ^ j * finiteFactorialMoment s P j) := havoid
    _ ≤ (∑ j ∈ Finset.range (K + 1),
          ((-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ))) +
          ∑ j ∈ Finset.range (K + 1), err j := by
      calc
        _ ≤ ∑ j ∈ Finset.range (K + 1),
            (((-1 : ℝ) ^ j * lambdaVar ^ j / (j.factorial : ℝ)) + err j) := hsum
        _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ Real.exp (-lambdaVar) + lambdaVar ^ (K + 1) /
          ((K + 1).factorial : ℝ) +
            ∑ j ∈ Finset.range (K + 1), err j := by linarith

/-- Every finite initial exponential series is bounded by the full exponential
series on the nonnegative real axis. -/
theorem exp_factorial_partial_sum_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) ≤ Real.exp x := by
  have hsum := (NormedSpace.expSeries_div_summable ℝ x).sum_le_tsum
    (Finset.range n) (by intro k hk; positivity)
  have htsum : (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ]
    exact (congrFun (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ)) x).symm
  rw [htsum] at hsum
  exact hsum

/-- The binomial/factorial cancellation used to normalize the source error
term after setting `j = k + 2`. -/
theorem choose_two_factorial_shift (k : ℕ) :
    (2 : ℝ) * (Nat.choose (k + 2) 2 : ℝ) /
        ((k + 2).factorial : ℝ) = 1 / (k.factorial : ℝ) := by
  have hNat := Nat.choose_mul_factorial_mul_factorial
    (n := k + 2) (k := 2) (by omega)
  have hNat' : Nat.choose (k + 2) 2 * 2 * k.factorial = (k + 2).factorial := by
    simpa [Nat.add_sub_cancel_right] using hNat
  have hReal : (Nat.choose (k + 2) 2 : ℝ) * 2 *
      (k.factorial : ℝ) = ((k + 2).factorial : ℝ) := by
    exact_mod_cast hNat'
  have hden : (0 : ℝ) < ((k + 2).factorial : ℝ) := by positivity
  have hkden : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  field_simp [ne_of_gt hden, ne_of_gt hkden]
  nlinarith [hReal]

/-- The manuscript's raw factorial-moment error bound implies the shifted
termwise hypothesis used in the summation lemma. -/
theorem source_factorial_error_term_bound
    (k : ℕ) (lambdaVar d c : ℝ) (err : ℕ → ℝ)
    (hraw : err (k + 2) ≤
      2 * (Nat.choose (k + 2) 2 : ℝ) * d *
        lambdaVar ^ (k + 1) * Real.exp c) :
    err (k + 2) / ((k + 2).factorial : ℝ) ≤
      d * lambdaVar * (lambdaVar ^ k / (k.factorial : ℝ)) * Real.exp c := by
  have hden : (0 : ℝ) ≤ ((k + 2).factorial : ℝ) := by positivity
  calc
    err (k + 2) / ((k + 2).factorial : ℝ) ≤
        (2 * (Nat.choose (k + 2) 2 : ℝ) * d *
          lambdaVar ^ (k + 1) * Real.exp c) /
            ((k + 2).factorial : ℝ) := div_le_div_of_nonneg_right hraw hden
    _ = ((2 : ℝ) * (Nat.choose (k + 2) 2 : ℝ) /
          ((k + 2).factorial : ℝ)) *
          (d * lambdaVar ^ (k + 1) * Real.exp c) := by ring
    _ = (1 / (k.factorial : ℝ)) *
          (d * lambdaVar ^ (k + 1) * Real.exp c) := by
      rw [choose_two_factorial_shift]
    _ = d * lambdaVar * (lambdaVar ^ k / (k.factorial : ℝ)) * Real.exp c := by
      rw [pow_succ]
      ring

/-- The error-summation step in the finite Bonferroni argument. The input
`hterm` is the termwise result after using
`2 * choose (k+2) 2 / (k+2)! = 1/k!` in the source factorial-moment bound. -/
theorem sum_factorial_moment_errors_le
    (K : ℕ) (lambdaVar d c : ℝ) (hlambda : 0 < lambdaVar)
    (hd : 0 ≤ d) (err : ℕ → ℝ)
    (hterm : ∀ k ∈ Finset.range (K - 1),
      err (k + 2) / ((k + 2).factorial : ℝ) ≤
        d * lambdaVar * (lambdaVar ^ k / (k.factorial : ℝ)) * Real.exp c) :
    (∑ k ∈ Finset.range (K - 1),
      err (k + 2) / ((k + 2).factorial : ℝ)) ≤
        d * lambdaVar * Real.exp (lambdaVar + c) := by
  have hsum :
      (∑ k ∈ Finset.range (K - 1),
        err (k + 2) / ((k + 2).factorial : ℝ)) ≤
        ∑ k ∈ Finset.range (K - 1),
          d * lambdaVar * (lambdaVar ^ k / (k.factorial : ℝ)) * Real.exp c := by
    apply Finset.sum_le_sum
    intro k hk
    exact hterm k hk
  have hseries := exp_factorial_partial_sum_le lambdaVar (le_of_lt hlambda) (K - 1)
  calc
    _ ≤ (∑ k ∈ Finset.range (K - 1),
        d * lambdaVar * (lambdaVar ^ k / (k.factorial : ℝ)) * Real.exp c) := hsum
    _ = d * lambdaVar * Real.exp c *
        (∑ k ∈ Finset.range (K - 1), lambdaVar ^ k / (k.factorial : ℝ)) := by
      calc
        _ = ∑ k ∈ Finset.range (K - 1),
            (d * lambdaVar * Real.exp c) *
              (lambdaVar ^ k / (k.factorial : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ d * lambdaVar * Real.exp c * Real.exp lambdaVar := by
      apply mul_le_mul_of_nonneg_left hseries
      positivity
    _ = d * lambdaVar * Real.exp (lambdaVar + c) := by rw [Real.exp_add]; ring


/-- Summed form of the manuscript's factorial-moment error estimate. The
pointwise input has the exponent at its own order; monotonicity of `choose j 2`
replaces it by the order-`K` exponent before summing. -/
theorem sum_source_factorial_moment_errors_le
    (K : ℕ) (hK : 2 ≤ K) (lambdaVar d : ℝ) (hlambda : 0 < lambdaVar)
    (hd : 0 ≤ d) (err : ℕ → ℝ)
    (hraw : ∀ j ∈ Finset.Icc 2 K,
      err j ≤ 2 * (Nat.choose j 2 : ℝ) * d * lambdaVar ^ (j - 1) *
        Real.exp (((Nat.choose j 2 : ℝ) * d) / lambdaVar)) :
    (∑ k ∈ Finset.range (K - 1),
      err (k + 2) / ((k + 2).factorial : ℝ)) ≤
        d * lambdaVar * Real.exp
          (lambdaVar + ((Nat.choose K 2 : ℝ) * d) / lambdaVar) := by
  let c : ℝ := ((Nat.choose K 2 : ℝ) * d) / lambdaVar
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  apply sum_factorial_moment_errors_le K lambdaVar d c hlambda hd err
  intro k hk
  have hj : k + 2 ∈ Finset.Icc 2 K := by
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hk' := Finset.mem_range.mp hk
      omega
  have hchooseNat : Nat.choose (k + 2) 2 ≤ Nat.choose K 2 := by
    exact Nat.choose_le_choose 2 (Finset.mem_Icc.mp hj).2
  have hchoose : (Nat.choose (k + 2) 2 : ℝ) ≤ (Nat.choose K 2 : ℝ) := by
    exact_mod_cast hchooseNat
  have hexp : Real.exp
      (((Nat.choose (k + 2) 2 : ℝ) * d) / lambdaVar) ≤ Real.exp c := by
    apply Real.exp_le_exp.mpr
    dsimp [c]
    apply div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hchoose hd) (le_of_lt hlambda)
  have hrawj := hraw (k + 2) hj
  have hcoefficient :
      0 ≤ 2 * (Nat.choose (k + 2) 2 : ℝ) * d * lambdaVar ^ ((k + 2) - 1) := by
    positivity
  have hrawj' : err (k + 2) ≤
      2 * (Nat.choose (k + 2) 2 : ℝ) * d * lambdaVar ^ ((k + 2) - 1) * Real.exp c :=
    hrawj.trans (mul_le_mul_of_nonneg_left hexp hcoefficient)
  exact source_factorial_error_term_bound k lambdaVar d c err hrawj'


end Erdos1016.Proof.ConditionalMoments
