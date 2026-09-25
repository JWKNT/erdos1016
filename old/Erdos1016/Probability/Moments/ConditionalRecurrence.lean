import Erdos1016.Probability.Moments.CompatibleTupleMoments

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ConditionalMoments

open scoped BigOperators

local instance orderedMomentDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The contribution of a tuple to an ordered moment. Invalid tuples contribute
zero; the joint weight is only used for valid tuples. -/
def validTupleWeight {α : Type*} {n : ℕ} (valid : (Fin n → α) → Prop)
    (joint : (Fin n → α) → ℝ) (u : Fin n → α) : ℝ :=
  if valid u then joint u else 0

/-- A one-cycle extension bound. Distant extensions factor exactly. Each
coordinate contributes at most `d` times the old joint weight to the sum of
nearby extensions. Overlaps among the neighborhoods only improve the bound. -/
theorem tuple_extension_sum_le
    {α : Type*} [Fintype α] {n : ℕ}
    (R : α → α → Prop) (w : α → ℝ)
    (valid : (Fin (n + 1) → α) → Prop)
    (joint : (Fin (n + 1) → α) → ℝ)
    (u : Fin n → α) (p lambdaVar d : ℝ)
    (hp : 0 ≤ p) (hw : ∀ a, 0 ≤ w a)
    (hjoint : ∀ a, valid (Fin.snoc u a) → 0 ≤ joint (Fin.snoc u a))
    (hsum : ∑ a, w a = lambdaVar)
    (hfar : ∀ a, valid (Fin.snoc u a) →
      (∀ i, ¬ R (u i) a) → joint (Fin.snoc u a) = p * w a)
    (hnear : ∀ i : Fin n,
      (∑ a, if valid (Fin.snoc u a) ∧ R (u i) a then
        joint (Fin.snoc u a) else 0) ≤ p * d) :
    (∑ a, validTupleWeight valid joint (Fin.snoc u a)) ≤
      p * (lambdaVar + (n : ℝ) * d) := by
  classical
  have hpoint (a : α) :
      validTupleWeight valid joint (Fin.snoc u a) ≤
        p * w a + ∑ i : Fin n,
          if valid (Fin.snoc u a) ∧ R (u i) a then
            joint (Fin.snoc u a) else 0 := by
    by_cases hv : valid (Fin.snoc u a)
    · by_cases hclose : ∃ i, R (u i) a
      · obtain ⟨i, hi⟩ := hclose
        have hle : joint (Fin.snoc u a) ≤
            ∑ k : Fin n, if valid (Fin.snoc u a) ∧ R (u k) a then
              joint (Fin.snoc u a) else 0 := by
          calc
            _ = (if valid (Fin.snoc u a) ∧ R (u i) a then
                joint (Fin.snoc u a) else 0) := by simp [hv, hi]
            _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
              (f := fun k : Fin n => if valid (Fin.snoc u a) ∧ R (u k) a then
                joint (Fin.snoc u a) else 0)
              (fun k _ => ite_nonneg (hjoint a hv) (le_refl 0))
              (Finset.mem_univ i)
        simpa [validTupleWeight, hv] using
          hle.trans (le_add_of_nonneg_left (mul_nonneg hp (hw a)))
      · have hnone : ∀ i, ¬ R (u i) a := by simpa using hclose
        simp [validTupleWeight, hv, hnone, hfar a hv hnone]
    · simp [validTupleWeight, hv, mul_nonneg hp (hw a)]
  calc
    _ ≤ ∑ a, (p * w a + ∑ i : Fin n,
        if valid (Fin.snoc u a) ∧ R (u i) a then
          joint (Fin.snoc u a) else 0) := Finset.sum_le_sum fun a _ => hpoint a
    _ = p * lambdaVar + ∑ i : Fin n, ∑ a,
        if valid (Fin.snoc u a) ∧ R (u i) a then
          joint (Fin.snoc u a) else 0 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_comm]
    _ ≤ p * lambdaVar + ∑ _i : Fin n, p * d := by
      exact add_le_add_left (Finset.sum_le_sum fun i _ => hnear i) _
    _ = _ := by simp; ring

/-- Summing extension estimates gives the ordered-moment recurrence. The
hereditary validity condition prevents an invalid prefix from contributing. -/
theorem ordered_moment_succ_le
    {α : Type*} [Fintype α] {n : ℕ}
    (valid : (k : ℕ) → (Fin k → α) → Prop)
    (joint : (k : ℕ) → (Fin k → α) → ℝ) (c : ℝ)
    (hprefix : ∀ u a, valid (n + 1) (Fin.snoc u a) → valid n u)
    (hext : ∀ u, valid n u →
      (∑ a, validTupleWeight (valid (n + 1)) (joint (n + 1)) (Fin.snoc u a)) ≤
        joint n u * c) :
    (∑ u, validTupleWeight (valid (n + 1)) (joint (n + 1)) u) ≤
      (∑ u, validTupleWeight (valid n) (joint n) u) * c := by
  classical
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => α)
  rw [← Equiv.sum_comp e]
  change (∑ p : α × (Fin n → α),
    validTupleWeight (valid (n + 1)) (joint (n + 1)) (Fin.snoc p.2 p.1)) ≤ _
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : valid n u
  · simpa [validTupleWeight, hu] using hext u hu
  · have hbad (a : α) : ¬ valid (n + 1) (Fin.snoc u a) := fun h => hu (hprefix u a h)
    simp [validTupleWeight, hu, hbad]

/-- Iterating the extension estimate produces the rising product, with one
linear neighborhood charge at each step. -/
theorem moment_le_rising_product (M : ℕ → ℝ) (lambdaVar d : ℝ)
    (hlambda : 0 ≤ lambdaVar) (hd : 0 ≤ d) (hzero : M 0 ≤ 1)
    (n : ℕ) (hstep : ∀ k < n, M (k + 1) ≤ M k * (lambdaVar + (k : ℝ) * d)) :
    M n ≤ ∏ k ∈ Finset.range n, (lambdaVar + (k : ℝ) * d) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    rw [Finset.prod_range_succ]
    exact (hstep n (Nat.lt_succ_self n)).trans
      (mul_le_mul_of_nonneg_right (ih fun k hk => hstep k (Nat.lt_succ_of_lt hk))
        (by positivity))

private theorem sum_range_eq_choose_two (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ)) = (Nat.choose n 2 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Nat.choose_succ_succ n 1
    norm_num at h
    simpa [add_comm] using (show (n : ℝ) + (n.choose 2 : ℝ) =
      ((n + 1).choose 2 : ℝ) by exact_mod_cast h.symm)

/-- The rising product is bounded by a Poisson moment times the exponential
of the total pair charge. -/
theorem rising_product_le_exp (n : ℕ) (lambdaVar d : ℝ)
    (hlambda : 0 < lambdaVar) (hd : 0 ≤ d) :
    (∏ k ∈ Finset.range n, (lambdaVar + (k : ℝ) * d)) ≤
      lambdaVar ^ n * Real.exp ((Nat.choose n 2 : ℝ) * d / lambdaVar) := by
  have hpoint (k : ℕ) : lambdaVar + (k : ℝ) * d ≤
      lambdaVar * Real.exp ((k : ℝ) * d / lambdaVar) := by
    have h := Real.add_one_le_exp ((k : ℝ) * d / lambdaVar)
    have hm := mul_le_mul_of_nonneg_left h hlambda.le
    have heq : lambdaVar * ((k : ℝ) * d / lambdaVar + 1) =
        lambdaVar + (k : ℝ) * d := by field_simp; ring
    rwa [heq] at hm
  calc
    _ ≤ ∏ k ∈ Finset.range n,
        (lambdaVar * Real.exp ((k : ℝ) * d / lambdaVar)) :=
      Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => hpoint k)
    _ = lambdaVar ^ n * Real.exp ((Nat.choose n 2 : ℝ) * d / lambdaVar) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp only [Finset.prod_const, Finset.card_range]
      congr 1
      rw [← Finset.sum_div, ← Finset.sum_mul, sum_range_eq_choose_two]

/-- Upper and lower moment estimates give an absolute error with the same
pair charge. The upper bound comes from the extension recurrence; the lower
bound only needs the mass lost to invalid tuples. -/
theorem moment_error_of_rising_product
    (n : ℕ) (hn : 1 ≤ n) (M lambdaVar d : ℝ)
    (hlambda : 0 < lambdaVar) (hd : 0 ≤ d)
    (hupper : M ≤ ∏ k ∈ Finset.range n, (lambdaVar + (k : ℝ) * d))
    (hlower : lambdaVar ^ n - (Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1) ≤ M) :
    |M - lambdaVar ^ n| ≤
      (Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1) *
        Real.exp ((Nat.choose n 2 : ℝ) * d / lambdaVar) := by
  let X := (Nat.choose n 2 : ℝ) * d / lambdaVar
  let A := (Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hexp : 1 ≤ Real.exp X := Real.one_le_exp hX
  have hexpdiff : Real.exp X - 1 ≤ X * Real.exp X := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-X))
      (Real.exp_pos X).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    linarith
  have hpow : lambdaVar ^ n * X = A := by
    dsimp [X, A]
    rw [← Nat.sub_add_cancel hn, pow_succ]
    field_simp
    ring
  have hu := hupper.trans (rising_product_le_exp n lambdaVar d hlambda hd)
  have he := mul_le_mul_of_nonneg_left hexpdiff (pow_nonneg hlambda.le n)
  change M ≤ lambdaVar ^ n * Real.exp X at hu
  change lambdaVar ^ n - A ≤ M at hlower
  change |M - lambdaVar ^ n| ≤ A * Real.exp X
  apply abs_le.mpr
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hexp hA]
  · calc
      M - lambdaVar ^ n ≤ lambdaVar ^ n * (Real.exp X - 1) := by linarith
      _ ≤ lambdaVar ^ n * (X * Real.exp X) := he
      _ = A * Real.exp X := by rw [← mul_assoc, hpow]

/-- The lower bound loses only the product mass of invalid tuples. Joint
probabilities of valid tuples may exceed their product weights. -/
theorem ordered_moment_ge_product_sub_invalid
    {α : Type*} [Fintype α] (n : ℕ)
    (compatible : (Fin n → α) → Prop) (joint : (Fin n → α) → ℝ)
    (w : α → ℝ) (lambdaVar : ℝ) (hsum : ∑ a, w a = lambdaVar)
    (hlower : ∀ u, Function.Injective u → compatible u → tupleProduct w u ≤ joint u) :
    lambdaVar ^ n - invalidTupleProductMass n compatible w ≤
      orderedFactorialMoment n compatible joint := by
  classical
  rw [← InvalidTupleMass.tuple_product_mass_eq_pow n w lambdaVar hsum]
  unfold invalidTupleProductMass orderedFactorialMoment
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : Function.Injective u ∧ compatible u
  · simpa [hu, tupleProduct] using hlower u hu.1 hu.2
  · simp [hu, tupleProduct]

/-- The full ordered-moment comparison from local extension laws. In
particular, this theorem proves the moment error instead of assuming an
already aggregated close-tuple error. All hypotheses concern single-cycle
extensions or product weights. -/
theorem ordered_factorial_moment_error_of_extension_load
    {α : Type*} [Fintype α]
    (n : ℕ) (hn : 1 ≤ n) (R : α → α → Prop)
    (compatible : (k : ℕ) → (Fin k → α) → Prop)
    (joint : (k : ℕ) → (Fin k → α) → ℝ)
    (w : α → ℝ) (lambdaVar d : ℝ)
    (hlambda : 0 < lambdaVar) (hd : 0 ≤ d) (hw : ∀ a, 0 ≤ w a)
    (hsum : ∑ a, w a = lambdaVar)
    (hzero : orderedFactorialMoment 0 (compatible 0) (joint 0) ≤ 1)
    (hprefix : ∀ k < n, ∀ u a, compatible (k + 1) (Fin.snoc u a) → compatible k u)
    (hjoint : ∀ k ≤ n, ∀ u, Function.Injective u → compatible k u → 0 ≤ joint k u)
    (hfar : ∀ k < n, ∀ u a,
      Function.Injective (Fin.snoc u a) → compatible (k + 1) (Fin.snoc u a) →
      (∀ i, ¬ R (u i) a) → joint (k + 1) (Fin.snoc u a) = joint k u * w a)
    (hnear : ∀ k < n, ∀ u, Function.Injective u → compatible k u → ∀ i : Fin k,
      (∑ a, if (Function.Injective (Fin.snoc u a) ∧
          compatible (k + 1) (Fin.snoc u a)) ∧ R (u i) a then
        joint (k + 1) (Fin.snoc u a) else 0) ≤ joint k u * d)
    (hproduct : ∀ u, Function.Injective u → compatible n u →
      tupleProduct w u ≤ joint n u)
    (hdiag : ∀ a, R a a)
    (hrow : ∀ a, (∑ b, if R a b then w b else 0) ≤ d)
    (hgood : ∀ u, InvalidTupleMass.pairwiseRGood R n u → compatible n u) :
    |orderedFactorialMoment n (compatible n) (joint n) - lambdaVar ^ n| ≤
      (Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1) *
        Real.exp ((Nat.choose n 2 : ℝ) * d / lambdaVar) := by
  classical
  let valid := fun k (u : Fin k → α) => Function.Injective u ∧ compatible k u
  have hweight (k : ℕ) (u : Fin k → α) :
      validTupleWeight (valid k) (joint k) u =
        (if Function.Injective u ∧ compatible k u then joint k u else 0) := by
    by_cases hu : Function.Injective u ∧ compatible k u <;>
      simp [validTupleWeight, valid, hu]
  have hmoment (k : ℕ) : (∑ u, validTupleWeight (valid k) (joint k) u) =
      orderedFactorialMoment k (compatible k) (joint k) := by
    unfold orderedFactorialMoment
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : Function.Injective u ∧ compatible k u <;>
      simp [validTupleWeight, valid, hu]
  have hstep (k : ℕ) (hk : k < n) :
      orderedFactorialMoment (k + 1) (compatible (k + 1)) (joint (k + 1)) ≤
        orderedFactorialMoment k (compatible k) (joint k) *
          (lambdaVar + (k : ℝ) * d) := by
    have hp : ∀ u a, valid (k + 1) (Fin.snoc u a) → valid k u := by
      intro u a hu
      refine ⟨?_, hprefix k hk u a hu.2⟩
      intro i j hij
      have hc : i.castSucc = j.castSucc := hu.1 (by simpa using hij)
      exact Fin.castSucc_injective _ hc
    have he : ∀ u, valid k u →
        (∑ a, validTupleWeight (valid (k + 1)) (joint (k + 1)) (Fin.snoc u a)) ≤
          joint k u * (lambdaVar + (k : ℝ) * d) := by
      intro u hu
      apply tuple_extension_sum_le R w (valid (k + 1)) (joint (k + 1)) u
        (joint k u) lambdaVar d (hjoint k hk.le u hu.1 hu.2) hw
        (fun a ha => hjoint (k + 1) hk (Fin.snoc u a) ha.1 ha.2) hsum
        (fun a ha hf => hfar k hk u a ha.1 ha.2 hf)
      intro i
      convert hnear k hk u hu.1 hu.2 i using 1
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Function.Injective (Fin.snoc u a) ∧ compatible (k + 1) (Fin.snoc u a) <;>
        by_cases hr : R (u i) a <;> simp [valid, ha, hr]
    have hrec := ordered_moment_succ_le (n := k) valid joint
      (lambdaVar + (k : ℝ) * d) hp he
    rwa [hmoment, hmoment] at hrec
  have hu := moment_le_rising_product
    (fun k => orderedFactorialMoment k (compatible k) (joint k))
    lambdaVar d hlambda.le hd hzero n hstep
  have hl := ordered_moment_ge_product_sub_invalid n (compatible n) (joint n)
    w lambdaVar hsum hproduct
  have hi := invalid_tuple_product_mass_le_choose_two_of_pairwiseRGood
    n R (compatible n) w lambdaVar d hw hdiag hrow hsum hd hgood
  exact moment_error_of_rising_product n hn _ lambdaVar d hlambda hd hu (by linarith)

end Erdos1016.Proof.ConditionalMoments
