import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Erdos1016.Nonbacktracking.Walks.ShortPathUniqueness

/-!
# The finite summation step in the short external-return filter

The graph-theoretic theta decomposition is kept separate from the exact
weight arithmetic here.  A fixed-endpoint suffix estimate gives a mass of at
most `(3/2) 2^{-s}` at each path length.  Summing over at most `L` lengths,
`L^2` ordered endpoint pairs on a base cycle, and then over base cycles gives
the relative theta mass `(3/2) L^3 2^{-s} W_L`.  The final factor `3 * 2^q`
is the paper's constituent-cycle charging step.

The remaining graph-specific inputs are stated explicitly in
`shortReturn_filter_bound_of_theta_accounting`; this file does not claim to
construct the theta decomposition from `SimpleGraph.Walk`s.
-/

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ExternalReturnFilter

open scoped BigOperators

/-- One length slice of the paper's suffix estimate, expressed as weighted
path mass.  The count premise is precisely the subcubic prefix budget
`3 * 2^(a-s-1)`. -/
theorem one_length_suffix_mass_le
    (a s : ℕ) (count : ℕ)
    (hsa : s < a)
    (hcount : count ≤ 3 * 2 ^ (a - s - 1)) :
    (count : ℝ) * (1 / 2 : ℝ) ^ a ≤
      (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hcast : (count : ℝ) ≤ 3 * (2 : ℝ) ^ (a - s - 1) := by
    exact_mod_cast hcount
  have hexp : (a - s - 1) + (s + 1) = a := by omega
  have hpow : (2 : ℝ) ^ (a - s - 1) * (2 : ℝ) ^ (s + 1) =
      (2 : ℝ) ^ a := by
    rw [← pow_add]
    congr 1
  have hright : ((3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s) *
      (2 : ℝ) ^ a = 3 * (2 : ℝ) ^ (a - s - 1) := by
    rw [← hpow, pow_succ]
    field_simp
    ring
  have hmass : (count : ℝ) / (2 : ℝ) ^ a ≤
      (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
    apply (div_le_iff₀ hp).2
    calc
      (count : ℝ) ≤ 3 * (2 : ℝ) ^ (a - s - 1) := hcast
      _ = ((3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s) * (2 : ℝ) ^ a := hright.symm
  have hrecip : (1 / 2 : ℝ) ^ a = ((2 : ℝ) ^ a)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  calc
    (count : ℝ) * (1 / 2 : ℝ) ^ a =
        (count : ℝ) * ((2 : ℝ) ^ a)⁻¹ := by rw [hrecip]
    _ = (count : ℝ) / (2 : ℝ) ^ a := (div_eq_mul_inv _ _).symm
    _ ≤ (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := hmass

/-- Sum the equal fixed-endpoint suffix budgets over all lengths
`s < a ≤ L`. -/
theorem fixed_endpoint_suffix_mass_le
    (s L : ℕ) (count : ℕ → ℕ)
    (hcount : ∀ a ∈ Finset.Ioc s L,
      count a ≤ 3 * 2 ^ (a - s - 1)) :
    (∑ a ∈ Finset.Ioc s L,
        (count a : ℝ) * (1 / 2 : ℝ) ^ a) ≤
      (3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s := by
  have hslice (a : ℕ) (ha : a ∈ Finset.Ioc s L) :
      (count a : ℝ) * (1 / 2 : ℝ) ^ a ≤
        (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s :=
    one_length_suffix_mass_le a s (count a) (Finset.mem_Ioc.mp ha).1
      (hcount a ha)
  have hcard : (Finset.Ioc s L).card = L - s := by simp
  have hL : ((Finset.Ioc s L).card : ℝ) ≤ (L : ℝ) := by
    rw [hcard]
    exact_mod_cast Nat.sub_le L s
  have hconst : 0 ≤ (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by positivity
  calc
    _ ≤ ∑ _a ∈ Finset.Ioc s L,
        (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
          apply Finset.sum_le_sum
          intro a ha
          exact hslice a ha
    _ = ((Finset.Ioc s L).card : ℝ) *
        ((3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s) := by simp
    _ ≤ (L : ℝ) * ((3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s) :=
      mul_le_mul_of_nonneg_right hL hconst
    _ = (3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s := by ring

/-- Sum suffix path mass over the at most `L^2` ordered endpoint choices on
each base cycle, and over a finite base-cycle supply.  The `count` values may
be any graph-specific path counts satisfying the exact prefix bound. -/
theorem base_endpoint_suffix_mass_le
    {B E : Type*} [DecidableEq B] [DecidableEq E]
    (bases : Finset B) (endpoints : B → Finset E)
    (baseWeight : B → ℝ) (count : B → E → ℕ → ℕ) (s L : ℕ)
    (hweight : ∀ b ∈ bases, 0 ≤ baseWeight b)
    (hendpoint : ∀ b ∈ bases, (endpoints b).card ≤ L ^ 2)
    (hcount : ∀ b ∈ bases, ∀ e ∈ endpoints b, ∀ a ∈ Finset.Ioc s L,
      count b e a ≤ 3 * 2 ^ (a - s - 1)) :
    (∑ b ∈ bases, baseWeight b *
      (∑ e ∈ endpoints b, ∑ a ∈ Finset.Ioc s L,
        (count b e a : ℝ) * (1 / 2 : ℝ) ^ a)) ≤
      (3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s *
        (∑ b ∈ bases, baseWeight b) := by
  have hslice (b : B) (hb : b ∈ bases) (e : E) (he : e ∈ endpoints b) :
      (∑ a ∈ Finset.Ioc s L,
        (count b e a : ℝ) * (1 / 2 : ℝ) ^ a) ≤
        (3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s :=
    fixed_endpoint_suffix_mass_le s L (count b e)
      (fun a ha => hcount b hb e he a ha)
  have hendpointMass (b : B) (hb : b ∈ bases) :
      (∑ e ∈ endpoints b, ∑ a ∈ Finset.Ioc s L,
        (count b e a : ℝ) * (1 / 2 : ℝ) ^ a) ≤
      (L : ℝ) ^ 2 * ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s) := by
    calc
      _ ≤ ∑ _e ∈ endpoints b,
          (3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s := by
            apply Finset.sum_le_sum
            intro e he
            exact hslice b hb e he
      _ = ((endpoints b).card : ℝ) *
          ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s) := by simp
      _ ≤ (L : ℝ) ^ 2 * ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hendpoint b hb
        · positivity
  have hbase (b : B) (hb : b ∈ bases) :
      baseWeight b *
        (∑ e ∈ endpoints b, ∑ a ∈ Finset.Ioc s L,
          (count b e a : ℝ) * (1 / 2 : ℝ) ^ a) ≤
      baseWeight b * ((L : ℝ) ^ 2 *
        ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s)) :=
    mul_le_mul_of_nonneg_left (hendpointMass b hb) (hweight b hb)
  calc
    _ ≤ ∑ b ∈ bases, baseWeight b * ((L : ℝ) ^ 2 *
        ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s)) := by
          apply Finset.sum_le_sum
          intro b hb
          exact hbase b hb
    _ = ((L : ℝ) ^ 2 *
        ((3 / 2 : ℝ) * (L : ℝ) * (1 / 2 : ℝ) ^ s)) *
        (∑ b ∈ bases, baseWeight b) := by
          rw [Finset.mul_sum]
          simp_rw [mul_comm (baseWeight _)]
    _ = (3 / 2 : ℝ) * (L : ℝ) ^ 3 * (1 / 2 : ℝ) ^ s *
        (∑ b ∈ bases, baseWeight b) := by ring



end Erdos1016.Proof.ExternalReturnFilter
end
