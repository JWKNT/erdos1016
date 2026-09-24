import Erdos1016.Probability.Conditional.UniformReveal
import Erdos1016.Probability.Conditional.ComponentProductLaw

set_option autoImplicit false

/-!
# Conditional products inside a revealed fiber

This finite product estimate supplies the local step for the reveal argument:
if a fiber decomposes as independent local choices and each selected
zero-cut region has local forest density at most one half, then `z` such
regions multiply the conditional bound to `2^-z`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.RevealedFiberProduct

open Erdos1016

private theorem activeDensity_eq_finiteDensity {α : Type*} [Fintype α]
    (P : α → Prop) :
    Erdos1016.Proof.ActiveComponentProbability.density P =
      Finite.density P := by
  classical
  unfold Erdos1016.Proof.ActiveComponentProbability.density Finite.density
  rw [Erdos1016.BoundaryTrace.count_eq_subtype_card]
  simp [Nat.card_eq_fintype_card]

/-- A product event whose `Z`-indexed local factors each have density at most
one half has global density at most `2^(−|Z|)`. -/
theorem density_intersection_le_half_pow
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)]
    (e : Ω ≃ ((i : ι) → A i))
    (U : Ω → Prop) (Q : ∀ i, A i → Prop)
    (hU : ∀ x, U x ↔ ∀ i, Q i (e x i))
    (Z : Finset ι)
    (hhalf : ∀ i ∈ Z,
      Finite.density (Q i) ≤ (1 / 2 : ℝ)) :
    Finite.density U ≤ (1 / 2 : ℝ) ^ Z.card := by
  classical
  letI : ∀ i, Fintype (A i) := fun i => inferInstance
  have hfactor :=
    Erdos1016.Proof.ActiveComponentProbability.density_eq_prod_of_equiv
      A (fun i => inferInstance) e U Q hU
  rw [activeDensity_eq_finiteDensity] at hfactor
  rw [hfactor]
  let p : ι → ℝ := fun i =>
    Erdos1016.Proof.ActiveComponentProbability.density (Q i)
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    dsimp [p]
    rw [activeDensity_eq_finiteDensity]
    exact Finite.density_nonneg (Q i)
  have hp1 : ∀ i, p i ≤ 1 := by
    intro i
    dsimp [p]
    rw [activeDensity_eq_finiteDensity]
    exact Finite.density_le_one (Q i)
  have hprod :
      (∏ i, p i) ≤ ∏ i, if i ∈ Z then (1 / 2 : ℝ) else 1 := by
    apply Finset.prod_le_prod
    · intro i hi
      exact hp0 i
    · intro i hi
      by_cases hz : i ∈ Z
      · have hh : p i ≤ (1 / 2 : ℝ) := by
          dsimp [p]
          rw [activeDensity_eq_finiteDensity]
          exact hhalf i hz
        simpa [hz] using hh
      · simpa [p, hz] using hp1 i
  have htarget :
      (∏ i, if i ∈ Z then (1 / 2 : ℝ) else 1) =
        (1 / 2 : ℝ) ^ Z.card := by
    rw [Finset.prod_ite_mem]
    simp
  simpa [p, htarget] using hprod

/-- It is enough for the global event to imply the selected local conditions.
The global event itself may retain interactions with all other coordinates:
we compare it by inclusion with the intersection on the selected factors. -/
theorem density_le_half_pow_of_selected_product_implication
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (A : ι → Type*) [∀ i, Fintype (A i)]
    (e : Ω ≃ ((i : ι) → A i))
    (U : Ω → Prop) (Q : ∀ i, A i → Prop)
    (Z : Finset ι)
    (hU : ∀ x, U x → ∀ i ∈ Z, Q i (e x i))
    (hhalf : ∀ i ∈ Z,
      Finite.density (Q i) ≤ (1 / 2 : ℝ)) :
    Finite.density U ≤ (1 / 2 : ℝ) ^ Z.card := by
  classical
  letI : ∀ i, Fintype (A i) := fun i => inferInstance
  let UZ : Ω → Prop := fun x => ∀ i ∈ Z, Q i (e x i)
  let QZ : ∀ i, A i → Prop := fun i a => if i ∈ Z then Q i a else True
  have hfactor : ∀ x, UZ x ↔ ∀ i, QZ i (e x i) := by
    intro x
    simp [UZ, QZ]
  have hUZ := density_intersection_le_half_pow A e UZ QZ hfactor Z (by
    intro i hi
    simpa [QZ, hi] using hhalf i hi)
  have hcountIncl : Finite.count U ≤ Finite.count UZ :=
    Finite.count_mono (fun x hx => hU x hx)
  have hcountUZ := Finite.count_le_mul_card_of_density_le hUZ
  have hcountU : Finite.count U ≤ (1 / 2 : ℝ) ^ Z.card * Fintype.card Ω := by
    calc
      Finite.count U ≤ Finite.count UZ := hcountIncl
      _ ≤ (1 / 2 : ℝ) ^ Z.card * Fintype.card Ω := by
        simpa [mul_comm] using hcountUZ
  exact Finite.density_le_of_count_le_mul_card (by positivity) hcountU



/-- Conditional form of the implication variant above. Given any revealed
fiber, if the global forest event forces each zero-cut local factor to be a
forest and each such factor has density at most one half, `a` zero cuts yield
the conditional bound `2^-a`. No factorization of the global event is needed. -/
theorem fiber_density_le_half_pow_of_selected_product_implication
    {Ω Y ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (reveal : Ω → Y)
    (A : Y → ι → Type*)
    (hA : ∀ y i, Fintype (A y i))
    (e : ∀ y, Erdos1016.Proof.RevealedFiberProbability.fiber reveal y ≃
      ((i : ι) → A y i))
    (U : Ω → Prop) (Q : ∀ y i, A y i → Prop)
    (zeroCut : ι → Y → Prop)
    (hU : ∀ y (x : Erdos1016.Proof.RevealedFiberProbability.fiber reveal y),
      U x.1 → ∀ i, zeroCut i y → Q y i (e y x i))
    (hzero : ∀ y i, zeroCut i y →
      Finite.density (Q y i) ≤ (1 / 2 : ℝ))
    (a : ℕ) :
    ∀ y, a ≤ Nat.card {i : ι // zeroCut i y} →
      Finite.density
        (fun x : Erdos1016.Proof.RevealedFiberProbability.fiber reveal y => U x.1) ≤
        (1 / 2 : ℝ) ^ a := by
  classical
  intro y hmany
  letI : ∀ i, Fintype (A y i) := fun i => hA y i
  letI : DecidablePred (fun i : ι => zeroCut i y) :=
    fun i => Classical.propDecidable (zeroCut i y)
  letI : Fintype {i : ι // zeroCut i y} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  let Z : Finset ι := Finset.univ.filter fun i => zeroCut i y
  have hZcard : Z.card = Nat.card {i : ι // zeroCut i y} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hproduct := density_le_half_pow_of_selected_product_implication
    (A y) (e y) (fun x : Erdos1016.Proof.RevealedFiberProbability.fiber reveal y =>
      U x.1) (Q y) Z (by
        intro x hx i hi
        exact hU y x hx i (Finset.mem_filter.mp hi).2)
    (by
      intro i hi
      exact hzero y i (Finset.mem_filter.mp hi).2)
  have hpow : (1 / 2 : ℝ) ^ Z.card ≤ (1 / 2 : ℝ) ^ a := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    rw [hZcard]
    exact hmany
  simpa [Z] using hproduct.trans hpow

end Erdos1016.Proof.RevealedFiberProduct
