import Erdos1016.Probability.Cylinders.Affine
import Erdos1016.Probability.Moments.PaleyZygmund

set_option autoImplicit false

/-!
# Uniform lower bound for a feasible three-coordinate event

A nonempty fiber of at most three binary linear constraints has probability
at least `1/8` in the ambient uniform vector space. This is the first-moment
input used for the selected-star-triple events in the Section 10 cleanup.
-/

noncomputable section

namespace Erdos1016.Proof.SelectedTripleCylinder

abbrev F₂ := ZMod 2

/-- Uniform event probability is invariant under a bijective reindexing of
the finite sample space. -/
theorem uniformEventProbability_congr_equiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : X → Prop) :
    Erdos1016.Proof.FinitePaleyZygmund.probability P =
      Erdos1016.Proof.FinitePaleyZygmund.probability
        (fun y => P (e.symm y)) := by
  classical
  have hsub : {x : X // P x} ≃ {y : Y // P (e.symm y)} := by
    refine Equiv.subtypeEquiv e ?_
    intro x
    simp
  have hcard : Fintype.card X = Fintype.card Y := Fintype.card_congr e
  unfold Erdos1016.Proof.FinitePaleyZygmund.probability
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  rw [Fintype.card_congr hsub, hcard]

variable {U V : Type*}
  [AddCommGroup U] [Module F₂ U] [FiniteDimensional F₂ U] [Fintype U]
  [AddCommGroup V] [Module F₂ V] [FiniteDimensional F₂ V] [Fintype V]
  [Fintype F₂]

/-- Uniform probability of a fiber of a linear map on a finite vector space. -/
def fiberProbability (f : U →ₗ[F₂] V) (b : V) : ℝ :=
  (Nat.card {x : U // f x = b} : ℝ) / (Fintype.card U : ℝ)

/-- The probability of a feasible linear fiber is exactly `2` to minus the
rank of the constraint map. -/
theorem fiberProbability_eq (f : U →ₗ[F₂] V) (b : V)
    (x₀ : {x : U // f x = b}) :
    fiberProbability f b =
      1 / (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range f) := by
  have hfiber := Erdos1016.Proof.AffineCylinders.fiber_natCard f x₀
  have hU : Nat.card U = 2 ^ Module.finrank F₂ U := by
    simpa [Nat.card_eq_fintype_card] using
      (Module.natCard_eq_pow_finrank (K := F₂) (V := U))
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  unfold fiberProbability
  rw [hfiber]
  have hpow : (2 : ℝ) ^ Module.finrank F₂ (LinearMap.ker f) *
      (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range f) =
        (2 : ℝ) ^ Module.finrank F₂ U := by
    calc
      _ = (2 : ℝ) ^ (Module.finrank F₂ (LinearMap.ker f) +
          Module.finrank F₂ (LinearMap.range f)) := by rw [← pow_add]
      _ = (2 : ℝ) ^ (Module.finrank F₂ (LinearMap.range f) +
          Module.finrank F₂ (LinearMap.ker f)) := by rw [Nat.add_comm]
      _ = (2 : ℝ) ^ Module.finrank F₂ U := by rw [hrank]
  have hden : (Fintype.card U : ℝ) =
      (2 : ℝ) ^ Module.finrank F₂ U := by
    have hUcast : (Nat.card U : ℝ) =
        (2 : ℝ) ^ Module.finrank F₂ U := by exact_mod_cast hU
    simpa [Nat.card_eq_fintype_card] using hUcast
  rw [hden]
  have hsub : (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range f) ≠ 0 := by
    positivity
  field_simp
  nlinarith

/-- A feasible affine event imposed by a constraint space of dimension at
most three has probability at least `1/8`. -/
theorem fiberProbability_ge_one_eighth
    (f : U →ₗ[F₂] V) (b : V)
    (hV : Module.finrank F₂ V ≤ 3)
    (x₀ : {x : U // f x = b}) :
    (1 / 8 : ℝ) ≤ fiberProbability f b := by
  rw [fiberProbability_eq f b x₀]
  have hrange : Module.finrank F₂ (LinearMap.range f) ≤ 3 := by
    have hmono := Submodule.finrank_mono
      (le_top : LinearMap.range f ≤ (⊤ : Submodule F₂ V))
    have hmono' : Module.finrank F₂ (LinearMap.range f) ≤
        Module.finrank F₂ V := by simpa using hmono
    exact hmono'.trans hV
  have hpow : (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range f) ≤ 2 ^ 3 := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) hrange)
  have hrecip := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ Module.finrank F₂ (LinearMap.range f))
    hpow
  norm_num at hrecip ⊢
  exact hrecip

/-- The fiber-cardinality probability agrees with the project's standard
uniform-event probability, so this estimate can be used directly in the
finite cylinder second-moment argument. -/
theorem eventProbability_eq_fiberProbability
    (f : U →ₗ[F₂] V) (b : V) :
    Erdos1016.Proof.FinitePaleyZygmund.probability
        (fun x : U => f x = b) = fiberProbability f b := by
  classical
  unfold Erdos1016.Proof.FinitePaleyZygmund.probability fiberProbability
  have hcard : (Finset.univ.filter (fun x : U => f x = b)).card =
      Fintype.card {x : U // f x = b} := by
    rw [Fintype.card_subtype]
  rw [hcard]
  have hnat : Nat.card {x : U // f x = b} =
      Fintype.card {x : U // f x = b} := by
    exact Nat.card_eq_fintype_card
  rw [hnat]

/-- Standard uniform probability form of the feasible three-constraint
lower bound. -/
theorem eventProbability_fiber_ge_one_eighth
    [Nonempty U] (f : U →ₗ[F₂] V) (b : V)
    (hV : Module.finrank F₂ V ≤ 3)
    (x₀ : {x : U // f x = b}) :
    (1 / 8 : ℝ) ≤
      Erdos1016.Proof.FinitePaleyZygmund.probability
        (fun x : U => f x = b) := by
  rw [eventProbability_eq_fiberProbability]
  exact fiberProbability_ge_one_eighth f b hV x₀

end Erdos1016.Proof.SelectedTripleCylinder
