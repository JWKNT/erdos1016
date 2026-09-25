import Erdos1016.Probability.Finite.Counting

set_option autoImplicit false

/-!
# A nonzero linear projection costs at least half the uniform mass

If an event can occur only in the kernel of a nonzero linear map over
`F₂`, translation by any vector with nonzero image pairs its points with
points outside the event. The estimate is stated using the project's
uniform finite density convention.
-/

noncomputable section

namespace Erdos1016.Proof.NonzeroProjectionLoss

open Erdos1016

abbrev F₂ := ZMod 2

theorem density_le_half_of_nonzero_linear_obstruction
    {X Y : Type*}
    [AddCommGroup X] [Module F₂ X] [FiniteDimensional F₂ X] [Fintype X]
    [AddCommGroup Y] [Module F₂ Y] [FiniteDimensional F₂ Y] [Fintype Y]
    (f : X →ₗ[F₂] Y) (hf : f ≠ 0) (U : X → Prop)
    (hU : ∀ x, U x → f x = 0) :
    Finite.density U ≤ (1 / 2 : ℝ) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : X, f a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext h)
  let translate : {x : X // U x} → {x : X // ¬ U x} := fun x => by
    refine ⟨x.1 + a, ?_⟩
    intro hUa
    have hzero := hU (x.1 + a) hUa
    rw [map_add, hU x.1 x.2] at hzero
    exact ha (by simpa using hzero)
  have hinj : Function.Injective translate := by
    intro x y hxy
    apply Subtype.ext
    have hv := congrArg Subtype.val hxy
    exact add_right_cancel hv
  have hcard : Fintype.card {x : X // U x} ≤
      Fintype.card {x : X // ¬ U x} :=
    Fintype.card_le_of_injective translate hinj
  let good : Finset X := Finset.univ.filter U
  let bad : Finset X := Finset.univ.filter (fun x => ¬ U x)
  have hgood : Finite.count U = (good.card : ℝ) := by
    simp [Finite.count, good, Finset.sum_boole]
  have hgoodCard : Fintype.card {x : X // U x} = good.card := by
    simpa [good] using (Fintype.card_subtype U)
  have hbadCard : Fintype.card {x : X // ¬ U x} = bad.card := by
    simpa [bad] using (Fintype.card_subtype (fun x : X => ¬ U x))
  have hgoodleNat : good.card ≤ bad.card := by
    calc
      good.card = Fintype.card {x : X // U x} := hgoodCard.symm
      _ ≤ Fintype.card {x : X // ¬ U x} := hcard
      _ = bad.card := hbadCard
  have hsum : good.card + bad.card = Fintype.card X := by
    simpa [good, bad] using
      (Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ) U)
  have hgoodle : (good.card : ℝ) ≤ (bad.card : ℝ) := by
    exact_mod_cast hgoodleNat
  unfold Finite.density
  rw [hgood]
  have hden : (Fintype.card X : ℝ) = (good.card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast hsum.symm
  rw [hden]
  have hXpos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨(0 : X)⟩
  have hdenpos : (0 : ℝ) < (good.card : ℝ) + (bad.card : ℝ) := by
    rw [← hden]
    exact_mod_cast hXpos
  apply (div_le_iff₀ hdenpos).2
  nlinarith

end Erdos1016.Proof.NonzeroProjectionLoss
