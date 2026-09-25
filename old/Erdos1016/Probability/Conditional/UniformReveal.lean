import Erdos1016.Boundary.EvenBoundaryAverage
import Erdos1016.Probability.Cylinders.GraphicalThreshold

set_option autoImplicit false

/-!
# Conditioning by a uniform finite reveal

If a finite sample space is revealed through a map with equally sized fibers,
then any conditional event bound on the high-count fibers can be averaged
without loss. This is the abstract probability step behind complete outside
conditioning in the many-cyclic-regions argument.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.RevealedFiberProbability

open Erdos1016
open Erdos1016.BoundaryTrace

local instance revealedFiberDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def fiber {Ω Y : Type*} (reveal : Ω → Y) (y : Y) :=
  {x : Ω // reveal x = y}

noncomputable instance fiberFintype {Ω Y : Type*} [Fintype Ω]
    (reveal : Ω → Y) (y : Y) : Fintype (fiber reveal y) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

def revealEquivSigma {Ω Y : Type*} (reveal : Ω → Y) :
    Ω ≃ Σ y : Y, fiber reveal y where
  toFun x := ⟨reveal x, ⟨x, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨y, ⟨x, hxy⟩⟩
    subst y
    rfl

private theorem density_compl {Y : Type*} [Fintype Y] [Nonempty Y]
    (P : Y → Prop) :
    Finite.density (fun y => ¬ P y) = 1 - Finite.density P := by
  classical
  letI : DecidablePred P := fun y => Classical.propDecidable (P y)
  letI : DecidablePred (fun y : Y => ¬ P y) :=
    fun y => Classical.propDecidable ((fun y : Y => ¬ P y) y)
  have hsum : Finite.count P + Finite.count (fun y => ¬ P y) =
      (Fintype.card Y : ℝ) := by
    unfold Finite.count
    rw [← Finset.sum_add_distrib]
    calc
      (∑ y, ((if P y then (1 : ℝ) else 0) +
          (if ¬ P y then (1 : ℝ) else 0))) = ∑ _y : Y, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases h : P y <;> simp [h]
      _ = (Fintype.card Y : ℝ) := by simp
  have hden : (Fintype.card Y : ℝ) ≠ 0 := by positivity
  unfold Finite.density
  have h := congrArg (fun z : ℝ => z / (Fintype.card Y : ℝ)) hsum
  change (Finite.count P + Finite.count (fun y => ¬ P y)) /
      Fintype.card Y = (Fintype.card Y : ℝ) / Fintype.card Y at h
  rw [add_div, div_self hden] at h
  linarith

private theorem eventProbability_eq_density {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) :
    Erdos1016.Proof.GraphicalThreshold.eventProbability P =
      Finite.density P := by
  classical
  unfold Erdos1016.Proof.GraphicalThreshold.eventProbability
    Erdos1016.Proof.FinitePaleyZygmund.probability Finite.density Finite.count
  rw [Finset.sum_boole]

theorem eventProbability_congr {Ω : Type*} [Fintype Ω]
    {P Q : Ω → Prop} (h : ∀ x, P x ↔ Q x) :
    Erdos1016.Proof.GraphicalThreshold.eventProbability P =
      Erdos1016.Proof.GraphicalThreshold.eventProbability Q := by
  rw [eventProbability_eq_density, eventProbability_eq_density]
  exact Finite.density_equiv (Equiv.refl Ω) (by intro x; exact h x)

noncomputable def eventCountNat {Ω ι : Type*} [Fintype ι]
    (E : ι → Ω → Prop) (x : Ω) : ℕ :=
  (Finset.univ.filter fun i => E i x).card

/-- An event count is unchanged by pulling its cylinders back through a reveal
map. -/
theorem eventCount_eq_nat_reveal {Ω Y ι : Type*} [Fintype ι]
    (reveal : Ω → Y) (E : ι → Ω → Prop) (Ebar : ι → Y → Prop)
    (hE : ∀ i x, E i x ↔ Ebar i (reveal x)) (x : Ω) :
    Erdos1016.Proof.GraphicalThreshold.eventCount E x =
      (eventCountNat Ebar (reveal x) : ℝ) := by
  classical
  unfold Erdos1016.Proof.GraphicalThreshold.eventCount eventCountNat
  have hsum :
      (∑ i, if E i x then (1 : ℝ) else 0) =
        ∑ i, if Ebar i (reveal x) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hE i x]
  rw [hsum, Finset.sum_boole]

/-- Pulling an event back along an equally-fibered surjection preserves its
uniform density. -/
theorem density_pullback_of_uniform_fibers
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] [Nonempty Ω]
    (reveal : Ω → Y) (hsurj : Function.Surjective reveal)
    (k : ℕ) (hcard : ∀ y, Fintype.card (fiber reveal y) = k)
    (P : Y → Prop) :
    Finite.density (fun x => P (reveal x)) = Finite.density P := by
  classical
  letI : Nonempty Y := ⟨reveal (Classical.choice ‹Nonempty Ω›)⟩
  have hk : 0 < k := by
    obtain ⟨x, hx⟩ := hsurj (Classical.choice ‹Nonempty Y›)
    have hpos : 0 < Fintype.card (fiber reveal (reveal x)) :=
      Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    rw [hcard] at hpos
    exact hpos
  rw [Finite.density_equiv (revealEquivSigma reveal)
    (P := fun x : Ω => P (reveal x))
    (Q := fun z : Σ y : Y, fiber reveal y => P z.1)
    (by intro x; rfl)]
  rw [sigma_density_eq_average k hcard (fun z : Σ y : Y, fiber reveal y => P z.1)]
  have hlocal (y : Y) :
      Finite.density (fun x : fiber reveal y => P y) =
        if P y then 1 else 0 := by
    by_cases hp : P y
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
      simp [hp, Finite.density, Finite.count, hcard y, hkR]
    · simp [hp, Finite.density, Finite.count]
  have hsumLocal :
      (∑ y, Finite.density (fun x : fiber reveal y => P y)) =
        ∑ y, if P y then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hlocal y
  rw [hsumLocal]
  unfold Finite.density Finite.count
  rw [Finset.sum_boole]

/-- Suppose that every reveal fiber on which at least `a` local events occur
has conditional `U`-density at most `2^-a`. Then the global density of `U` is
at most one minus the high-count probability, plus the same tail allowance. -/
theorem event_density_le_complement_high_count_add
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] [Nonempty Ω]
    (reveal : Ω → Y) (hsurj : Function.Surjective reveal)
    (k : ℕ) (hcard : ∀ y, Fintype.card (fiber reveal y) = k)
    (U : Ω → Prop) (score : Y → ℕ) (a : ℕ)
    (hconditional : ∀ y, a ≤ score y →
      Finite.density (fun x : fiber reveal y => U x.1) ≤
        (1 / 2 : ℝ) ^ a) :
    Finite.density U ≤
      1 - Finite.density (fun x => a ≤ score (reveal x)) +
        (1 / 2 : ℝ) ^ a := by
  classical
  letI : Nonempty Y := ⟨reveal (Classical.choice ‹Nonempty Ω›)⟩
  have hk : 0 < k := by
    obtain ⟨x, hx⟩ := hsurj (Classical.choice ‹Nonempty Y›)
    have hpos : 0 < Fintype.card (fiber reveal (reveal x)) :=
      Fintype.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    rw [hcard] at hpos
    exact hpos
  let high : Y → Prop := fun y => a ≤ score y
  letI : DecidablePred high := fun y => Classical.propDecidable (high y)
  letI : DecidablePred (fun y : Y => ¬ high y) :=
    fun y => Classical.propDecidable ((fun y : Y => ¬ high y) y)
  let localU : Y → ℝ := fun y =>
    Finite.density (fun x : fiber reveal y => U x.1)
  have hUavg : Finite.density U =
      (∑ y, localU y) / Fintype.card Y := by
    rw [Finite.density_equiv (revealEquivSigma reveal)
      (P := U)
      (Q := fun z : Σ y : Y, fiber reveal y => U z.2.1)
      (by intro x; rfl)]
    exact sigma_density_eq_average k hcard
      (fun z : Σ y : Y, fiber reveal y => U z.2.1)
  have hHighPull : Finite.density (fun x => high (reveal x)) =
      Finite.density high :=
    density_pullback_of_uniform_fibers reveal hsurj k hcard high
  have hlocalBound (y : Y) : localU y ≤ if high y then
      (1 / 2 : ℝ) ^ a else 1 := by
    by_cases hy : high y
    · simpa [localU, high, hy] using hconditional y hy
    · have hle := Finite.density_le_one
        (fun x : fiber reveal y => U x.1)
      simpa [localU, hy] using hle
  have hsum : (∑ y, localU y) ≤
      ∑ y, if high y then (1 / 2 : ℝ) ^ a else 1 := by
    apply Finset.sum_le_sum
    intro y hy
    exact hlocalBound y
  have hsumRewrite :
      (∑ y, if high y then (1 / 2 : ℝ) ^ a else 1) =
        Finite.count (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.count high := by
    calc
      (∑ y, if high y then (1 / 2 : ℝ) ^ a else 1) =
          ∑ y, ((if ¬ high y then (1 : ℝ) else 0) +
            (1 / 2 : ℝ) ^ a * (if high y then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hh : high y <;> simp [hh]
      _ = (∑ y, if ¬ high y then (1 : ℝ) else 0) +
          (1 / 2 : ℝ) ^ a * (∑ y, if high y then (1 : ℝ) else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by unfold Finite.count; rfl
  have hHCompl := density_compl high
  have hHle : Finite.density high ≤ 1 := Finite.density_le_one high
  have htaunonneg : 0 ≤ (1 / 2 : ℝ) ^ a := by positivity
  have havg :
      (Finite.count (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.count high) /
        Fintype.card Y ≤
          Finite.density (fun y => ¬ high y) + (1 / 2 : ℝ) ^ a := by
    have hN : (0 : ℝ) < Fintype.card Y := by positivity
    have hrewrite :
        (Finite.count (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.count high) /
          Fintype.card Y =
        Finite.density (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.density high := by
      unfold Finite.density
      rw [add_div]
      ring
    rw [hrewrite]
    calc
      Finite.density (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.density high ≤
        Finite.density (fun y => ¬ high y) + (1 / 2 : ℝ) ^ a * 1 :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left hHle htaunonneg)
            (Finite.density (fun y => ¬ high y))
      _ = Finite.density (fun y => ¬ high y) + (1 / 2 : ℝ) ^ a := by ring
  have hmain : Finite.density U ≤
      Finite.density (fun y => ¬ high y) + (1 / 2 : ℝ) ^ a := by
    rw [hUavg]
    calc
      (∑ y, localU y) / Fintype.card Y ≤
          (∑ y, if high y then (1 / 2 : ℝ) ^ a else 1) /
            Fintype.card Y := by
        apply div_le_div_of_nonneg_right hsum
        exact Nat.cast_nonneg _
      _ = (Finite.count (fun y => ¬ high y) +
          (1 / 2 : ℝ) ^ a * Finite.count high) /
            Fintype.card Y := by rw [hsumRewrite]
      _ ≤ _ := havg
  have hmain' := hmain
  rw [hHCompl] at hmain'
  rw [← hHighPull] at hmain'
  simpa [high] using hmain'

/-- The same estimate in the `eventProbability` notation used by the
many-cyclic-regions second-moment theorem. -/
theorem eventProbability_le_complement_high_count_add
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] [Nonempty Ω]
    (reveal : Ω → Y) (hsurj : Function.Surjective reveal)
    (k : ℕ) (hcard : ∀ y, Fintype.card (fiber reveal y) = k)
    (U : Ω → Prop) (score : Y → ℕ) (a : ℕ)
    (hconditional : ∀ y, a ≤ score y →
      Finite.density (fun x : fiber reveal y => U x.1) ≤
        (1 / 2 : ℝ) ^ a) :
    Erdos1016.Proof.GraphicalThreshold.eventProbability U ≤
      1 - Erdos1016.Proof.GraphicalThreshold.eventProbability
          (fun x => a ≤ score (reveal x)) + (1 / 2 : ℝ) ^ a := by
  rw [eventProbability_eq_density, eventProbability_eq_density]
  exact event_density_le_complement_high_count_add
    reveal hsurj k hcard U score a hconditional

/-- The revealing-space lemma specialized to a family of cylinder events:
if each high-count reveal fiber has forest density at most `2^-a`, then the
usual event-count conditional-product inequality follows. -/
theorem eventProbability_le_complement_eventCount_add
    {Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι] [Nonempty Ω]
    (reveal : Ω → Y) (hsurj : Function.Surjective reveal)
    (k : ℕ) (hcard : ∀ y, Fintype.card (fiber reveal y) = k)
    (E : ι → Ω → Prop) (Ebar : ι → Y → Prop)
    (hE : ∀ i x, E i x ↔ Ebar i (reveal x))
    (U : Ω → Prop) (a : ℕ)
    (hconditional : ∀ y, a ≤ eventCountNat Ebar y →
      Finite.density (fun x : fiber reveal y => U x.1) ≤
        (1 / 2 : ℝ) ^ a) :
    Erdos1016.Proof.GraphicalThreshold.eventProbability U ≤
      1 - Erdos1016.Proof.GraphicalThreshold.eventProbability
          (fun x => (a : ℝ) ≤
            Erdos1016.Proof.GraphicalThreshold.eventCount E x) +
        (1 / 2 : ℝ) ^ a := by
  let score : Y → ℕ := eventCountNat Ebar
  have hgeneric := eventProbability_le_complement_high_count_add
    reveal hsurj k hcard U score a (by
      intro y hy
      exact hconditional y (by simpa [score] using hy))
  have hthreshold (x : Ω) :
      ((a : ℝ) ≤ Erdos1016.Proof.GraphicalThreshold.eventCount E x) ↔
        a ≤ score (reveal x) := by
    rw [eventCount_eq_nat_reveal reveal E Ebar hE x]
    exact_mod_cast (Iff.rfl : a ≤ eventCountNat Ebar (reveal x) ↔
      a ≤ eventCountNat Ebar (reveal x))
  have hevents := eventProbability_congr hthreshold
  rw [hevents]
  simpa [score] using hgeneric

end Erdos1016.Proof.RevealedFiberProbability
