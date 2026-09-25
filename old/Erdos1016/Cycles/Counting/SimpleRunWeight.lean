import Erdos1016.Cycles.Counting.CycleSupportFibers

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Weighted simple-run to cycle-word comparison

At each length, simple cyclic runs are partitioned by their physical cycle
word. The existing root/orientation fiber bound gives the cycle-word mass
upper bound needed in the trace-to-cycle argument.
-/

noncomputable section
namespace Erdos1016.Proof.SimpleRunWeight

open Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.SimpleRunMass
open Erdos1016.Proof.CycleSupportFibers
open scoped BigOperators

variable (G : PhysicalGraph)

/-- Cycle-word mass at one fixed length. -/
def cycleWordMassAtLength (ell : ℕ) : ℝ :=
  (Fintype.card (CycleWordsAtLength G ell) : ℝ) * (1 / 2 : ℝ) ^ ell

/-- Every simple cyclic run maps to its length-indexed cycle word. The fiber
bound `simpleRunFiber_card_le` therefore bounds their total number by `2 ℓ`
times the number of cycle words. -/
theorem simpleCyclicRuns_card_le_cycleWords (ell : ℕ) (hell : 0 < ell) :
    Fintype.card (simpleCyclicRuns G ell) ≤
      2 * ell * Fintype.card (CycleWordsAtLength G ell) := by
  classical
  let f : simpleCyclicRuns G ell → CycleWordsAtLength G ell := fun r =>
    ⟨simpleRunCycleWord ell r,
      simpleRunCycleWord_length ell hell r⟩
  have hfiberSum :
      (∑ C : CycleWordsAtLength G ell,
        (Finset.univ.filter fun r : simpleCyclicRuns G ell => f r = C).card) =
        Fintype.card (simpleCyclicRuns G ell) := by
    simpa [f] using
      (Finset.sum_card_fiberwise_eq_card_filter
        (s := (Finset.univ : Finset (simpleCyclicRuns G ell)))
        (t := (Finset.univ : Finset (CycleWordsAtLength G ell))) (g := f))
  have hbound (C : CycleWordsAtLength G ell) :
      (Finset.univ.filter fun r : simpleCyclicRuns G ell => f r = C).card ≤
        2 * ell := by
    let fiber : Finset (simpleCyclicRuns G ell) :=
      Finset.univ.filter fun r => simpleRunCycleWord ell r = C.1
    have hfiber :
        (Finset.univ.filter fun r : simpleCyclicRuns G ell => f r = C) = fiber := by
      ext r
      simp [fiber, f, Subtype.ext_iff]
    rw [hfiber]
    letI : Fintype (simpleCyclicRuns G ell) := simpleCyclicRunsFintype G ell
    letI : Fintype {r : simpleCyclicRuns G ell // r ∈ fiber} := Fintype.subtype fiber (by
      intro r
      simp [fiber])
    let efiber : SimpleRunFiber ell C ≃
        {r : simpleCyclicRuns G ell // r ∈ fiber} :=
      Equiv.subtypeEquivRight (fun r => by simp [SimpleRunFiber, fiber])
    have hcard : Fintype.card (SimpleRunFiber ell C) = fiber.card := by
      calc
        Fintype.card (SimpleRunFiber ell C) =
            Fintype.card {r : simpleCyclicRuns G ell // r ∈ fiber} :=
          Fintype.card_congr efiber
        _ = fiber.card := by simp
    rw [← hcard]
    exact simpleRunFiber_card_le ell hell C
  calc
    Fintype.card (simpleCyclicRuns G ell) =
        ∑ C : CycleWordsAtLength G ell,
          (Finset.univ.filter fun r : simpleCyclicRuns G ell => f r = C).card :=
      hfiberSum.symm
    _ ≤ ∑ _C : CycleWordsAtLength G ell, 2 * ell :=
      Finset.sum_le_sum fun C _ => hbound C
    _ = 2 * ell * Fintype.card (CycleWordsAtLength G ell) := by
      simp [mul_comm]

/-- The normalized simple-run mass at fixed length is at most the physical
cycle-word mass at that length. -/
theorem simpleCyclicRunMassAtLength_le_cycleWordMassAtLength
    (ell : ℕ) (hell : 0 < ell) :
    (Fintype.card (simpleCyclicRuns G ell) : ℝ) /
        ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) ≤
      cycleWordMassAtLength G ell := by
  have hcard := simpleCyclicRuns_card_le_cycleWords G ell hell
  have hcardR : (Fintype.card (simpleCyclicRuns G ell) : ℝ) ≤
      2 * (ell : ℝ) * (Fintype.card (CycleWordsAtLength G ell) : ℝ) := by
    exact_mod_cast hcard
  have hden : (0 : ℝ) < (2 * (ell : ℝ)) * (2 : ℝ) ^ ell := by positivity
  apply (div_le_iff₀ hden).2
  unfold cycleWordMassAtLength
  calc
    (Fintype.card (simpleCyclicRuns G ell) : ℝ) ≤
        2 * (ell : ℝ) * (Fintype.card (CycleWordsAtLength G ell) : ℝ) := hcardR
    _ = ((Fintype.card (CycleWordsAtLength G ell) : ℝ) *
        (1 / 2 : ℝ) ^ ell) * ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) := by
          have hinv : (1 / 2 : ℝ) ^ ell * (2 : ℝ) ^ ell = 1 := by
            rw [← mul_pow]
            norm_num
          calc
            _ = (Fintype.card (CycleWordsAtLength G ell) : ℝ) *
                ((2 * (ell : ℝ)) * 1) := by ring
            _ = (Fintype.card (CycleWordsAtLength G ell) : ℝ) *
                ((2 * (ell : ℝ)) * ((1 / 2 : ℝ) ^ ell * (2 : ℝ) ^ ell)) := by
                  rw [hinv]
            _ = ((Fintype.card (CycleWordsAtLength G ell) : ℝ) *
                (1 / 2 : ℝ) ^ ell) * ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) := by ring

/-- Summing over the finite length interval gives the trace-to-cycle mass
comparison in length-indexed form. -/
theorem simpleCyclicRunMass_le_lengthIndexedCycleWordMass
    (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L,
      (Fintype.card (simpleCyclicRuns G ell) : ℝ) /
        ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) ≤
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell := by
  apply Finset.sum_le_sum
  intro ell hell
  exact simpleCyclicRunMassAtLength_le_cycleWordMassAtLength G ell
    (Finset.mem_Icc.mp hell).1

end Erdos1016.Proof.SimpleRunWeight

end
