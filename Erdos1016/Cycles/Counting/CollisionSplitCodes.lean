import Erdos1016.Nonbacktracking.Girth.CollisionSlices

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CollisionSplitCodes

open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Nonbacktracking



/-- Lengths that can serve as the first arc in the split encoding. The
complementary arc has enough transitions to retain a prefix after deleting a
suffix of length `s`. -/
abbrev SplitLength (ell s : ℕ) :=
  {a : Fin ell // 1 ≤ a.val ∧ s < ell - a.val}

/-- A code for a split at length `a`: the first closed arc, followed by the
initial prefix of the complementary arc. The latter's final `s` transitions
are recoverable from girth uniqueness once the terminal vertex is fixed. -/
abbrev SplitCodeFiber (G : PhysicalGraph) (ell s : ℕ)
    (a : SplitLength ell s) :=
  Σ u : ClosedEndpointRuns (G := G) (a.val - 1),
    StartingRuns G (ell - a.val - s - 1) (tail G u.1.1)

/-- The subcubic prefix estimate bounds each split-code fiber by the number
of choices for its closed first arc times the number of complementary
prefixes. This is the fiber-counting part of the collision injection. -/
theorem splitCodeFiber_card_le
    (G : PhysicalGraph) (ell s : ℕ)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (a : SplitLength ell s) :
    Fintype.card (SplitCodeFiber G ell s a) ≤
      Fintype.card (ClosedEndpointRuns (G := G) (a.val - 1)) *
        (3 * 2 ^ (ell - a.val - s - 1)) := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ u : ClosedEndpointRuns (G := G) (a.val - 1),
        Fintype.card (StartingRuns G (ell - a.val - s - 1) (tail G u.1.1))) ≤
      ∑ _u : ClosedEndpointRuns (G := G) (a.val - 1),
        3 * 2 ^ (ell - a.val - s - 1) := by
          apply Finset.sum_le_sum
          intro u hu
          exact startingRuns_card_le_suffix_budget G hmin hmax
            (ell - a.val) s (tail G u.1.1)
    _ = Fintype.card (ClosedEndpointRuns (G := G) (a.val - 1)) *
          (3 * 2 ^ (ell - a.val - s - 1)) := by simp

/-- Exact finite-type target for the remaining graph-specific injection:
choose a cyclic split position, its shorter closed arc, and the prefix of the
longer complementary arc. -/
abbrev PositionedSplitCodeFiber (G : PhysicalGraph) (ell s : ℕ)
    (a : SplitLength ell s) :=
  Fin ell × SplitCodeFiber G ell s a

/-- Including the choice of cyclic split position contributes the required
factor `ell` to the preceding fiber estimate. -/
theorem positionedSplitCodeFiber_card_le
    (G : PhysicalGraph) (ell s : ℕ)
    (hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (a : SplitLength ell s) :
    Fintype.card (PositionedSplitCodeFiber G ell s a) ≤
      ell * Fintype.card (ClosedEndpointRuns (G := G) (a.val - 1)) *
        (3 * 2 ^ (ell - a.val - s - 1)) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    ell * Fintype.card (SplitCodeFiber G ell s a) ≤
        ell * (Fintype.card (ClosedEndpointRuns (G := G) (a.val - 1)) *
          (3 * 2 ^ (ell - a.val - s - 1))) :=
      Nat.mul_le_mul_left ell (splitCodeFiber_card_le G ell s hmin hmax a)
    _ = ell * Fintype.card (ClosedEndpointRuns (G := G) (a.val - 1)) *
        (3 * 2 ^ (ell - a.val - s - 1)) := by ring

/-- Once the split map is injective, fiber estimates sum to a global bound.
For the paper's `hraw`, instantiate `weight a` by the closed-arc count times
the subcubic prefix budget, and prove the final scalar sum algebraically. -/
theorem card_bad_runs_le_of_positioned_split_code
    (G : PhysicalGraph) (ell s : ℕ)
    (code : NonsimpleCyclicRuns G ell →
      Σ a : SplitLength ell s, PositionedSplitCodeFiber G ell s a)
    (hcode : Function.Injective code)
    (weight : SplitLength ell s → ℝ)
    (hfiber : ∀ a, (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) ≤
      weight a)
    (target : ℝ)
    (hsum : (∑ a, weight a) ≤ target) :
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤ target := by
  have hcard := Fintype.card_le_of_injective code hcode
  have hcast : (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
      (Fintype.card (Σ a : SplitLength ell s,
        PositionedSplitCodeFiber G ell s a) : ℝ) := by exact_mod_cast hcard
  have hsigma : (Fintype.card (Σ a : SplitLength ell s,
        PositionedSplitCodeFiber G ell s a) : ℝ) =
      ∑ a, (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) := by
    rw [Fintype.card_sigma]
    norm_cast
  calc
    (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
        (Fintype.card (Σ a : SplitLength ell s,
          PositionedSplitCodeFiber G ell s a) : ℝ) := hcast
    _ = ∑ a, (Fintype.card (PositionedSplitCodeFiber G ell s a) : ℝ) := hsigma
    _ ≤ ∑ a, weight a := by
      apply Finset.sum_le_sum
      intro a ha
      exact hfiber a
    _ ≤ target := hsum

end Erdos1016.Proof.CollisionSplitCodes

end
