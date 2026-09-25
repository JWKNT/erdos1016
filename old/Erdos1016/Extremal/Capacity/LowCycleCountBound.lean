import Erdos1016.Extremal.Capacity.PointwiseTailBounds
import Erdos1016.Extremal.Capacity.Basic

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Extremal

open Erdos1016

/-- The finite supremum defining `initialCapacity` is attained by a graph.
This makes explicit the extremal realization chosen in the paper's pointwise
recurrence proof. -/
theorem exists_initialCapacity_realizer (r : ℕ) :
    ∃ G : PhysicalGraph,
      G.cycleRank ≤ r ∧ G.InitialCoverage (initialCapacity r) := by
  classical
  let S := (Finset.range (2 ^ r + 2)).filter fun L =>
    ∃ H : PhysicalGraph, H.cycleRank ≤ r ∧ H.InitialCoverage L
  have hS : S.Nonempty := by
    refine ⟨2, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    have hp : 0 < 2 ^ r := pow_pos (by decide) _
    refine ⟨by omega, ?_⟩
    refine ⟨capacityEmptyGraph, ?_, ?_⟩
    · rw [capacityEmptyGraph_rank]
      exact Nat.zero_le r
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      omega
  obtain ⟨L, hL, hsup⟩ := Finset.exists_mem_eq_sup S hS id
  have hLcap : L = initialCapacity r := by
    simpa [S, initialCapacity] using hsup.symm
  obtain ⟨G, hGr, hcov⟩ := (Finset.mem_filter.mp hL).2
  exact ⟨G, hGr, hLcap ▸ hcov⟩

/-- A graph realizing `I(r)` with fewer than half the tail's normalized
number of distinct cycle lengths forces the easy low-count branch of the
pointwise recurrence. The realization hypothesis is explicit so the bound is
not silently inferred for unrelated graphs. -/
theorem low_cycle_count_forces_capacity_bound
    (R r : ℕ) (hR : 5 ≤ R) (G : PhysicalGraph)
    (hcov : G.InitialCoverage (initialCapacity r))
    (hsmall : (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r <
      tailCapacity R / 2) :
    initialCapacityExcess r ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R := by
  have hI2 : 2 ≤ initialCapacity r := initialCapacity_two_le r
  have hcard : initialCapacity r - 2 ≤ G.cycleLengths.card := by
    have h := Finset.card_le_card hcov
    simpa only [Nat.card_Icc] using h
  have hcardReal : ((initialCapacity r - 2 : ℕ) : ℝ) ≤
      (G.cycleLengths.card : ℝ) := by exact_mod_cast hcard
  have hnum : (initialCapacity r : ℝ) - 2 ≤
      (G.cycleLengths.card : ℝ) := by
    simpa [Nat.cast_sub hI2] using hcardReal
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hbound : initialCapacityExcess r ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ r := by
    unfold initialCapacityExcess
    exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
  have hphi : 0 ≤ tailCapacity R := tailCapacity_bounds R |>.1
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hfactor : 1 / 2 ≤ (1 / 2 : ℝ) + 1 / (R : ℝ) := by
    have hInv : 0 ≤ 1 / (R : ℝ) := by positivity
    linarith
  have hhalf : tailCapacity R / 2 ≤
      ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R := by
    nlinarith [mul_le_mul_of_nonneg_right hfactor hphi]
  exact hbound.trans ((le_of_lt hsmall).trans hhalf)



end Erdos1016.Extremal
