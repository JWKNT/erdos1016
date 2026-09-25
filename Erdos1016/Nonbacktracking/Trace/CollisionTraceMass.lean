import Erdos1016.Nonbacktracking.Girth.CollisionGeometry
import Erdos1016.Nonbacktracking.Girth.CollisionMassBound
import Erdos1016.Nonbacktracking.Trace.ClosedTailTraceBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CollisionTraceMass

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.CyclicRunCollisionGeometry
open Erdos1016.Proof.HighGirthCollisionArithmetic

variable (G : Erdos1016.PhysicalGraph)

/-- The collision slice's normalized ordinary run mass is exactly the
ordinary closed endpoint-run mass used by the graph-tail estimate. -/
theorem V_eq_ordinaryClosedRunMass (a : ℕ) :
    V G a = ordinaryClosedRunMass (G := G) a := by
  unfold V ordinaryClosedRunCount ordinaryClosedRunMass
  rw [div_pow, one_pow]
  rw [div_eq_mul_inv]
  ring

/-- The existing graph-side closed-run estimate and collision slice bound
combine to give the aggregate collision error in terms of the normalized
nonbacktracking trace mass. The only non-analytic premise is the graph-specific
per-length split-count estimate `hraw`. -/
theorem collision_error_le_of_split_counts
    (L s : ℕ)
    (hdegree : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hgirth : ShortWalks.GirthGreater G.toSimpleGraph s)
    (hraw : ∀ ell ∈ Finset.Icc 1 L, s ≤ ell →
      (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) ≤
        (3 / 2 : ℝ) * (ell : ℝ) * (2 : ℝ) ^ (ell - s) *
          (∑ a ∈ Finset.Icc 1 (ell - 1), V G a)) :
    normalizedCollisionMass (bad G) L ≤
      (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s *
        nonbacktrackingTraceMass (G := G) L := by
  have hS : 0 ≤ nonbacktrackingTraceMass (G := G) L := by
    unfold nonbacktrackingTraceMass
    apply Finset.sum_nonneg
    intro ell hell
    positivity
  have hVnonneg : ∀ a ∈ Finset.Icc 1 L, 0 ≤ V G a := by
    intro a ha
    rw [V_eq_ordinaryClosedRunMass (G := G) a]
    unfold ordinaryClosedRunMass
    positivity
  have hVsum :
      (∑ a ∈ Finset.Icc 1 L, V G a) ≤
        (3 : ℝ) * L * nonbacktrackingTraceMass (G := G) L := by
    calc
      (∑ a ∈ Finset.Icc 1 L, V G a) =
          ∑ a ∈ Finset.Icc 1 L, ordinaryClosedRunMass (G := G) a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact V_eq_ordinaryClosedRunMass (G := G) a
      _ ≤ (3 : ℝ) * L * nonbacktrackingTraceMass (G := G) L :=
        ordinaryClosedRunMass_prefix_le_three_L_nonbacktrackingTraceMass
          (G := G) hdegree L
  have hslice : ∀ ell ∈ Finset.Icc 1 L,
      bad G ell ≤ (3 / 2 : ℝ) * (ell : ℝ) * (1 / 2 : ℝ) ^ s *
        prefixMass (V G) ell := by
    intro ell hell
    by_cases hsle : s ≤ ell
    · have hraw' := hraw ell hell hsle
      exact bad_le_of_split_count G ell s (by omega) hraw'
    · have hellpos : 0 < ell := (Finset.mem_Icc.mp hell).1
      have hcard : Fintype.card (NonsimpleCyclicRuns G ell) = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨?_⟩
        rintro ⟨p, hbad⟩
        have hlen := cyclicRunWalk_length G ell hellpos p
        have hnotnil : ¬ (cyclicRunWalk G ell p).Nil :=
          (SimpleGraph.Walk.not_nil_iff_lt_length).2 (by omega)
        have hlong := reduced_closed_nonempty_length_gt s hgirth
          (cyclicRunWalk G ell p) (cyclicRunWalk_reduced G ell p) hnotnil
        omega
      have hprefix : 0 ≤ prefixMass (V G) ell := by
        unfold prefixMass
        apply Finset.sum_nonneg
        intro a ha
        rw [V_eq_ordinaryClosedRunMass (G := G) a]
        unfold ordinaryClosedRunMass
        positivity
      rw [bad, hcard]
      simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (by positivity) hprefix
  exact collision_error_sum_le (V G) (bad G) L s
    (nonbacktrackingTraceMass (G := G) L) hS hVnonneg hVsum hslice

end Erdos1016.Proof.CollisionTraceMass

end
