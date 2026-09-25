import Erdos1016.Cycles.Counting.CollisionCharging
import Erdos1016.Cycles.Counting.RootedCyclicRunInjection

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.SimpleRunMass

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.RootedCyclicRunInjection
open Erdos1016.Proof.HighGirthCollisionArithmetic
open Erdos1016.Proof.CollisionCharging

variable (G : PhysicalGraph)

def simpleCyclicRuns (ell : ℕ) :=
  {p : CyclicRuns G ell // (cyclicRunWalk G ell p).IsCycle}

noncomputable instance simpleCyclicRunsFintype (ell : ℕ) : Fintype (simpleCyclicRuns G ell) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun p : CyclicRuns G ell =>
    (cyclicRunWalk G ell p).IsCycle) (by intro p; simp [simpleCyclicRuns])

theorem cyclicRuns_card_eq_simple_add_bad (ell : ℕ) :
    Fintype.card (CyclicRuns G ell) =
      Fintype.card (simpleCyclicRuns G ell) + Fintype.card (NonsimpleCyclicRuns G ell) := by
  classical
  letI : Fintype (simpleCyclicRuns G ell) := simpleCyclicRunsFintype G ell
  have hc := Fintype.card_subtype_compl
    (α := CyclicRuns G ell) (p := fun p => (cyclicRunWalk G ell p).IsCycle)
  have hle : Fintype.card (simpleCyclicRuns G ell) ≤ Fintype.card (CyclicRuns G ell) :=
    Fintype.card_subtype_le _
  have hbad : Fintype.card (NonsimpleCyclicRuns G ell) =
      Fintype.card (CyclicRuns G ell) - Fintype.card (simpleCyclicRuns G ell) := by
    simpa [NonsimpleCyclicRuns, simpleCyclicRuns] using hc
  omega

theorem closedRunCount_le_cyclicRuns_card (ell : ℕ) (hell : 0 < ell) :
    closedRunCount G ell ≤ Fintype.card (CyclicRuns G ell) := by
  classical
  letI : Fintype (ClosedDartRun (G := G) ell) := inferInstance
  have hcard : Fintype.card (ClosedDartRun (G := G) ell) = closedRunCount G ell := by
    simp [ClosedDartRun, closedRunCount, Fintype.card_sigma]
  rw [← hcard]
  exact Fintype.card_le_of_injective (closedDartRunToCyclic (G := G) ell hell)
    (closedDartRunToCyclic_injective (G := G) ell hell)

/-- The raw trace splits below into simple cyclic runs and collision runs,
with the paper's exact `2 ell 2^ell` normalization. -/
theorem traceMass_le_simplePlusBad (L : ℕ) :
    nonbacktrackingTraceMass (G := G) L ≤
      (∑ ell ∈ Finset.Icc 1 L,
        (Fintype.card (simpleCyclicRuns G ell) : ℝ) /
          ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) +
      (∑ ell ∈ Finset.Icc 1 L,
        (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) /
          ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) := by
  unfold nonbacktrackingTraceMass
  calc
    _ ≤ ∑ ell ∈ Finset.Icc 1 L,
        ((Fintype.card (simpleCyclicRuns G ell) : ℝ) +
          (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ)) /
          ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) := by
      apply Finset.sum_le_sum
      intro ell hell
      have hpos : 0 < ell := (Finset.mem_Icc.mp hell).1
      have hcardN := closedRunCount_le_cyclicRuns_card (G := G) ell hpos
      have hsplit := cyclicRuns_card_eq_simple_add_bad (G := G) ell
      have hcard : closedRunCount G ell ≤
          Fintype.card (simpleCyclicRuns G ell) + Fintype.card (NonsimpleCyclicRuns G ell) :=
        hcardN.trans_eq hsplit
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by
      simp_rw [add_div]
      rw [Finset.sum_add_distrib]

/-- The nonsimple cyclic-run term uses precisely the normalized collision
mass from the Section 6 charging argument. -/
theorem nonsimpleTraceTerm_eq_collisionMass (L : ℕ) :
    (∑ ell ∈ Finset.Icc 1 L,
      (Fintype.card (NonsimpleCyclicRuns G ell) : ℝ) /
        ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell)) =
      normalizedCollisionMass (bad G) L := by
  unfold normalizedCollisionMass
  apply Finset.sum_congr rfl
  intro ell hell
  rw [bad]
  have hp : (1 / 2 : ℝ) ^ ell = ((2 : ℝ) ^ ell)⁻¹ := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
  rw [hp]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The collision estimate therefore leaves at least its relative complement
of the trace mass among simple cyclic runs. -/
theorem simpleCyclicRunMass_ge_one_sub_collisionError (L s D : ℕ)
    (hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) *
        nonbacktrackingTraceMass (G := G) L ≤
      ∑ ell ∈ Finset.Icc 1 L,
        (Fintype.card (simpleCyclicRuns G ell) : ℝ) /
          ((2 * (ell : ℝ)) * (2 : ℝ) ^ ell) := by
  have hsplit := traceMass_le_simplePlusBad (G := G) L
  rw [nonsimpleTraceTerm_eq_collisionMass (G := G) L] at hsplit
  have hcollision := normalizedCollisionMass_le_trace (G := G) L s D
    hmin hmax hg hshort hs
  linarith

end Erdos1016.Proof.SimpleRunMass
end
