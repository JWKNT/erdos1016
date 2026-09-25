import Erdos1016.Cycles.Counting.SimpleRunWeight

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.TraceCycleMass

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.CyclicRunCollisionSlice
open Erdos1016.Proof.SimpleRunMass
open Erdos1016.Proof.SimpleRunWeight

variable (G : PhysicalGraph)

/-- The relative trace estimate for collision runs, followed by the
root/orientation fiber bound, gives a lower bound on the total physical
cycle-word mass in the length range. -/
theorem cycleWordMass_sum_ge_one_sub_collisionError_of_max_degree (L s D : ℕ)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) *
        nonbacktrackingTraceMass (G := G) L ≤
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell := by
  exact (simpleCyclicRunMass_ge_one_sub_collisionError_of_max_degree
      (G := G) L s D hmax hg hshort hs).trans
    (simpleCyclicRunMass_le_lengthIndexedCycleWordMass G L)


/-- Compatibility form of the stronger maximum-degree-only bound. -/
theorem cycleWordMass_sum_ge_one_sub_collisionError (L s D : ℕ)
    (_hmin : ∀ v : G.Vertex, 2 ≤ G.degree v)
    (hmax : ∀ v : G.Vertex, G.degree v ≤ 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s) :
    (1 - (9 / 4 : ℝ) * (L : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) *
        nonbacktrackingTraceMass (G := G) L ≤
      ∑ ell ∈ Finset.Icc 1 L, cycleWordMassAtLength G ell  := by
  exact cycleWordMass_sum_ge_one_sub_collisionError_of_max_degree G L s D hmax hg hshort hs

end Erdos1016.Proof.TraceCycleMass

end
