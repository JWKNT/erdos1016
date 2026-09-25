import Erdos1016.Cycles.Counting.FixedLengthVertexMass
import Erdos1016.Cycles.Filtering.ReturnMassAccounting
import Erdos1016.Cycles.Filtering.ReturnRunCounts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The high-girth endpoint and per-vertex cycle-weight bounds, with no
 minimum-degree condition. -/
noncomputable section
namespace Erdos1016.Proof.LowDegreeVertexMass
open scoped BigOperators
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.FixedLengthVertexMass
open Erdos1016.Proof.ExternalReturnFilter

/-- Equation (6), on the literal fixed-endpoint run set. A run of a edges
 has a-1 transitions in the existing representation. -/
theorem normalized_endpoint_mass_le (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (D a s : ℕ) (u v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsa : s < a) (hshort : 2 * s ≤ D) :
    (Fintype.card (EndpointRuns G (a - 1) u v) : ℝ) * (1 / 2 : ℝ) ^ a ≤
      (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
  exact one_length_suffix_mass_le a s _ hsa
    (endpointRuns_card_le_suffix_budget_of_max_degree G hmax D a s u v hg hs hsa hshort)

theorem cycle_length_gt_of_girth (G : PhysicalGraph) (D : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) (C : G.CycleWord) :
    D < BoundaryDecay.Cycle.length C := by
  obtain ⟨u, p, hp, rfl⟩ := exists_cycle_walk_of_cycleWord G C
  rw [cycleWordOfWalk_length]
  exact hg u p hp

/-- At every fixed length the cycle mass through a vertex is bounded by
 the high-girth suffix factor. Choosing one orientation already suffices. -/
theorem cycle_mass_at_vertex_le (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (D ell s : ℕ) (v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) :
    ((cyclesAtVertex G ell v).card : ℝ) * (1 / 2 : ℝ) ^ ell ≤
      (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
  classical
  by_cases hsa : s < ell
  · let f : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v} →
        EndpointRuns G (ell - 1) v v := fun C => encodeCyclePrefixAtVertex G ell v C false
    have hf : Function.Injective f := by
      intro C E h
      have hpair : (C, false) = (E, false) :=
        @encodeCyclePrefixAtVertex_injective G ell v (C, false) (E, false) h
      exact congrArg Prod.fst hpair
    have hcard : (cyclesAtVertex G ell v).card ≤
        Fintype.card (EndpointRuns G (ell - 1) v v) := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ell)).trans
      (normalized_endpoint_mass_le G hmax D ell s v v hg hs hsa hshort)
  · have hempty : cyclesAtVertex G ell v = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro C hC
      have hlen := cycle_length_gt_of_girth G D hg C.1
      have hlen' : BoundaryDecay.Cycle.length C.1 = ell := C.2
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

/-- Summing the fixed-vertex bound over the positive lengths through L
 yields precisely the O(L 2^-s) load used in the exceptional-pair estimate. -/
theorem lengthIndexed_vertex_mass_le (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (D L s : ℕ) (v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hshort : 2 * s ≤ D) :
    (∑ ell ∈ Finset.Icc 1 L,
      ((cyclesAtVertex G ell v).card : ℝ) * (1 / 2 : ℝ) ^ ell) ≤
      (3 / 2 : ℝ) * L * (1 / 2 : ℝ) ^ s := by
  calc
    _ ≤ ∑ _ell ∈ Finset.Icc 1 L, (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ s := by
      exact Finset.sum_le_sum fun ell _ => cycle_mass_at_vertex_le G hmax D ell s v hg hs hshort
    _ = _ := by simp; ring

end Erdos1016.Proof.LowDegreeVertexMass
