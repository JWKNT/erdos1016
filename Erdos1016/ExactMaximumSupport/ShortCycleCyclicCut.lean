import Erdos1016.ExactMaximumSupport.CycleRegions
import Erdos1016.ExactMaximumSupport.VertexRankDeletion
import Erdos1016.ExactMaximumSupport.MinimalCyclicInterval

set_option autoImplicit false

/-!
# A short physical cycle gives a small cyclic cut at sufficiently large rank

Deleting a cycle region loses at most twice its number of vertices. If the
ambient rank exceeds twice the cycle length, the complement still contains
an actual supported cycle. The cut uses physical labels and retains parallels.
Connectivity is unnecessary.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut

open FiniteMultiGraph LargeGirth

/-- Positive rank in the actual induced labelled graph yields an ambient cycle
supported in that vertex region. -/
theorem hasCycleIn_of_induced_rank_pos (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (R : Finset G.Vertex) (hr : 0 < (PieceCore.Induced.graph G R).cycleRank) :
    G.HasCycleIn R := by
  apply MinimalCyclicInterval.hasCycleIn_of_not_forest G hloop R
  intro hf
  have hz := VertexRankDeletion.induced_rank_eq_zero_of_forest G R hf
  omega

/-- The literal support of a short cycle is a cyclic cut with no more crossing
labels than the cycle length bound. -/
theorem cycle_region_cyclic_cut (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (hdegree : ∀ v, G.degree v ≤ 3) (z : G.EdgeWord) (hz : G.IsCycleWord z)
    (d : ℕ) (hd : G.wordLength z ≤ d) (hr : 2 * d < G.cycleRank) :
    G.IsCyclicCut (CycleRegions.region G z) ∧
      (G.cutEdges (CycleRegions.region G z)).card ≤ d := by
  have hcard := CycleRegions.cycle_region_card G z hz
  have hdel := VertexRankDeletion.rank_le_exterior_add_twice_card G
    (CycleRegions.region G z) hloop (fun v _ => hdegree v)
  have hpos : 0 < (PieceCore.Induced.graph G (CycleRegions.region G z)ᶜ).cycleRank := by
    omega
  refine ⟨⟨?_, hasCycleIn_of_induced_rank_pos G hloop _ hpos⟩,
    (CycleRegions.cycle_cut_le_length G z hz hdegree).trans hd⟩
  refine ⟨z, hz, ?_⟩
  intro e he
  exact ⟨(CycleRegions.mem_region G z _).mpr (G.selectedDegree_src_pos he),
    (CycleRegions.mem_region G z _).mpr (G.selectedDegree_dst_pos he)⟩

/-- A cycle of length at most `d` forces a cyclic cut of size at most `d`
when the physical cycle rank is greater than `2*d`. -/
theorem hasCyclicCutLE_of_cycle (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (hdegree : ∀ v, G.degree v ≤ 3) (z : G.EdgeWord) (hz : G.IsCycleWord z)
    (d : ℕ) (hd : G.wordLength z ≤ d) (hr : 2 * d < G.cycleRank) :
    G.HasCyclicCutLE d :=
  ⟨CycleRegions.region G z, cycle_region_cyclic_cut G hloop hdegree z hz d hd hr⟩

/-- In rank at least nine, an actual cycle of length at most four gives an
actual cyclic cut of at most four physical labels. -/
theorem hasCyclicCutLE_four_of_rank_ge_nine (G : FiniteMultiGraph)
    (hloop : G.IsLoopless) (hdegree : ∀ v, G.degree v ≤ 3)
    (z : G.EdgeWord) (hz : G.IsCycleWord z) (hd : G.wordLength z ≤ 4)
    (hr : 9 ≤ G.cycleRank) : G.HasCyclicCutLE 4 :=
  hasCyclicCutLE_of_cycle G hloop hdegree z hz 4 hd (by omega)

end Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut
