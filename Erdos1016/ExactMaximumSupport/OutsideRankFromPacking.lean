import Erdos1016.ExactMaximumSupport.IntervalCyclePacking
import Erdos1016.ExactMaximumSupport.PoleCyclePacking

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Exterior rank from actual cyclic intervals

A maximal family of small cyclic intervals leaves a physical forest.
Choose one actual cycle in each interval. The forest-density packing bound
controls their number, and vertex deletion then controls the exterior rank.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.OutsideRankFromPacking
open FiniteMultiGraph ThinIntervalBoundary

local instance outsideRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The local small-interval property and the actual forest margin bound exterior rank. -/
theorem rank_le_of_local_intervals (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (level : G.Vertex → ℤ) (L : ℕ) (hloop : G.IsLoopless)
    (hG : G.toSimpleGraph.Connected) (hdegree : ∀ v, G.degree v ≤ 3)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e) + 1 ∧
      level (G.dst e) ≤ level (G.src e) + 1)
    (hlocal : ∀ a b : ℤ, G.HasCycleIn (region G P level a b) →
      ∃ c d : ℤ, region G P level c d ⊆ region G P level a b ∧
        (region G P level c d).card ≤ L ∧ G.HasCycleIn (region G P level c d))
    (hforest : (501 / 1000 : ℝ) ≤ Finite.density (fun z : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges Pᶜ) z.1))) :
    (LargeGirth.PieceCore.Induced.graph G Pᶜ).cycleRank ≤
      2 * L * (1000 * (L + 1) * 2 ^ L) := by
  classical
  obtain ⟨F, hF, hdisj, hout, hrem⟩ :=
    IntervalCyclePacking.exists_packing_with_forest_remainder G P level L hloop hlevel hlocal
  let I := {R : Finset G.Vertex // R ∈ F}
  have hcycles (i : I) : ∃ z : G.EdgeWord, G.IsCycleWord z ∧ G.SupportedIn z i.1 :=
    (hF i.1 i.2).2.2
  choose Z hZ hsupport using hcycles
  have hsub (i : I) : CycleRegions.region G (Z i) ⊆ i.1 :=
    MinimalCyclicInterval.cycle_region_subset_of_supported G (Z i) i.1 (hsupport i)
  have hcycle_disj : Pairwise fun i j : I =>
      Disjoint (CycleRegions.region G (Z i)) (CycleRegions.region G (Z j)) := by
    intro i j hij
    apply (hdisj i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))).mono (hsub i) (hsub j)
  have hcycle_out (i : I) : Disjoint (CycleRegions.region G (Z i)) P := by
    apply Finset.disjoint_left.mpr
    intro v hv hp
    have hvi : v ∈ F.biUnion id := Finset.mem_biUnion.mpr ⟨i.1, i.2, hsub i hv⟩
    exact Finset.mem_compl.mp (hout hvi) hp
  have hlength (i : I) : G.wordLength (Z i) ≤ L := by
    rw [← CycleRegions.cycle_region_card G (Z i) (hZ i)]
    exact (Finset.card_le_card (hsub i)).trans (hF i.1 i.2).2.1
  have hcard := PoleCyclePacking.card_le_of_exterior_probability G hG hdegree
    Z hZ hcycle_disj P hcycle_out L hlength hforest
  have hFcard : F.card ≤ 1000 * (L + 1) * 2 ^ L := by
    simpa only [I, Fintype.card_coe] using hcard
  exact (IntervalCyclePacking.exterior_rank_le G P level L F hloop hdegree hF hrem).trans
    (Nat.mul_le_mul_left (2 * L) hFcard)

end Erdos1016.ExactMaximumSupport.OutsideRankFromPacking
