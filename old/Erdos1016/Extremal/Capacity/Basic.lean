import Erdos1016.Extremal.Capacity.CycleLengths

set_option autoImplicit false

noncomputable section
namespace Erdos1016

/-- Capacity is monotone in the allowed cycle rank. -/
theorem initialCapacity_mono {r s : ℕ} (hrs : r ≤ s) :
    initialCapacity r ≤ initialCapacity s := by
  classical
  unfold initialCapacity
  apply Finset.sup_le
  intro L hL
  have hfilter := Finset.mem_filter.1 hL
  have hrange := Finset.mem_range.1 hfilter.1
  obtain ⟨G, hGr, hcoverage⟩ := hfilter.2
  have hpow : (2 : ℕ) ^ r ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hrs
  have hrange' : L ∈ Finset.range (2 ^ s + 2) :=
    Finset.mem_range.2 (lt_of_lt_of_le hrange (by omega))
  have hmem : L ∈ (Finset.range (2 ^ s + 2)).filter
      (fun q => ∃ H : PhysicalGraph, H.cycleRank ≤ s ∧ H.InitialCoverage q) := by
    refine Finset.mem_filter.2 ⟨hrange', ?_⟩
    exact ⟨G, hGr.trans hrs, hcoverage⟩
  exact Finset.le_sup (f := id) hmem

/-- A rank-zero empty graph witnesses the harmless base value two, whose
initial coverage interval is empty. This keeps logarithmic capacity arguments
away from the zero case. -/
def capacityEmptyGraph : PhysicalGraph where
  vertexCount := 0
  edgeCount := 0
  src := Fin.elim0
  dst := Fin.elim0
  noLoops e := Fin.elim0 e
  simple e := Fin.elim0 e

theorem capacityEmptyGraph_rank : capacityEmptyGraph.cycleRank = 0 := by
  unfold PhysicalGraph.cycleRank
  haveI : Subsingleton capacityEmptyGraph.Word :=
    ⟨fun f g => funext (fun e => Fin.elim0 e)⟩
  haveI : Subsingleton capacityEmptyGraph.CycleSpace := inferInstance
  exact Module.finrank_zero_of_subsingleton

theorem two_le_initialCapacity (r : ℕ) : 2 ≤ initialCapacity r := by
  apply coverage_le_initialCapacity capacityEmptyGraph
  · rw [capacityEmptyGraph_rank]
    omega
  · intro n hn
    have h := Finset.mem_Icc.1 hn
    omega

end Erdos1016
