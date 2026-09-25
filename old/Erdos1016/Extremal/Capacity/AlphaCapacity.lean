import Erdos1016.Extremal.Capacity.LinearForestCapacity
import Erdos1016.Extremal.CompleteGraphWitness
import Erdos1016.Extremal.PancyclicGraphTransfer

set_option autoImplicit false

/-!
# Global local-capacity envelope

This defines the paper's `α(L)` using the existing physical local-capacity
quantity. The finite restriction bridge relating this envelope to the global
cycle-capacity function is not proved here.
-/

noncomputable section
namespace Erdos1016
namespace PhysicalGraph

/-- The real local capacities of physical graphs covering all cycle lengths
from three through `L`. -/
def alphaCapacitySet (L : ℕ) : Set ℝ :=
  {a | ∃ G : PhysicalGraph, G.InitialCoverage L ∧
    a = G.normalizedLinearForestCapacity}

/-- The paper's global `α(L)`, as the supremum of local forest capacities
among graphs with initial coverage through `L`. -/
def alphaCapacity (L : ℕ) : ℝ := sSup (alphaCapacitySet L)

theorem alphaCapacitySet_nonempty (L : ℕ) : (alphaCapacitySet L).Nonempty := by
  let n := max L 3
  have hn : 3 ≤ n := by dsimp [n]; exact le_max_right _ _
  have hLn : L ≤ n := by dsimp [n]; exact le_max_left _ _
  let G : SimpleGraph (Fin n) := completeGraph (Fin n)
  have hpan : Problem1016.IsPancyclic G :=
    Problem1016.completeGraph_isPancyclic n
  let H : PhysicalGraph := Problem1016.physicalOfSimpleGraph G
  have hphys := Problem1016.final_isPancyclic_of_isPancyclic G hn hpan
  have hcoverage : H.InitialCoverage n := by
    simpa [H] using hphys.2.2
  have hcoverageL : H.InitialCoverage L := by
    intro k hk
    apply hcoverage
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
      (Finset.mem_Icc.mp hk).2.trans hLn⟩
  exact ⟨H.normalizedLinearForestCapacity, H, hcoverageL, rfl⟩

theorem alphaCapacitySet_bddAbove (L : ℕ) : BddAbove (alphaCapacitySet L) := by
  refine ⟨1, ?_⟩
  rintro a ⟨G, _, rfl⟩
  exact G.normalizedLinearForestCapacity_le_one

/-- Every `α(L)` is a genuine real number in `[0,1]`. -/
theorem alphaCapacity_bounds (L : ℕ) : 0 ≤ alphaCapacity L ∧ alphaCapacity L ≤ 1 := by
  constructor
  · unfold alphaCapacity
    obtain ⟨a, ha⟩ := alphaCapacitySet_nonempty L
    have hnonneg : 0 ≤ a := by
      rcases ha with ⟨G, _, rfl⟩
      exact le_of_lt G.normalizedLinearForestCapacity_pos
    exact hnonneg.trans (le_csSup (alphaCapacitySet_bddAbove L) ha)
  · unfold alphaCapacity
    apply csSup_le (alphaCapacitySet_nonempty L)
    rintro a ⟨G, _, rfl⟩
    exact G.normalizedLinearForestCapacity_le_one

theorem alphaCapacitySet_antitone {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    alphaCapacitySet L₂ ⊆ alphaCapacitySet L₁ := by
  rintro a ⟨G, hG, rfl⟩
  refine ⟨G, ?_, rfl⟩
  intro k hk
  apply hG
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
    (Finset.mem_Icc.mp hk).2.trans h⟩



end PhysicalGraph
end Erdos1016
