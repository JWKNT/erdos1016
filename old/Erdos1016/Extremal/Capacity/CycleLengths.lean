import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# The elementary capacity bound

Cycle lengths inject only after choosing one cycle at each length. We instead
bound the image of all circuit words by all nonzero even words. This keeps
physical-state counting separate from distinct-length counting.
-/

noncomputable section

namespace Erdos1016
namespace PhysicalGraph

/-- The complete set of lengths of circuit words in the physical graph. -/
def cycleLengths (G : PhysicalGraph) : Finset ℕ := by
  classical
  exact Finset.univ.image fun c : G.CycleWord => G.wordLength c.1

/-- Contains every simple-cycle length from 3 through `L`. -/
def InitialCoverage (G : PhysicalGraph) (L : ℕ) : Prop :=
  Finset.Icc 3 L ⊆ G.cycleLengths

/-- Pancyclicity is initial coverage through the number of vertices. -/
def IsPancyclic (G : PhysicalGraph) : Prop := G.InitialCoverage G.vertexCount

private def cycleInjection (G : PhysicalGraph) :
    G.CycleWord → {z : G.CycleSpace // z ≠ 0} := fun c =>
  ⟨⟨c.1, c.2.2.1⟩, by
    intro hz
    apply c.2.1
    exact congrArg (fun z : G.CycleSpace => (z : G.Word)) hz⟩

private lemma cycleInjection_injective (G : PhysicalGraph) :
    Function.Injective (cycleInjection G) := by
  intro c d h
  apply Subtype.ext
  exact congrArg
    (fun z : {z : G.CycleSpace // z ≠ 0} => (z.1 : G.Word)) h

lemma cycleWord_card_le (G : PhysicalGraph) :
    Fintype.card G.CycleWord ≤ 2 ^ G.cycleRank - 1 := by
  classical
  have hinj := Fintype.card_le_of_injective
    (cycleInjection G) (cycleInjection_injective G)
  have hnz : Fintype.card {z : G.CycleSpace // z ≠ 0} =
      Fintype.card G.CycleSpace - 1 := by
    rw [Fintype.card_of_subtype (Finset.univ.erase 0)
      (by intro z; simp)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : G.CycleSpace)),
      Finset.card_univ]
  rw [hnz, G.cycleSpace_card] at hinj
  exact hinj

lemma cycleLengths_card_le (G : PhysicalGraph) :
    G.cycleLengths.card ≤ 2 ^ G.cycleRank - 1 := by
  classical
  unfold cycleLengths
  exact (Finset.card_image_le).trans (by simpa using G.cycleWord_card_le)

/-- The familiar `I(r) ≤ 2^r + 1` estimate at the level of one graph. -/
theorem coverage_bound (G : PhysicalGraph) {L : ℕ} (h : G.InitialCoverage L) :
    L ≤ 2 ^ G.cycleRank + 1 := by
  have hc := (Finset.card_le_card h).trans G.cycleLengths_card_le
  have hp : 0 < (2 : ℕ) ^ G.cycleRank := pow_pos (by norm_num) _
  simp only [Nat.card_Icc] at hc <;> norm_num <;> omega

end PhysicalGraph

/-- A finite implementation of the maximum in the source definition of I(r).
The upper cutoff is justified by `PhysicalGraph.coverage_bound`. -/
def initialCapacity (r : ℕ) : ℕ := by
  classical
  exact ((Finset.range (2 ^ r + 2)).filter fun L =>
    ∃ G : PhysicalGraph, G.cycleRank ≤ r ∧ G.InitialCoverage L).sup id

theorem initialCapacity_le (r : ℕ) : initialCapacity r ≤ 2 ^ r + 1 := by
  classical
  unfold initialCapacity
  apply Finset.sup_le
  intro L hL
  have h := (Finset.mem_filter.mp hL).1
  have hlt := Finset.mem_range.mp h
  exact Nat.le_of_lt_succ hlt

/-- Every actual covered endpoint is bounded by the corresponding extremum. -/
theorem coverage_le_initialCapacity (G : PhysicalGraph) {L r : ℕ}
    (hr : G.cycleRank ≤ r) (hL : G.InitialCoverage L) :
    L ≤ initialCapacity r := by
  classical
  have hp : (2 : ℕ) ^ G.cycleRank ≤ 2 ^ r := by gcongr <;> norm_num
  have hb := G.coverage_bound hL
  have hm : L ∈ (Finset.range (2 ^ r + 2)).filter
      (fun q => ∃ H : PhysicalGraph, H.cycleRank ≤ r ∧ H.InitialCoverage q) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), G, hr, hL⟩
  exact Finset.le_sup (f := id) hm







end Erdos1016
