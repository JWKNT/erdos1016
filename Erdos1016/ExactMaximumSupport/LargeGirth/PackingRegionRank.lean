import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProductWords
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Rank supplied by disjoint cyclic subregions

Each actual cyclic subregion contributes a nonzero even word with its own
physical support. These words are linearly independent inside the full region.
The exact induced-cycle-space equivalence transfers their dimension bound.
No connectedness, simplicity, degree, or girth hypothesis is required.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingRegionRank
open FiniteMultiGraph
local instance packingRegionRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- Inclusion of regions preserves their actual internal cycle subspaces. -/
theorem internalCycleSpace_mono {U X : Finset G.Vertex} (hUX : U ⊆ X) :
    G.internalCycleSpace U ≤ G.internalCycleSpace X := by
  intro z hz e he
  apply hz e
  intro hm
  apply he
  have hh := (Finset.mem_filter.mp hm).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hUX hh.1, hUX hh.2⟩

/-- Distinct disjoint regions support independent nonzero even words. -/
theorem linearIndependent_internal {ι : Type*} [Fintype ι]
    (U : ι → Finset G.Vertex)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (z : ∀ i, G.internalCycleSpace (U i)) (hz : ∀ i, z i ≠ 0) :
    LinearIndependent F₂ (fun i => (z i).1) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  obtain ⟨e, he⟩ : ∃ e, (z i).1.1 e ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz i
    apply Subtype.ext
    apply Subtype.ext
    funext e
    exact h e
  have hm : e ∈ G.internalEdges (U i) := by
    by_contra hm
    exact he ((z i).2 e hm)
  have heq : (∑ j, a j • (z j).1).1 e = 0 := by rw [ha]; rfl
  have hs : (∑ j, a j • (z j).1).1 e = a i * (z i).1.1 e := by
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [G.internal_vanish_on_disjoint (U j) (U i) (hdisj hji) (z j) e hm, mul_zero]
    · simp
  rw [hs] at heq
  exact (mul_eq_zero.mp heq).resolve_right he

/-- A region containing disjoint cyclic subregions has at least their number in rank. -/
theorem card_le_induced_cycleRank {ι : Type*} [Fintype ι]
    (X : Finset G.Vertex) (U : ι → Finset G.Vertex)
    (hUX : ∀ i, U i ⊆ X)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcyc : ∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0) :
    Fintype.card ι ≤ (PieceCore.Induced.graph G X).cycleRank := by
  classical
  choose z hz using hcyc
  let v (i : ι) : G.internalCycleSpace X :=
    ⟨(z i).1, internalCycleSpace_mono G (hUX i) (z i).2⟩
  have hi : LinearIndependent F₂ v := by
    apply LinearIndependent.of_comp (G.internalCycleSpace X).subtype
    exact linearIndependent_internal G U hdisj z hz
  have hr := hi.fintype_card_le_finrank
  have he := (PoleProduct.cycleEquiv G X).finrank_eq
  change Module.finrank F₂ (PieceCore.Induced.graph G X).CycleSpace = _ at he
  change Fintype.card ι ≤ Module.finrank F₂ (PieceCore.Induced.graph G X).CycleSpace
  exact hr.trans_eq he.symm

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingRegionRank
