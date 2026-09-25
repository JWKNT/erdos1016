import Erdos1016.CycleSpace.Support.ActiveRestriction

set_option autoImplicit false

/-!
# Rank accounting across active connected components

The cycle-space product decomposition also gives an exact sum formula for
cycle rank. This is the numerical form needed when componentwise probability
estimates are combined with a global rank bound.
-/

namespace Erdos1016.Proof.ActiveComponentRankSum

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents

theorem cycleRank_eq_sum_activeComponentRanks (G : PhysicalGraph) :
    G.cycleRank = ∑ c : ActiveComponent G,
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
  classical
  have hcard : Fintype.card G.CycleSpace =
      Fintype.card ((c : ActiveComponent G) →
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace) :=
    Fintype.card_congr (cycleSpaceProductEquiv G)
  have hpow : 2 ^ G.cycleRank =
      2 ^ (∑ c : ActiveComponent G,
        ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank) := by
    simpa only [PhysicalGraph.cycleSpace_card, Fintype.card_pi,
      Finset.prod_pow_eq_pow_sum] using hcard
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hpow



/-- The same averaging argument over a specified finite subset. -/
theorem exists_mem_large_rank
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (rank : ι → ℕ)
    (N total : ℕ) (hcount : s.card ≤ N)
    (htotal : total ≤ ∑ i ∈ s, rank i) :
    ∃ i, i ∈ s ∧ total ≤ N * rank i := by
  classical
  let S := s.sup rank
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup s hs rank
  have hsum : (∑ i ∈ s, rank i) ≤ s.card * S := by
    calc
      (∑ i ∈ s, rank i) ≤ ∑ i ∈ s, S := by
        apply Finset.sum_le_sum
        intro i hi'
        exact Finset.le_sup hi'
      _ = s.card * S := by simp [S]
  have hlarge : total ≤ N * S := by
    calc
      total ≤ ∑ i ∈ s, rank i := htotal
      _ ≤ s.card * S := hsum
      _ ≤ N * S := Nat.mul_le_mul_right S hcount
  exact ⟨i, hi, hmax ▸ hlarge⟩

/-- A graph with no edge coordinates has trivial cycle space. -/
private theorem cycleRank_zero_of_edgeCount_zero (G : PhysicalGraph)
    (hzero : G.edgeCount = 0) : G.cycleRank = 0 := by
  haveI : Subsingleton G.Word := ⟨fun x y => by
    funext e
    have he := e.isLt
    have : False := by omega
    exact this.elim⟩
  haveI : Subsingleton G.CycleSpace := inferInstance
  unfold PhysicalGraph.cycleRank
  exact Module.finrank_zero_of_subsingleton

private theorem activeComponent_rank_zero_of_no_edges (G : PhysicalGraph)
    (c : ActiveComponent G) (hempty : componentEdges G c = ∅) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank = 0 := by
  apply cycleRank_zero_of_edgeCount_zero
  simp [PhysicalGraph.restrictPhysical, Finset.card_eq_zero.mpr hempty]

/-- The finite set of active connected components containing at least one
active edge. Isolated host vertices are excluded, as in the paper's active
support graph. -/
noncomputable def nonemptyActiveComponents (G : PhysicalGraph) : Finset (ActiveComponent G) := by
  classical
  exact Finset.univ.filter fun c => (componentEdges G c).Nonempty

/-- Rank is unchanged when summing only over active components that contain
edges; the omitted isolated components have trivial cycle space. -/
theorem cycleRank_eq_sum_nonemptyActiveComponentRanks (G : PhysicalGraph) :
    G.cycleRank = ∑ c ∈ nonemptyActiveComponents G,
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
  classical
  have hsum := Finset.sum_subset
    (Finset.filter_subset (fun c : ActiveComponent G =>
      (componentEdges G c).Nonempty) Finset.univ)
    (by
      intro c hc hnot
      have hnot' : ¬ (componentEdges G c).Nonempty := by
        simpa [nonemptyActiveComponents] using hnot
      exact activeComponent_rank_zero_of_no_edges G c
        (Finset.not_nonempty_iff_eq_empty.mp hnot'))
  rw [cycleRank_eq_sum_activeComponentRanks G]
  simpa [nonemptyActiveComponents] using hsum.symm

end Erdos1016.Proof.ActiveComponentRankSum
