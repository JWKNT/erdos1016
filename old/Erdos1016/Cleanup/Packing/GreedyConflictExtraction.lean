import Erdos1016.Cleanup.Packing.CorridorPairedPathCertificates
import Erdos1016.Cycles.Geometry.CycleWalkExistence
import Erdos1016.Probability.Regions.TwoCutForestLaw
import Erdos1016.Extremal.Recurrence.ForestProbabilityReduction

set_option autoImplicit false

/-!
# Greedy packing under an explicit conflict bound

When candidate regions are not already pairwise disjoint, a bounded-degree
conflict relation still gives a large disjoint subfamily.  This is the exact
finite extraction inequality needed to feed the existing Section 10
many-region probability theorem.
-/

noncomputable section

namespace Erdos1016.Proof.GreedyConflictExtraction

open Erdos1016.Proof.Capacity

open Erdos1016.Proof.VertexSupportedWitness
open Erdos1016.Proof.PhysicalManyRegionConditionalProduct
open Erdos1016.Proof.PhysicalManyRegionReveal
open Erdos1016.Proof.PhysicalManyRegionProbabilityBridge

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]

def PairwiseDisjointOn (U : ι → Finset V) (S : Finset ι) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (U i) (U j)

noncomputable def closedConflicts (U : ι → Finset V) (S : Finset ι) (i : ι) : Finset ι := by
  classical
  exact S.filter fun j => j = i ∨ ¬ Disjoint (U i) (U j)

/-- A conflict-degree bound of `D` (including the selected vertex itself as
one removed element) permits a disjoint subfamily whose size loses at most a
factor `D`. The closed-neighborhood hypothesis is stated as `D` so the proof
does not depend on a particular conflict-graph encoding. -/
theorem exists_disjoint_subfamily
    (U : ι → Finset V) (S : Finset ι) (D : ℕ)
    (hconflict : ∀ i ∈ S, (closedConflicts U S i).card ≤ D)
    :
    ∃ T : Finset ι, T ⊆ S ∧ PairwiseDisjointOn U T ∧
      S.card ≤ D * T.card := by
  classical
  let P : Finset ι → Prop := fun S =>
    (∀ i ∈ S, (closedConflicts U S i).card ≤ D) →
      ∃ T : Finset ι, T ⊆ S ∧ PairwiseDisjointOn U T ∧
        S.card ≤ D * T.card
  have hP : P S := by
    refine Finset.strongInductionOn S ?_
    intro S ih hconflict
    by_cases hne : ∃ i : ι, i ∈ S
    · obtain ⟨i, hi⟩ := hne
      let bad := closedConflicts U S i
      let S' := S \ bad
      have hiBad : i ∈ bad := by
        simp [bad, closedConflicts, hi]
      have hsubset : S' ⊆ S := Finset.sdiff_subset
      have hsub : S' ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨hsubset, by
          intro heq
          have : i ∈ S' := by simpa [heq]
          exact (Finset.mem_sdiff.mp this).2 hiBad⟩
      have hlt : S'.card < S.card := Finset.card_lt_card hsub
      have hconflict' : ∀ j ∈ S',
          (closedConflicts U S' j).card ≤ D := by
        intro j hj
        have hjS : j ∈ S := hsubset hj
        have hfilter : closedConflicts U S' j ⊆ closedConflicts U S j := by
          intro x hx
          have hx' := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hsubset hx'.1, hx'.2⟩
        exact (Finset.card_le_card hfilter).trans (hconflict j hjS)
      obtain ⟨T, hTS', hTdisj, hS'card⟩ := ih S' hsub hconflict'
      have hTsub : T ⊆ S := hTS'.trans hsubset
      have hTnotbad : ∀ j ∈ T, j ∉ bad := by
        intro j hj hbad
        have : j ∈ S' := hTS' hj
        exact (Finset.mem_sdiff.mp this).2 hbad
      have hnewdisj : ∀ j ∈ T, Disjoint (U i) (U j) := by
        intro j hj
        have hjS : j ∈ S := hTsub hj
        have hjNotEq : j ≠ i := by
          intro hEq
          subst j
          exact hTnotbad i hj (by simp [bad, closedConflicts, hi])
        have hdisj : Disjoint (U i) (U j) := by
          classical
          by_contra hnot
          apply hTnotbad j hj
          simp [bad, closedConflicts, hjS, hjNotEq, hnot]
        exact hdisj
      refine ⟨insert i T, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjT
        · exact hi
        · exact hTsub hjT
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjT
        · rcases Finset.mem_insert.mp hk with rfl | hkT
          · exact (hjk rfl).elim
          · exact hnewdisj k hkT
        · rcases Finset.mem_insert.mp hk with rfl | hkT
          · exact (hnewdisj j hjT).symm
          · exact hTdisj j hjT k hkT hjk
      · have hremove : S.card ≤ bad.card + S'.card := by
          have hEq := Finset.card_sdiff_add_card_eq_card
            (Finset.filter_subset _ _ : bad ⊆ S)
          have hEq' : S'.card + bad.card = S.card := by
            simpa [S'] using hEq
          omega
        have hbad := hconflict i hi
        have hsum : S.card ≤ D + D * T.card := by
          calc
            S.card ≤ bad.card + S'.card := hremove
            _ ≤ D + D * T.card := Nat.add_le_add hbad hS'card
        calc
          S.card ≤ D + D * T.card := hsum
          _ = D * (T.card + 1) := by ring
          _ = D * (insert i T).card := by
            have hiNotMem : i ∉ T := by
              intro hiT
              have hiBad : i ∈ bad := by
                simp [bad, closedConflicts, hi]
              exact hTnotbad i hiT hiBad
            rw [Finset.card_insert_of_not_mem hiNotMem]
    · have hsempty : S = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr (by
        intro i hi
        exact hne ⟨i, hi⟩)
      subst S
      refine ⟨∅, by simp, ?_, by simp⟩
      intro i hi j hj hij
      simp at hi
  exact hP hconflict

/-- If the original family has at least `(D+1)` times the Section 10
threshold many members, a conflict bound of `D` yields enough pairwise
disjoint regions for the finite probability estimate. -/
theorem exists_disjoint_subfamily_of_threshold
    (U : ι → Finset V) (D threshold : ℕ)
    (hD : 1 ≤ D)
    (hconflict : ∀ i ∈ Finset.univ,
      (closedConflicts U Finset.univ i).card ≤ D)
    (hsize : D * threshold ≤ Fintype.card ι) :
    ∃ T : Finset ι, T ⊆ Finset.univ ∧ PairwiseDisjointOn U T ∧
      threshold ≤ T.card := by
  obtain ⟨T, hT, hdisj, hbound⟩ :=
    exists_disjoint_subfamily U Finset.univ D hconflict
  have hcard : D * threshold ≤ D * T.card := hsize.trans hbound
  have hDpos : 0 < D := hD
  have hthreshold : threshold ≤ T.card := by
    by_contra hnot
    have hlt : T.card < threshold := Nat.lt_of_not_ge hnot
    nlinarith
  exact ⟨T, hT, hdisj, hthreshold⟩



end Erdos1016.Proof.GreedyConflictExtraction

end
