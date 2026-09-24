import Erdos1016.Extremal.Capacity.CycleLengthComposition
import Erdos1016.Extremal.Capacity.PureCycleBound
import Erdos1016.Extremal.Capacity.CycleLengths

set_option autoImplicit false

/-!
# Cycle-length counting across an edge partition

The per-cycle restriction lemma and the pure-cycle rank bound combine into a
finite cardinality estimate for all cycle lengths of a physical graph.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PhysicalGraph

/-- Nonzero demands in the actual common-boundary image of the edge
partition. Crossing cycles can only contribute at one of these demands. -/
def activeCommonBoundaryDemands (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset G.Demand :=
  by
    classical
    exact Finset.univ.filter fun t =>
      t ≠ 0 ∧ t ∈ LinearMap.range (G.commonBoundaryMap E)

@[simp] theorem mem_activeCommonBoundaryDemands
    (G : PhysicalGraph) (E : Finset G.Edge) (t : G.Demand) :
    t ∈ G.activeCommonBoundaryDemands E ↔
      t ≠ 0 ∧ t ∈ LinearMap.range (G.commonBoundaryMap E) := by
  classical
  simp [activeCommonBoundaryDemands]

private theorem cycle_length_mem_partition_sets
    (G : PhysicalGraph) (E : Finset G.Edge) {C : G.CycleWord} :
    G.wordLength C.1 ∈
      G.pureCycleLengths E ∪ G.pureCycleLengths Eᶜ ∪
        (G.activeCommonBoundaryDemands E).biUnion (fun t =>
          Capacity.naturalSumset
            (G.restrictedLinearForestLengths E t)
            (G.restrictedLinearForestLengths Eᶜ t)) := by
  classical
  simp only [Finset.mem_union]
  by_cases hout : ∃ e, e ∉ E ∧ C.1 e ≠ 0
  · by_cases hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0
    · right
      let t := G.restrictedBoundary E (G.restrictWord E C.1)
      have htnz : t ≠ 0 := G.restrictCycle_boundary_ne_zero C E hin hout
      have hrange : t ∈ LinearMap.range (G.commonBoundaryMap E) := by
        refine ⟨⟨C.1, C.2.2.1⟩, ?_⟩
        change G.outsideBoundary E (G.restrictOutsideWord E C.1) = t
        rw [← G.restrictCycle_boundary_eq C E]
      have ht : t ∈ G.activeCommonBoundaryDemands E := by
        exact (mem_activeCommonBoundaryDemands G E t).2 ⟨htnz, hrange⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨t, ht, ?_⟩
      simpa [t] using G.crossingCycle_length_mem_naturalSumset C E hin hout
    · left
      right
      have hzero : ∀ e, e ∈ E → C.1 e = 0 := by
        intro e he
        by_cases hval : C.1 e = 0
        · exact hval
        · exact False.elim (hin ⟨e, he, hval⟩)
      let C' : G.PureCycleWord Eᶜ := ⟨C, by
        intro e he
        apply hzero e
        simpa using he⟩
      unfold pureCycleLengths
      exact Finset.mem_image.mpr ⟨C', Finset.mem_univ _, rfl⟩
  · left
    left
    have hzero : ∀ e, e ∉ E → C.1 e = 0 := by
      intro e he
      by_cases hval : C.1 e = 0
      · exact hval
      · exact False.elim (hout ⟨e, he, hval⟩)
    let C' : G.PureCycleWord E := ⟨C, hzero⟩
    unfold pureCycleLengths
    exact Finset.mem_image.mpr ⟨C', Finset.mem_univ _, rfl⟩

/-- Every cycle length is either pure on one side of the partition, or is a
sum of two local linear-forest lengths at a nonzero common-boundary demand.
Counting the union gives the graph-specific numerical composition bound. -/
theorem cycleLengths_card_le_partition
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.cycleLengths.card ≤
      (G.pureCycleLengths E).card +
        (G.pureCycleLengths Eᶜ).card +
        ∑ t ∈ G.activeCommonBoundaryDemands E,
          G.restrictedLinearForestMultiplicity E t *
            G.restrictedLinearForestMultiplicity Eᶜ t := by
  classical
  let A := G.pureCycleLengths E
  let M := G.pureCycleLengths Eᶜ
  let X := (G.activeCommonBoundaryDemands E).biUnion (fun t =>
    Capacity.naturalSumset
      (G.restrictedLinearForestLengths E t)
      (G.restrictedLinearForestLengths Eᶜ t))
  have hsub : G.cycleLengths ⊆ A ∪ M ∪ X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨C, -, rfl⟩
    simpa only [Finset.mem_union] using cycle_length_mem_partition_sets G E
  have hunion : (A ∪ M ∪ X).card ≤ A.card + M.card + X.card := by
    calc
      (A ∪ M ∪ X).card ≤ (A ∪ M).card + X.card := Finset.card_union_le _ _
      _ ≤ A.card + M.card + X.card := by
        exact add_le_add_right (Finset.card_union_le A M) _
  have hbiUnion := Capacity.card_biUnion_naturalSumsets_le
    (G.activeCommonBoundaryDemands E)
    (fun t => G.restrictedLinearForestLengths E t)
    (fun t => G.restrictedLinearForestLengths Eᶜ t)
  calc
    G.cycleLengths.card ≤ (A ∪ M ∪ X).card := Finset.card_le_card hsub
    _ ≤ A.card + M.card + X.card := hunion
    _ ≤ A.card + M.card +
        ∑ t ∈ G.activeCommonBoundaryDemands E,
          G.restrictedLinearForestMultiplicity E t *
            G.restrictedLinearForestMultiplicity Eᶜ t := by
      dsimp [X]
      simpa [restrictedLinearForestMultiplicity] using
        (add_le_add_left hbiUnion (A.card + M.card))
    _ = _ := by simp [A, M]

end Erdos1016.PhysicalGraph
