import Erdos1016.Cleanup.Packing.CubicEndpointConflicts
import Erdos1016.Cleanup.Protection.ParallelProtectionComplement

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.UnprotectedParallelPacking

open Erdos1016
open CleanupSpecification PostProtectionSimplicity
open ParallelProtectionComplement
open SuppressedParallelConflicts
open CubicEndpointConflicts GreedyConflictExtraction

abbrev PairIndex (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :=
  {p // p ∈ eligibleUnorderedParallelPairIndices Γ P}

theorem pair_facts (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (i : PairIndex Γ P) :
    parallelOutside Γ P i.1.1 i.1.2 ∧
    (Fintype.equivFin Γ.Edge i.1.1).val < (Fintype.equivFin Γ.Edge i.1.2).val := by
  have h := i.2
  simp only [eligibleUnorderedParallelPairIndices, eligibleParallelPairIndices,
    Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

private def pairSupport (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (i : PairIndex Γ P) : Finset Γ.Edge := {i.1.1, i.1.2}

private theorem support_injective (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    Function.Injective (pairSupport Γ P) := by
  intro i j hij
  have hfirst : i.1.1 = j.1.1 ∨ i.1.1 = j.1.2 := by
    have hm : i.1.1 ∈ pairSupport Γ P i := by simp [pairSupport]
    rw [hij] at hm
    simpa [pairSupport] using hm
  have hsecond : i.1.2 = j.1.1 ∨ i.1.2 = j.1.2 := by
    have hm : i.1.2 ∈ pairSupport Γ P i := by simp [pairSupport]
    rw [hij] at hm
    simpa [pairSupport] using hm
  have hi := pair_facts Γ P i
  have hj := pair_facts Γ P j
  rcases hfirst with h11 | h12
  · rcases hsecond with h21 | h22
    · exact (hi.1.1 (h11.trans h21.symm)).elim
    · exact Subtype.ext (Prod.ext h11 h22)
  · rcases hsecond with h21 | h22
    · have hi' := hi.2
      have hj' := hj.2
      rw [h12, h21] at hi'
      omega
    · exact (hi.1.1 (h12.trans h22.symm)).elim

noncomputable def suppressedPair (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hloop : ∀ e : Γ.Edge, Γ.src e ∉ P → Γ.dst e ∉ P → Γ.src e ≠ Γ.dst e)
    (i : PairIndex Γ P) [DecidableEq Γ.Vertex] : SuppressedParallelPair Γ.src Γ.dst := by
  classical
  have h := (pair_facts Γ P i).1
  refine ⟨Γ.src i.1.1, Γ.dst i.1.1, hloop i.1.1 h.2.1 h.2.2.1,
    pairSupport Γ P i, ?_, ?_, ?_⟩
  · exact Finset.card_pair h.1
  · intro e he
    have he' : e = i.1.1 ∨ e = i.1.2 := by simpa [pairSupport] using he
    rcases he' with rfl | rfl
    · simp [incidentLabels]
    · rcases h.2.2.2.2.2 with ⟨hs, _⟩ | ⟨hs, _⟩
      · simp [incidentLabels, hs]
      · simp [incidentLabels, hs]
  · intro e he
    have he' : e = i.1.1 ∨ e = i.1.2 := by simpa [pairSupport] using he
    rcases he' with rfl | rfl
    · simp [incidentLabels]
    · rcases h.2.2.2.2.2 with ⟨_, ht⟩ | ⟨_, ht⟩
      · simp [incidentLabels, ht]
      · simp [incidentLabels, ht]

/-- The actual unordered parallel pairs outside the protected vertices admit
one-third packing. Only vertices outside protection must be cubic. -/
theorem exists_disjoint_subfamily
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hcubic : ∀ v, v ∉ P → ambientDegree Γ v ≤ 3)
    (hloop : ∀ e : Γ.Edge, Γ.src e ∉ P → Γ.dst e ∉ P → Γ.src e ≠ Γ.dst e)
    {V : Type*} [Fintype V] (U : PairIndex Γ P → Finset V)
    (hbridge : ∀ i j, ¬ Disjoint (U i) (U j) →
      ¬ Disjoint ({Γ.src i.1.1, Γ.dst i.1.1} : Finset Γ.Vertex)
        {Γ.src j.1.1, Γ.dst j.1.1})
    (threshold : ℕ)
    (hsize : 3 * threshold ≤ (eligibleUnorderedParallelPairIndices Γ P).card) :
    ∃ T : Finset (PairIndex Γ P), T ⊆ Finset.univ ∧
      PairwiseDisjointOn U T ∧ threshold ≤ T.card := by
  classical
  letI : DecidableEq Γ.Vertex := Classical.decEq _
  let S : PairIndex Γ P → SuppressedParallelPair Γ.src Γ.dst :=
    fun i => suppressedPair Γ P hloop i
  have hdegree : ∀ i v, v ∈ pairEndpointRegion Γ.src Γ.dst (S i) →
      (incidentLabels Γ.src Γ.dst v).card ≤ 3 := by
    intro i v hv
    have hi := (pair_facts Γ P i).1
    have hvP : v ∉ P := by
      have hv' : v = Γ.src i.1.1 ∨ v = Γ.dst i.1.1 := by
        simpa [S, suppressedPair, pairEndpointRegion] using hv
      rcases hv' with rfl | rfl
      · exact hi.2.1
      · exact hi.2.2.1
    have hset : incidentLabels Γ.src Γ.dst v =
        (Finset.univ.filter fun e => Γ.src e = v) ∪
          (Finset.univ.filter fun e => Γ.dst e = v) := by
      ext e
      simp [incidentLabels]
    have hcard : (incidentLabels Γ.src Γ.dst v).card ≤ ambientDegree Γ v := by
      rw [hset]
      unfold ambientDegree
      convert (Finset.card_union_le
        (Finset.univ.filter fun e : Γ.Edge => Γ.src e = v)
        (Finset.univ.filter fun e : Γ.Edge => Γ.dst e = v)) using 1 <;>
        congr 1 <;> congr 1 <;> ext e <;> simp
    exact hcard.trans (hcubic v hvP)
  exact exists_disjoint_physical_route_subfamily_local Γ.src Γ.dst U S hdegree
    (support_injective Γ P) (by
      intro i j h
      simpa [S, suppressedPair, pairEndpointRegion] using hbridge i j h)
    threshold (by simpa using hsize)

end Erdos1016.Proof.UnprotectedParallelPacking

end
