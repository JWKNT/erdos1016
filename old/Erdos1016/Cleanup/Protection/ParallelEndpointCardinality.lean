import Erdos1016.Cleanup.Protection.ParallelProtectionComplement
import Erdos1016.Cleanup.Protection.ActiveComponentSurvival

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ParallelEndpointCardinality

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PostProtectionSimplicity
open Erdos1016.Proof.ParallelProtectionComplement
open Erdos1016.Proof.ActiveComponentSurvival
open Erdos1016.Proof.ProtectedDeletionRankLedger

/-- The two endpoints of the first label in a parallel pair. -/
private def firstPairEndpoints (Γ : FiniteMultiGraph)
    (p : Γ.Edge × Γ.Edge) : Finset Γ.Vertex :=
  {Γ.src p.1, Γ.dst p.1}



private theorem parallelOutside_swap_local
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex)
    {e f : Γ.Edge} (h : parallelOutside Γ P₀ e f) :
    parallelOutside Γ P₀ f e := by
  rcases h with ⟨hne, hes, het, hfs, hft, hp⟩
  refine ⟨hne.symm, hfs, hft, hes, het, ?_⟩
  rcases hp with hp | hp
  · exact Or.inl ⟨hp.1.symm, hp.2.symm⟩
  · exact Or.inr ⟨hp.2.symm, hp.1.symm⟩



private theorem firstPairEndpoints_card_le_two
    (Γ : FiniteMultiGraph) (p : Γ.Edge × Γ.Edge) :
    (firstPairEndpoints Γ p).card ≤ 2 := by
  unfold firstPairEndpoints
  calc
    (insert (Γ.src p.1) ({Γ.dst p.1} : Finset Γ.Vertex)).card ≤
        ({Γ.dst p.1} : Finset Γ.Vertex).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

private theorem vertex_endpoint_of_parallel
    (Γ : FiniteMultiGraph) (e f : Γ.Edge) {v : Γ.Vertex}
    (hparallel :
      ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
        (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f)))
    (hv : v = Γ.src e ∨ v = Γ.dst e ∨ v = Γ.src f ∨ v = Γ.dst f) :
    v = Γ.src f ∨ v = Γ.dst f := by
  rcases hparallel with hp | hp
  · rcases hv with hv | hv | hv | hv
    · exact Or.inl (hv.trans hp.1)
    · exact Or.inr (hv.trans hp.2)
    · exact Or.inl hv
    · exact Or.inr hv
  · rcases hv with hv | hv | hv | hv
    · exact Or.inr (hv.trans hp.1)
    · exact Or.inl (hv.trans hp.2)
    · exact Or.inl hv
    · exact Or.inr hv

private theorem vertex_endpoint_of_parallel_rev
    (Γ : FiniteMultiGraph) (e f : Γ.Edge) {v : Γ.Vertex}
    (hparallel :
      ((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
        (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f)))
    (hv : v = Γ.src e ∨ v = Γ.dst e ∨ v = Γ.src f ∨ v = Γ.dst f) :
    v = Γ.src e ∨ v = Γ.dst e := by
  rcases hparallel with hp | hp
  · rcases hv with hv | hv | hv | hv
    · exact Or.inl hv
    · exact Or.inr hv
    · exact Or.inl (hv.trans hp.1.symm)
    · exact Or.inr (hv.trans hp.2.symm)
  · rcases hv with hv | hv | hv | hv
    · exact Or.inl hv
    · exact Or.inr hv
    · exact Or.inr (hv.trans hp.2.symm)
    · exact Or.inl (hv.trans hp.1.symm)

private theorem protectParallelEndpoints_mem_iff_unordered
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex) (v : Γ.Vertex) :
    v ∈ protectParallelEndpoints Γ P₀ ↔
      ∃ p ∈ eligibleUnorderedParallelPairIndices Γ P₀,
        v ∈ firstPairEndpoints Γ p := by
  classical
  constructor
  · intro hv
    simp only [protectParallelEndpoints, Finset.mem_filter,
      Finset.mem_univ, true_and] at hv
    obtain ⟨e, f, hp, hv⟩ := hv
    have hneVal :
        (Fintype.equivFin Γ.Edge e).val ≠
          (Fintype.equivFin Γ.Edge f).val := by
      intro heq
      apply hp.1
      exact (Fintype.equivFin Γ.Edge).injective (Fin.ext heq)
    rcases Nat.lt_or_gt_of_ne hneVal with hlt | hgt
    · refine ⟨(e, f), ?_, ?_⟩
      · simp only [eligibleUnorderedParallelPairIndices, Finset.mem_filter,
          eligibleParallelPairIndices, Finset.mem_filter, Finset.mem_univ,
          true_and, parallelOutside]
        exact ⟨hp, hlt⟩
      · simp only [firstPairEndpoints, Finset.mem_insert, Finset.mem_singleton]
        exact vertex_endpoint_of_parallel_rev Γ e f hp.2.2.2.2.2 hv
    · refine ⟨(f, e), ?_, ?_⟩
      · simp only [eligibleUnorderedParallelPairIndices, Finset.mem_filter,
          eligibleParallelPairIndices, Finset.mem_filter, Finset.mem_univ,
          true_and, parallelOutside]
        exact ⟨parallelOutside_swap_local Γ P₀ hp, hgt⟩
      · simp only [firstPairEndpoints, Finset.mem_insert, Finset.mem_singleton]
        exact vertex_endpoint_of_parallel Γ e f hp.2.2.2.2.2 hv
  · rintro ⟨⟨e, f⟩, hp, hv⟩
    simp only [eligibleUnorderedParallelPairIndices, Finset.mem_filter,
      eligibleParallelPairIndices, Finset.mem_filter, Finset.mem_univ,
      true_and, parallelOutside] at hp
    rcases hp.1 with ⟨hne, hs, ht, hfs, hft, hparallel⟩
    simp only [protectParallelEndpoints, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨e, f, ⟨hne, hs, ht, hfs, hft, hparallel⟩, ?_⟩
    simp only [firstPairEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)

private theorem protectParallelEndpoints_eq_unordered_biUnion
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex) :
    protectParallelEndpoints Γ P₀ =
      (eligibleUnorderedParallelPairIndices Γ P₀).biUnion
        (firstPairEndpoints Γ) := by
  classical
  ext v
  simp only [Finset.mem_biUnion, protectParallelEndpoints_mem_iff_unordered]

/-- The actual protected endpoint set has at most two vertices per unordered
eligible parallel pair. Overlaps between pairs are automatically counted only
once by the union. -/
theorem protectParallelEndpoints_card_le_two_mul_unorderedPairCount
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex) :
    (protectParallelEndpoints Γ P₀).card ≤
      2 * (eligibleUnorderedParallelPairIndices Γ P₀).card := by
  classical
  rw [protectParallelEndpoints_eq_unordered_biUnion]
  calc
    ((eligibleUnorderedParallelPairIndices Γ P₀).biUnion
        (firstPairEndpoints Γ)).card ≤
      ∑ p ∈ eligibleUnorderedParallelPairIndices Γ P₀,
        (firstPairEndpoints Γ p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ eligibleUnorderedParallelPairIndices Γ P₀, 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact firstPairEndpoints_card_le_two Γ p
    _ = 2 * (eligibleUnorderedParallelPairIndices Γ P₀).card := by
      simp [Nat.mul_comm]

/-- Every vertex protected by a genuine parallel pair lies outside P₀. -/
theorem protectParallelEndpoints_disjoint_initial
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex) :
    Disjoint (protectParallelEndpoints Γ P₀) P₀ := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hp
  simp only [protectParallelEndpoints, Finset.mem_filter,
    Finset.mem_univ, true_and] at hv
  obtain ⟨e, f, hpair, hv⟩ := hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact hpair.2.1 hp
  · exact hpair.2.2.1 hp
  · exact hpair.2.2.2.1 hp
  · exact hpair.2.2.2.2.1 hp

/-- A real ambient degree dichotomy outside P₀ transfers to P₁. This gives
the paper's needed upper bound `≤ 3` but does not infer cubicity from the
final cleanup root. -/
theorem ambientDegree_le_three_on_protectedEndpoints
    (Γ : FiniteMultiGraph) (P₀ : Finset Γ.Vertex)
    (hdegree : ∀ v, v ∉ P₀ → ambientDegree Γ v = 2 ∨
      ambientDegree Γ v = 3) :
    ∀ v ∈ protectParallelEndpoints Γ P₀, ambientDegree Γ v ≤ 3 := by
  intro v hv
  have hv₀ : v ∉ P₀ := by
    intro h
    exact (Finset.disjoint_left.mp
      (protectParallelEndpoints_disjoint_initial Γ P₀)) hv h
  rcases hdegree v hv₀ with h | h <;> omega







end Erdos1016.Proof.ParallelEndpointCardinality

end
