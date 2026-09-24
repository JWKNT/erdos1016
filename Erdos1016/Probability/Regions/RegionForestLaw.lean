import Erdos1016.CycleSpace.EmbeddedForestMarginals
import Erdos1016.Cleanup.Transport.CorridorRouteEquivalence

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalRegionForestProbability

open Erdos1016 CleanupSpecification SingleCorridorRoute
open CorridorRouteEquivalence

/-- For a simple physical graph, the labelled incidence degree of an extended
restricted word equals its usual restricted degree. -/
theorem restricted_degree_eq (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) (v : G.Vertex) :
    G.restrictedSelectedDegree E (G.restrictWord E x) v =
      selectedDegree (routeGraph G) (fun e => if e ∈ E then x e else 0) v := by
  classical
  let A := Finset.univ.filter fun e : G.Edge => e ∈ E ∧ x e ≠ 0 ∧ G.src e = v
  let B := Finset.univ.filter fun e : G.Edge => e ∈ E ∧ x e ≠ 0 ∧ G.dst e = v
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact G.noLoops e ((Finset.mem_filter.mp he).2.2.2.trans
      (Finset.mem_filter.mp hf).2.2.2.symm)
  have hcard : G.restrictedSelectedDegree E (G.restrictWord E x) v = (A ∪ B).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      change x e.1 ≠ 0 ∧ (G.src e.1 = v ∨ G.dst e.1 = v) at he
      exact he.2.elim (fun hs => Or.inl ⟨e.2, he.1, hs⟩) (fun ht => Or.inr ⟨e.2, he.1, ht⟩)
    · intro e _ f _ h
      exact Subtype.ext h
    · intro e he
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at he
      have heE : e ∈ E := he.elim And.left And.left
      refine ⟨⟨e, heE⟩, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact he.elim (fun h => ⟨h.2.1, Or.inl h.2.2⟩) (fun h => ⟨h.2.1, Or.inr h.2.2⟩)
  rw [hcard, Finset.card_union_of_disjoint hd]
  unfold selectedDegree
  congr 1 <;> congr 1 <;> ext e <;>
    simp [A, B, routeGraph, and_assoc]

/-- A restricted forest is exactly the corresponding labelled forest word
with zero coordinates outside the restriction. -/
theorem restricted_forest_iff (G : PhysicalGraph) (E : Finset G.Edge) (x : G.Word) :
    G.IsRestrictedLinearForest E (G.restrictWord E x) ↔
      IsLinearForestWord (routeGraph G) (fun e => if e ∈ E then x e else 0) := by
  classical
  have hgraph : G.restrictedSelectedGraph E (G.restrictWord E x) =
      selectedGraph (routeGraph G) (fun e => if e ∈ E then x e else 0) := by
    ext u v
    constructor
    · rintro ⟨e, hx, he⟩
      have hne : u ≠ v := by
        intro huv
        subst v
        exact he.elim (fun h => G.noLoops e.1 (h.1.trans h.2.symm))
          (fun h => G.noLoops e.1 (h.1.trans h.2.symm))
      exact ⟨hne, e.1, by simpa [e.2] using hx, he⟩
    · rintro ⟨_, e, hx, he⟩
      have heE : e ∈ E := by by_contra hn; simp [hn] at hx
      exact ⟨⟨e, heE⟩, by simpa [heE] using hx, he⟩
  constructor
  · intro h
    refine ⟨fun e _ => G.noLoops e, ?_, ?_, ?_⟩
    · intro e f hef _ _ hp
      exact hef (G.simple e f hp)
    · rw [← hgraph]
      exact h.1
    · intro v
      rw [← restricted_degree_eq]
      exact h.2 v
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hgraph]
      exact h.2.2.1
    · intro v
      rw [restricted_degree_eq]
      exact h.2.2.2 v

/-- Testing the edges inside a region equals testing the complement of its
internal edge set as the outside witness. -/
theorem region_eq_outside (G : PhysicalGraph) (U : Finset G.Vertex) :
    regionForestProbability (routeGraph G) U =
      G.outsideLinearForestProbability (SafeCore.internalEdges G U)ᶜ := by
  classical
  let J := physicalCycleRouteEquiv G
  have hrank : G.cycleRank = (routeGraph G).cycleRank := J.finrank_eq
  have hcompl : ((SafeCore.internalEdges G U)ᶜ)ᶜ = SafeCore.internalEdges G U := by
    ext e
    simp only [Finset.mem_compl, not_not]
  have hevents :
      (Finset.univ.filter fun x : (routeGraph G).CycleSpace => auxiliaryCleanupGood (routeGraph G) U x).card =
      (G.outsideLinearForestStates (SafeCore.internalEdges G U)ᶜ).card := by
    apply Finset.card_bij (fun x _ => J.symm x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [PhysicalGraph.outsideLinearForestStates, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcompl]
      apply (restricted_forest_iff G (SafeCore.internalEdges G U) _).mpr
      exact hx
    · intro x _ y _ h
      exact J.symm.injective h
    · intro x hx
      refine ⟨J x, ?_, J.symm_apply_apply x⟩
      simp only [PhysicalGraph.outsideLinearForestStates, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hcompl] at hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (restricted_forest_iff G (SafeCore.internalEdges G U) _).mp hx
  unfold regionForestProbability PhysicalGraph.outsideLinearForestProbability
  change _ / (2 : ℝ) ^ (routeGraph G).cycleRank = _
  rw [← hrank]
  exact congrArg (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ G.cycleRank) hevents

end Erdos1016.Proof.PhysicalRegionForestProbability

end
