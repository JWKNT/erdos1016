import Erdos1016.Cleanup.Root.ComponentExtraction

set_option autoImplicit false

/-!
# Rank accounting after deleting a protected vertex set

This file isolates the scalar step in the Section 10 component extraction.
Once each connected component outside the protected set has its Euler ledger,
the sum of their ranks loses at most one unit per deleted edge coordinate.
-/

namespace Erdos1016.Proof.ProtectedDeletionRankLedger

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction

/-- Edge labels deleted when the protected vertex set is removed. A loop at
a protected vertex is counted once, since deleting its coordinate costs one
dimension. -/
def protectedIncidentEdges (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    Finset Γ.Edge := by
  classical
  exact Finset.univ.filter fun e => Γ.src e ∈ P ∨ Γ.dst e ∈ P

/-- Edges whose two endpoints remain outside the protected set. -/
def unprotectedEdges (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    Finset Γ.Edge := by
  classical
  exact Finset.univ.filter fun e => Γ.src e ∉ P ∧ Γ.dst e ∉ P

/-- The edge labels split into those incident to the protected set and those
internal to its complement. -/
theorem protectedIncidentEdges_card_add_unprotectedEdges_card
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    (protectedIncidentEdges Γ P).card + (unprotectedEdges Γ P).card =
      Γ.edgeCount := by
  classical
  have hdisj : Disjoint (protectedIncidentEdges Γ P) (unprotectedEdges Γ P) := by
    apply Finset.disjoint_left.mpr
    intro e he1 he2
    simp only [protectedIncidentEdges, unprotectedEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at he1 he2
    rcases he1 with hs | ht
    · exact he2.1 hs
    · exact he2.2 ht
  have hunion : protectedIncidentEdges Γ P ∪ unprotectedEdges Γ P = Finset.univ := by
    ext e
    simp only [Finset.mem_union, protectedIncidentEdges, unprotectedEdges,
      Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [← Finset.card_union_of_disjoint hdisj, hunion]
  simp





/-- Once the vertex and edge counts are partitioned by the components
outside `P`, their actual cycle ranks sum to at least the ambient rank minus
the number of edge coordinates incident to `P`. The local Euler equations
come from `componentInternalGraph_euler`; the two partition equalities are
purely set-theoretic. -/
theorem outside_rank_sum_lower_of_partition
    {Γ : FiniteMultiGraph} {P : Finset Γ.Vertex}
    (hcomponent : ∀ c : OutsideComponent Γ P,
      (componentInternalGraph Γ P c).toSimpleGraph.Connected)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hvertices :
      (∑ c : OutsideComponent Γ P,
        (outsideComponentVertices Γ P c).card) = Pᶜ.card)
    (hedges :
      (∑ c : OutsideComponent Γ P,
        (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
        (unprotectedEdges Γ P).card) :
    Γ.cycleRank ≤
      (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) +
        (protectedIncidentEdges Γ P).card := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hlocal :
      (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) +
        (∑ c : OutsideComponent Γ P,
          (outsideComponentVertices Γ P c).card) =
      (∑ c : OutsideComponent Γ P,
        (internalEdges Γ (outsideComponentVertices Γ P c)).card) +
        Fintype.card (OutsideComponent Γ P) := by
    calc
      _ = ∑ c : OutsideComponent Γ P,
          (outsideComponentRank Γ P c +
          (outsideComponentVertices Γ P c).card) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ c : OutsideComponent Γ P,
          ((internalEdges Γ (outsideComponentVertices Γ P c)).card + 1) := by
          apply Finset.sum_congr rfl
          intro c hc
          exact componentInternalGraph_euler Γ P c (hcomponent c)
      _ = _ := by simp [Finset.sum_add_distrib]
  have hlocal' :
      (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) + Pᶜ.card =
        (unprotectedEdges Γ P).card + Fintype.card (OutsideComponent Γ P) := by
    rw [← hvertices, ← hedges]
    exact hlocal
  have hglobal0 := FiniteMultiGraph.euler_formula Γ
  have hglobalComponents : Γ.componentCount = 1 := by
    letI : Subsingleton Γ.ConnectedComponent :=
      hconn.preconnected.subsingleton_connectedComponent
    letI : Unique Γ.ConnectedComponent :=
      ⟨⟨Γ.componentOf (Classical.choice hconn.nonempty)⟩,
        fun c => Subsingleton.elim _ _⟩
    simp [FiniteMultiGraph.componentCount, Fintype.card_unique]
  rw [hglobalComponents] at hglobal0
  have hvertexSplit : P.card + Pᶜ.card = Γ.vertexCount := by
    simpa [Nat.add_comm] using Finset.card_compl_add_card P
  have hedgeSplit := protectedIncidentEdges_card_add_unprotectedEdges_card Γ P
  have hglobal :
      Γ.cycleRank + (P.card + Pᶜ.card) =
        ((protectedIncidentEdges Γ P).card + (unprotectedEdges Γ P).card) + 1 := by
    omega
  have hpNat : 1 ≤ P.card := Finset.card_pos.mpr hP
  omega



end Erdos1016.Proof.ProtectedDeletionRankLedger
