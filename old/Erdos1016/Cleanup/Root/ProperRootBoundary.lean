import Erdos1016.Cleanup.CleanupSpecification

set_option autoImplicit false

/-!
# Immediate graph consequences of a cleanup certificate

The output interface records a proper root and a connected auxiliary graph.
This module derives the elementary boundary and exterior nonemptiness facts
used by the later root-size comparison, rather than treating them as extra
graph assumptions.
-/

noncomputable section

namespace Erdos1016.Proof.ProperRootBoundary

open Erdos1016
open Erdos1016.Proof.CleanupSpecification

private theorem walk_has_boundary_adjacency
    {V : Type*} {H : SimpleGraph V} {u v : V} (p : H.Walk u v)
    (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ H.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab q ih =>
      by_cases hb : b ∈ S
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

/-- A connected auxiliary multigraph has at least one labelled edge crossing
every nonempty proper vertex set. -/
theorem cutEdges_nonempty_of_connected
    (Γ : FiniteMultiGraph) (hconn : Γ.toSimpleGraph.Connected)
    (S : Finset Γ.Vertex) (hne : S.Nonempty)
    (hproper : S.card < Γ.vertexCount) :
    (cutEdges Γ S).Nonempty := by
  classical
  obtain ⟨u, hu⟩ := hne
  have hout : (Sᶜ : Finset Γ.Vertex).Nonempty := by
    by_contra h
    have hEq : S = Finset.univ := by
      ext v
      constructor
      · intro _
        simp
      · intro _
        by_contra hv
        exact h ⟨v, Finset.mem_compl.mpr hv⟩
    have hcard : S.card = Γ.vertexCount := by
      rw [hEq]
      simp
    omega
  obtain ⟨v, hv⟩ := hout
  have hv' : v ∉ S := by simpa using hv
  obtain ⟨p⟩ := hconn u v
  obtain ⟨a, b, ha, hb, hab⟩ :=
    walk_has_boundary_adjacency p S hu hv'
  change a ≠ b ∧ ∃ e : Γ.Edge,
    (Γ.src e = a ∧ Γ.dst e = b) ∨ (Γ.src e = b ∧ Γ.dst e = a) at hab
  rcases hab with ⟨_, e, he | he⟩
  · refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩⟩
    exact ⟨by simpa [he.1] using ha, by simpa [he.2] using hb⟩
  · refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩⟩
    exact ⟨by simpa [he.1] using hb, by simpa [he.2] using ha⟩

/-- A proper finite root has a nonempty actual exterior, hence the induced
exterior graph has at least one connected component. -/
theorem exteriorComponentCount_pos_of_proper
    (Γ : FiniteMultiGraph) (S : Finset Γ.Vertex)
    (hproper : S.card < Γ.vertexCount) :
    1 ≤ exteriorComponentCount Γ S := by
  classical
  have hout : (Sᶜ : Finset Γ.Vertex).Nonempty := by
    by_contra h
    have hEq : S = Finset.univ := by
      ext v
      constructor
      · intro _
        simp
      · intro _
        by_contra hv
        exact h ⟨v, Finset.mem_compl.mpr hv⟩
    have hcard : S.card = Γ.vertexCount := by
      rw [hEq]
      simp
    omega
  obtain ⟨v, hv⟩ := hout
  let K : SimpleGraph {w : Γ.Vertex // w ∈ (↑(Sᶜ) : Set Γ.Vertex)} :=
    Γ.toSimpleGraph.induce (↑(Sᶜ) : Set Γ.Vertex)
  let q : {w : Γ.Vertex // w ∈ (↑(Sᶜ) : Set Γ.Vertex)} := ⟨v, by simpa using hv⟩
  letI : Nonempty K.ConnectedComponent := ⟨K.connectedComponentMk q⟩
  unfold exteriorComponentCount
  exact Fintype.card_pos_iff.mpr inferInstance





end Erdos1016.Proof.ProperRootBoundary

end
