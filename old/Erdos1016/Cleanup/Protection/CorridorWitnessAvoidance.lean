import Erdos1016.Cleanup.Corridors.EndpointBoundary

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CorridorWitnessAvoidance

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.SingleCorridorRoute

variable {G : PhysicalGraph} {P₀ : Finset G.Vertex} {W : Finset G.Edge}

/-- A witness singleton corridor is pinned at witness vertices by the physical
step certificate. -/
theorem singleton_corridor_endpoints_are_witness_vertices
    (D : CorridorPartition G P₀ W) (V : Finset G.Vertex)
    (hV : ∀ e ∈ W, G.src e ∈ V ∧ G.dst e ∈ V)
    {e : G.Edge} (he : e ∈ W)
    {C : PhysicalCorridor G} (hC : C ∈ D.corridors)
    (hs : C.support = {e}) :
    corridorStart C ∈ V ∧ corridorFinish C ∈ V := by
  have hlen : C.edges.length = 1 := by
    have hc := C.support_card_eq_length
    rw [hs] at hc
    simpa using hc.symm
  have hvlen : C.vertices.length = 2 := by rw [C.vertices_length, hlen]
  have hedge : C.edges.get ⟨0, by omega⟩ = e := by
    have hm : e ∈ C.edges := by
      have : e ∈ C.support := by rw [hs]; simp
      exact List.mem_toFinset.mp this
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    have : i.val = 0 := by omega
    simpa [this] using hi
  have hstep := C.step ⟨0, by omega⟩
  simp only [hedge] at hstep
  have hs0 : C.vertices.get ⟨0, by omega⟩ = corridorStart C := by
    simp [corridorStart, List.head_eq_getElem_zero, hvlen]
  have ht0 : C.vertices.get ⟨1, by omega⟩ = corridorFinish C := by
    simp [corridorFinish, List.getLast_eq_getElem, hvlen]
  rcases hstep with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · rw [← hs0, ← ht0]
    have h0 : G.src e = corridorStart C := by simpa [corridorStart, List.head_eq_getElem_zero] using hsrc
    have h1 : G.dst e = corridorFinish C := by simpa [corridorFinish, List.getLast_eq_getElem, hvlen] using hdst
    constructor
    · have : G.src e ∈ V := (hV e he).1
      have hv : corridorStart C ∈ V := by simpa [h0] using this
      exact hs0 ▸ hv
    · have : G.dst e ∈ V := (hV e he).2
      have hv : corridorFinish C ∈ V := by simpa [h1] using this
      exact ht0 ▸ hv
  · rw [← hs0, ← ht0]
    have h0 : G.dst e = corridorStart C := by simpa [corridorStart, List.head_eq_getElem_zero] using hdst
    have h1 : G.src e = corridorFinish C := by simpa [corridorFinish, List.getLast_eq_getElem, hvlen] using hsrc
    constructor
    · have : G.dst e ∈ V := (hV e he).2
      have hv : corridorStart C ∈ V := by simpa [h0] using this
      exact hs0 ▸ hv
    · have : G.src e ∈ V := (hV e he).1
      have hv : corridorFinish C ∈ V := by simpa [h1] using this
      exact ht0 ▸ hv

/-- If both recorded endpoints avoid the protected witness vertices, the
physical corridor cannot contain a witness edge. Root separation is explicit
in the two endpoint hypotheses. -/
theorem corridor_support_disjoint_witnesses
    (D : CorridorPartition G P₀ W) (V : Finset G.Vertex)
    (hV : ∀ e ∈ W, G.src e ∈ V ∧ G.dst e ∈ V)
    {C : PhysicalCorridor G} (hC : C ∈ D.corridors)
    (hstart : corridorStart C ∉ V) (hfinish : corridorFinish C ∉ V) :
    Disjoint C.support W := by
  rw [Finset.disjoint_left]
  intro e heC heW
  obtain ⟨E, hE, hEs⟩ := D.witness_singleton e heW
  have hCE : C = E := by
    by_contra hne
    have hd := D.edge_disjoint C hC E hE hne
    have heE : e ∈ E.support := by rw [hEs]; simp
    exact (Finset.disjoint_left.mp hd) heC heE
  subst E
  have hend := singleton_corridor_endpoints_are_witness_vertices D V hV heW hE hEs
  exact (hstart hend.1).elim

end Erdos1016.Proof.CorridorWitnessAvoidance

end
