import Erdos1016.Cleanup.Corridors.OrientedInteriorDisjointness
import Erdos1016.Cleanup.Corridors.PairIntersectionEndpoints

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ParallelCorridorGeometry

open Erdos1016
open PhysicalPartition CorridorPairedPathCertificates
open PhysicalDegreeTwoCoreComponents EndpointRepetitionExclusion
open PairIntersectionEndpoints
open OrientedInteriorDisjointness
open PairedPathRegions

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

/-- Path simplicity follows from the actual partition fields. It does not
require the component graph to retain isolated vertices of the original host. -/
theorem corridor_nodup (D : CorridorPartition G P W)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (C : PhysicalCorridor G) (hC : C ∈ D.corridors)
    (hne : corridorStart C ≠ corridorFinish C) : C.vertices.Nodup := by
  have hs : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ =
      corridorStart C := by
    have h : C.vertices.head? = some
        (C.vertices.get ⟨0, by have := C.vertices_length; omega⟩) := by
      rw [List.head?_eq_getElem?]
      simp
    exact (Option.some.inj ((corridorStart_head? C).symm.trans h)).symm
  have ht : C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ =
      corridorFinish C := by
    have h : C.vertices.getLast? = some
        (C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩) := by
      rw [List.getLast?_eq_getElem?]
      simp [C.vertices_length]
    exact (Option.some.inj ((corridorFinish_getLast? C).symm.trans h)).symm
  apply corridor_vertices_nodup_of_distinct_endpoints (P₀ := protectedOrBranch G P) C
    (fun h => hne (hs.symm.trans (h.trans ht)))
  · intro i
    exact corridor_interior_not_mem_retained D C hC i rfl
  · intro v hv
    have hvP : v ∉ P := fun hp => hv (Finset.mem_union_left _ hp)
    rcases hdegree v hvP with h2 | h3
    · exact h2
    · exact (hv (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩))).elim

/-- Vertices of a corridor away from its endpoints retain their actual degree
and protection facts, without any hypothesis on degrees elsewhere. -/
theorem corridor_vertex_facts (D : CorridorPartition G P W)
    (C : PhysicalCorridor G) (hC : C ∈ D.corridors)
    {v : G.Vertex} (hv : v ∈ C.vertices)
    (hs : v ≠ corridorStart C) (ht : v ≠ corridorFinish C) :
    v ∉ P ∧ G.degree v = 2 := by
  obtain ⟨i, hi⟩ := interior_index_of_mem_ne_endpoints C hv hs ht
  have h := D.internal_unprotected_degree_two C hC i
  change C.vertices.get _ ∉ P ∧ G.degree (C.vertices.get _) = 2 at h
  rw [hi] at h
  exact h

/-- The two actual nonloop parallel routes produce a paired-path certificate
with their actual source and target, so degree conditions can be discharged
without guessing the endpoints chosen by an existential certificate. -/
theorem paired_certificate (D : CorridorPartition G P W)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)
    (C E : PhysicalCorridor G) (hC : C ∈ D.corridors) (hE : E ∈ D.corridors)
    (hCE : C ≠ E) (hne : corridorStart C ≠ corridorFinish C)
    (halign :
      (corridorStart C = corridorStart E ∧ corridorFinish C = corridorFinish E) ∨
      (corridorStart C = corridorFinish E ∧ corridorFinish C = corridorStart E)) :
    ∃ cert : PairedPathCertificate G (pairedRouteRegion C E),
      cert.source.1 = corridorStart C ∧ cert.target.1 = corridorFinish C := by
  classical
  have hneE : corridorStart E ≠ corridorFinish E := by
    rcases halign with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simpa [← hs, ← ht] using hne
    · simpa [← hs, ← ht] using hne.symm
  have hndC := corridor_nodup D hdegree C hC hne
  have hndE := corridor_nodup D hdegree E hE hneE
  have hlabels := D.edge_disjoint C hC E hE hCE
  have hs : corridorStart C ∈ pairedRouteRegion C E :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr
      (List.mem_of_mem_head? (corridorStart_head? C)))
  have ht : corridorFinish C ∈ pairedRouteRegion C E :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr
      (List.mem_of_mem_getLast? (corridorFinish_getLast? C)))
  have hUC : ∀ v ∈ C.vertices, v ∈ pairedRouteRegion C E :=
    fun v hv => Finset.mem_union_left _ (List.mem_toFinset.mpr hv)
  have hUE : ∀ v ∈ E.vertices, v ∈ pairedRouteRegion C E :=
    fun v hv => Finset.mem_union_right _ (List.mem_toFinset.mpr hv)
  have hcover : ∀ v ∈ pairedRouteRegion C E,
      v ∈ C.vertices ∨ v ∈ E.vertices := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl (List.mem_toFinset.mp hv)
    · exact Or.inr (List.mem_toFinset.mp hv)
  rcases halign with ⟨hstart, hfinish⟩ | ⟨hstart, hfinish⟩
  · let cert := pairedCertificate_of_corridors C E
      (corridorStart_head? C) (corridorFinish_getLast? C)
      (by rw [corridorStart_head? E, ← hstart])
      (by rw [corridorFinish_getLast? E, ← hfinish])
      hs ht hne hndC hndE hUC hUE
      (canonical_corridors_same_orientation_tails_disjoint D hC hE hCE hndC hndE
        ⟨hstart, hfinish⟩) hlabels hcover
    exact ⟨cert, rfl, rfl⟩
  · let cert := pairedCertificate_of_oppositely_oriented_corridors C E
      (corridorStart_head? C) (corridorFinish_getLast? C)
      (by rw [corridorStart_head? E, ← hfinish])
      (by rw [corridorFinish_getLast? E, ← hstart])
      hs ht hne hndC hndE hUC hUE
      (canonical_corridors_opposite_orientation_tails_disjoint D hC hE hCE hndC hndE
        ⟨hstart, hfinish⟩) hlabels hcover
    exact ⟨cert, rfl, rfl⟩

end Erdos1016.Proof.ParallelCorridorGeometry

end
