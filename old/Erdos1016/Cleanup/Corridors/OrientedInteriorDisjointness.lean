import Erdos1016.Cleanup.Paths.EndpointRepetitionExclusion
import Erdos1016.Cleanup.Corridors.CoreComponentAssembly
import Erdos1016.Cleanup.Corridors.InteriorOwnership

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.OrientedInteriorDisjointness

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.CorridorPairedPathCertificates
open Erdos1016.Proof.CoreComponentAssembly
open Erdos1016.Proof.PhysicalDegreeTwoCoreComponents
open Erdos1016.Proof.InteriorOwnership


variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

private theorem vertex_is_interior_index
    (C : PhysicalCorridor G) (x : G.Vertex)
    (hx : x ∈ C.vertices)
    (hstart : x ≠ C.vertices.get ⟨0, by have := C.vertices_length; omega⟩)
    (hfinish : x ≠ C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩) :
    ∃ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ = x := by
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  have hjpos : 0 < j := by
    by_contra hzero
    have hzero' : j = 0 := by omega
    subst j
    exact hstart hget.symm
  have hjlast : j < C.edges.length := by
    have hjlt : j < C.vertices.length := hj
    by_contra hnot
    have heqj : j = C.edges.length := by
      have hlen := C.vertices_length
      omega
    subst j
    exact hfinish hget.symm
  refine ⟨⟨j - 1, ?_⟩, ?_⟩
  · have hlen := C.vertices_length
    omega
  · have hlen := C.vertices_length
    have heq : j - 1 + 1 = j := by omega
    simpa [heq] using hget

private theorem start_get (C : PhysicalCorridor G) :
    C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ = corridorStart C := by
  have hh : C.vertices.head? = some
      (C.vertices.get ⟨0, by have := C.vertices_length; omega⟩) := by
    rw [List.head?_eq_getElem?]
    simp
  have hs := (corridorStart_head? C).symm.trans hh
  exact Option.some.inj hs |>.symm

private theorem finish_get (C : PhysicalCorridor G) :
    C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ = corridorFinish C := by
  have hh : C.vertices.getLast? = some
      (C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩) := by
    rw [List.getLast?_eq_getElem?]
    simp [C.vertices_length]
  have hs := (corridorFinish_getLast? C).symm.trans hh
  exact Option.some.inj hs |>.symm

private theorem mem_tail_ne_head (C : PhysicalCorridor G) (hnd : C.vertices.Nodup)
    {x : G.Vertex} (hx : x ∈ C.vertices.tail) :
    x ≠ C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ := by
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  have hjlen : j < C.vertices.length - 1 := by
    simpa [List.length_tail] using hj
  have hget' : C.vertices[j + 1] = x := by
    have ht := List.getElem_tail (l := C.vertices) (i := j)
      (by simpa [List.length_tail] using hj)
    exact ht.symm.trans hget
  intro heq
  have hEq : C.vertices[j + 1] = C.vertices[0] := hget'.trans heq
  have hidx := (hnd.getElem_inj_iff).mp hEq
  omega

private theorem mem_reverse_tail_ne_last (C : PhysicalCorridor G) (hnd : C.vertices.Nodup)
    {x : G.Vertex} (hx : x ∈ C.vertices.reverse.tail) :
    x ≠ C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ := by
  have hrev : C.vertices.reverse.Nodup := List.nodup_reverse.mpr hnd
  obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hx
  have hjlen : j < C.vertices.reverse.length - 1 := by
    simpa [List.length_tail] using hj
  have hget' : C.vertices.reverse[j + 1] = x := by
    have ht := List.getElem_tail (l := C.vertices.reverse) (i := j)
      (by simpa [List.length_tail] using hj)
    exact ht.symm.trans hget
  intro heq
  have hEq : C.vertices.reverse[j + 1] = C.vertices.reverse[0] := by
    rw [hget', heq]
    have hl : C.vertices.reverse[0] =
        C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ := by
      simp [List.getElem_reverse, C.vertices_length]
    exact hl.symm
  have hidx := (hrev.getElem_inj_iff).mp hEq
  omega

/-- Same-orientation path interiors are disjoint for distinct canonical corridors. -/
theorem canonical_corridors_same_orientation_tails_disjoint
    (D : CorridorPartition G P W) {C E : PhysicalCorridor G}
    (hC : C ∈ D.corridors) (hE : E ∈ D.corridors) (hCE : C ≠ E)
    (hndC : C.vertices.Nodup) (hndE : E.vertices.Nodup)
    (hends : corridorStart C = corridorStart E ∧ corridorFinish C = corridorFinish E)
    :
    Disjoint C.vertices.tail.toFinset E.vertices.reverse.tail.toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxC hxE
  have hxC' : x ∈ C.vertices.tail := List.mem_toFinset.mp hxC
  have hxE' : x ∈ E.vertices.reverse.tail := List.mem_toFinset.mp hxE
  have hxCs : x ≠ corridorStart C := by
    intro h; exact mem_tail_ne_head C hndC hxC' (h.trans (start_get C).symm)
  have hxEt : x ≠ corridorFinish E := by
    intro h; exact mem_reverse_tail_ne_last E hndE hxE' (h.trans (finish_get E).symm)
  have hxCt : x ≠ corridorFinish C := by simpa [hends.2] using hxEt
  have hxEs : x ≠ corridorStart E := by simpa [hends.1] using hxCs
  have hixC := vertex_is_interior_index C x (List.mem_of_mem_tail hxC')
    (by intro h; exact hxCs (h.trans (start_get C)))
    (by intro h; exact hxCt (h.trans (finish_get C)))
  have hxEfull : x ∈ E.vertices := List.mem_reverse.mp (List.mem_of_mem_tail hxE')
  have hixE := vertex_is_interior_index E x hxEfull
    (by intro h; exact hxEs (h.trans (start_get E)))
    (by intro h; exact hxEt (h.trans (finish_get E)))
  exact distinct_corridors_cannot_share_interior_index D hC hE hCE hixC.choose hixE.choose
    (hixC.choose_spec.trans hixE.choose_spec.symm)

/-- Opposite-orientation path interiors are disjoint for distinct canonical corridors. -/
theorem canonical_corridors_opposite_orientation_tails_disjoint
    (D : CorridorPartition G P W) {C E : PhysicalCorridor G}
    (hC : C ∈ D.corridors) (hE : E ∈ D.corridors) (hCE : C ≠ E)
    (hndC : C.vertices.Nodup) (hndE : E.vertices.Nodup)
    (hends : corridorStart C = corridorFinish E ∧ corridorFinish C = corridorStart E)
    :
    Disjoint C.vertices.tail.toFinset E.vertices.tail.toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxC hxE
  have hxC' : x ∈ C.vertices.tail := List.mem_toFinset.mp hxC
  have hxE' : x ∈ E.vertices.tail := List.mem_toFinset.mp hxE
  have hxCs : x ≠ corridorStart C := by
    intro h; exact mem_tail_ne_head C hndC hxC' (h.trans (start_get C).symm)
  have hxEs : x ≠ corridorStart E := by
    intro h; exact mem_tail_ne_head E hndE hxE' (h.trans (start_get E).symm)
  have hxCt : x ≠ corridorFinish C := by simpa [hends.2] using hxEs
  have hxEt : x ≠ corridorFinish E := by simpa [hends.1] using hxCs
  have hixC := vertex_is_interior_index C x (List.mem_of_mem_tail hxC')
    (by intro h; exact hxCs (h.trans (start_get C)))
    (by intro h; exact hxCt (h.trans (finish_get C)))
  have hixE := vertex_is_interior_index E x (List.mem_of_mem_tail hxE')
    (by intro h; exact hxEs (h.trans (start_get E)))
    (by intro h; exact hxEt (h.trans (finish_get E)))
  exact distinct_corridors_cannot_share_interior_index D hC hE hCE hixC.choose hixE.choose
    (hixC.choose_spec.trans hixE.choose_spec.symm)

end Erdos1016.Proof.OrientedInteriorDisjointness

end
