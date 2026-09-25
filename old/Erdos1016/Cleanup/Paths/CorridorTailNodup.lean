import Erdos1016.Cleanup.Paths.EndpointRepetitionExclusion
import Erdos1016.Cleanup.Transport.ComponentCorridorReindexing

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CorridorTailNodup

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.EndpointRepetitionExclusion
open Erdos1016.Proof.CoreComponentAssembly
open Erdos1016.Proof.InternalRepetitionExclusion
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.ComponentCorridorReindexing
open Erdos1016.Proof.PartitionRouteDecomposition

variable {G : PhysicalGraph}

/-- Even when a corridor returns to its starting vertex, the return is its
only repeated vertex if every internal vertex is unprotected and has physical
degree two. Thus the tail of its recorded vertex list is nodup. -/
theorem corridor_vertex_tail_nodup_of_internal_degree_two
    (C : PhysicalCorridor G)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      G.degree (C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩) = 2) :
    C.vertices.tail.Nodup := by
  let Pbad : Finset G.Vertex := Finset.univ.filter (fun v => G.degree v ≠ 2)
  have hnotbad : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ Pbad := by
    intro i hv
    have hne := (Finset.mem_filter.mp hv).2
    exact hne (hinternal i)
  have hdegreebad : ∀ v, v ∉ Pbad → G.degree v = 2 := by
    intro v hv
    by_contra hne
    exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hlen := C.vertices_length
  have hi : i.val < C.edges.length := by
    have := i.isLt
    simp at this
    omega
  have hj : j.val < C.edges.length := by
    have := j.isLt
    simp at this
    omega
  have hget : C.vertices.get ⟨i.val + 1, by omega⟩ =
      C.vertices.get ⟨j.val + 1, by omega⟩ := by
    simpa using hij
  by_contra hne
  have hvalne : i.val ≠ j.val := by
    intro h
    exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · have hlt' : i.val + 1 < j.val + 1 := by omega
    by_cases hfinal : j.val + 1 = C.edges.length
    · have hvertex : C.vertices.get ⟨i.val + 1, by omega⟩ =
          C.vertices.get ⟨C.edges.length, by omega⟩ := by
        simpa [hfinal] using hget
      exact (no_repeated_end_internal_vertex C hnotbad hdegreebad
        (i.val + 1) (by omega) (by omega) hvertex).elim
    · have hjinternal : j.val + 1 < C.edges.length := by omega
      exact (no_repeated_internal_vertex C hnotbad hdegreebad
        (i.val + 1) (j.val + 1) (by omega) (by omega)
        (by omega) (by omega) hlt' hget).elim
  · have hgt' : j.val + 1 < i.val + 1 := by omega
    by_cases hfinal : i.val + 1 = C.edges.length
    · have hvertex : C.vertices.get ⟨j.val + 1, by omega⟩ =
          C.vertices.get ⟨C.edges.length, by omega⟩ := by
        simpa [hfinal] using hget.symm
      exact (no_repeated_end_internal_vertex C hnotbad hdegreebad
        (j.val + 1) (by omega) (by omega) hvertex).elim
    · have hiinternal : i.val + 1 < C.edges.length := by omega
      exact (no_repeated_internal_vertex C hnotbad hdegreebad
        (j.val + 1) (i.val + 1) (by omega) (by omega)
        (by omega) (by omega) hgt' hget.symm).elim

/-- Any corridor in a `CorridorPartition` has the needed tail simplicity:
the partition certifies degree two at each internal vertex. This includes
corridors whose endpoints coincide. -/
theorem partition_corridor_vertex_tail_nodup
    {P : Finset G.Vertex} {W : Finset G.Edge}
    (D : CorridorPartition G P W) (C : PhysicalCorridor G)
    (hC : C ∈ D.corridors) : C.vertices.tail.Nodup := by
  have hlocal := D.internal_unprotected_degree_two C hC
  apply corridor_vertex_tail_nodup_of_internal_degree_two
  intro i
  exact (hlocal i).2







end Erdos1016.Proof.CorridorTailNodup

end
