import Erdos1016.Cleanup.Corridors.DegreeTwoComponentCut
import Mathlib.Combinatorics.SimpleGraph.Path

set_option autoImplicit false

/-!
# Attachments of degree-two tree components

The Section 10 reduction suppresses maximal corridors outside a protected
core. A finite tree component whose vertices all have ambient degree two has
two distinct boundary vertices whenever it has more than one vertex. This is
the endpoint form of the two-incidence cut count: each vertex already has an
internal neighbor, so it can contribute at most one external incidence.
-/

namespace Erdos1016.Proof.TreeBoundaryAttachments

open Erdos1016
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If every vertex in a finite region has ambient degree two and at least one
internal neighbor, and the region has exactly two outgoing incidences, then
those incidences are at distinct vertices. This is the endpoint extraction
needed for a nontrivial degree-two tree corridor. -/
theorem exists_distinct_boundary_vertices_of_two_incidences
    (H : SimpleGraph V) [DecidableRel H.Adj] (C : Finset V)
    (hdeg : ∀ v ∈ C, (H.neighborFinset v).card = 2)
    (hinternal : ∀ v ∈ C, 0 < (H.neighborFinset v ∩ C).card)
    (hboundary : Erdos1016.Proof.DegreeTwoComponentCut.boundaryCount H C = 2) :
    ∃ v w, v ∈ C ∧ w ∈ C ∧ v ≠ w ∧
      (H.neighborFinset v \ C).Nonempty ∧ (H.neighborFinset w \ C).Nonempty := by
  classical
  let B : Finset V := C.filter fun v => 0 < (H.neighborFinset v \ C).card
  have hout_le_one (v : V) (hv : v ∈ C) :
      (H.neighborFinset v \ C).card ≤ 1 := by
    have hsum := Finset.card_inter_add_card_sdiff (H.neighborFinset v) C
    rw [hdeg v hv] at hsum
    have hpos := hinternal v hv
    omega
  have hsum_card :
      Erdos1016.Proof.DegreeTwoComponentCut.boundaryCount H C = B.card := by
    rw [Erdos1016.Proof.DegreeTwoComponentCut.boundaryCount]
    calc
      (∑ v ∈ C, (H.neighborFinset v \ C).card) =
          ∑ v ∈ C, if v ∈ B then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        by_cases hb : v ∈ B
        · have hp : 0 < (H.neighborFinset v \ C).card := by
            exact (Finset.mem_filter.mp hb).2
          have hle := hout_le_one v hv
          have heq : (H.neighborFinset v \ C).card = 1 := by omega
          simp [hb, heq]
        · have hz : (H.neighborFinset v \ C).card = 0 := by
            by_contra hne
            have hp : 0 < (H.neighborFinset v \ C).card := by omega
            exact hb (Finset.mem_filter.mpr ⟨hv, hp⟩)
          simp [hb, hz]
      _ = B.card := by
        rw [Finset.sum_boole]
        apply congrArg Finset.card
        ext v
        simp [B]
  have hB : B.card = 2 := by
    rw [← hsum_card]
    exact hboundary
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
  have hwC : w ∈ C := (Finset.mem_filter.mp hw).1
  have hvout : (H.neighborFinset v \ C).Nonempty := by
    have hp := (Finset.mem_filter.mp hv).2
    exact Finset.card_pos.mp (by simpa using hp)
  have hwout : (H.neighborFinset w \ C).Nonempty := by
    have hp := (Finset.mem_filter.mp hw).2
    exact Finset.card_pos.mp (by simpa using hp)
  exact ⟨v, w, hvC, hwC, hvw, hvout, hwout⟩

end Erdos1016.Proof.TreeBoundaryAttachments
