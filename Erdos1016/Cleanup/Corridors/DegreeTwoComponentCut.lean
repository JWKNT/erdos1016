import Erdos1016.Graph.Basic

set_option autoImplicit false

namespace Erdos1016.Proof.DegreeTwoComponentCut

open Erdos1016
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]



private theorem walk_has_boundary_adjacency
    (H : SimpleGraph V) (C : Finset V) {u v : V}
    (p : H.Walk u v) (hu : u ∈ C) (hv : v ∉ C) :
    ∃ a b, a ∈ C ∧ b ∉ C ∧ H.Adj a b := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab q ih =>
      by_cases hb : b ∈ C
      · exact ih hb hv
      · exact ⟨a, b, hu, hb, hab⟩

/-- A nonempty finite vertex set disjoint from a nonempty protected set has a
crossing adjacency in a connected ambient graph. This is the cut API needed
when an induced degree-two component is shown to be closed by a cycle. -/
theorem exists_boundary_adjacency_of_connected
    (H : SimpleGraph V) (hconn : H.Connected)
    (C P : Finset V) (hC : C.Nonempty) (hP : P.Nonempty)
    (hdisjoint : Disjoint C P) :
    ∃ a b, a ∈ C ∧ b ∉ C ∧ H.Adj a b := by
  classical
  obtain ⟨a, ha⟩ := hC
  obtain ⟨b, hb⟩ := hP
  have hbC : b ∉ C := by
    intro hbc
    exact (Finset.disjoint_left.mp hdisjoint) hbc hb
  rcases hconn a b with ⟨p⟩
  exact walk_has_boundary_adjacency H C p ha hbC





/-- The external cut incidence count, counting an edge once at its endpoint
inside `C`. -/
noncomputable def boundaryCount (H : SimpleGraph V) [DecidableRel H.Adj]
    (C : Finset V) : ℕ :=
  ∑ v ∈ C, (H.neighborFinset v \ C).card

/-- The finite degree-sum decomposition into internal and external incidences.
This is the local handshaking identity for an arbitrary vertex set. -/
theorem degree_sum_eq_internal_plus_boundary
    (H : SimpleGraph V) [DecidableRel H.Adj] (C : Finset V) :
    (∑ v ∈ C, (H.neighborFinset v).card) =
      (∑ v ∈ C, (H.neighborFinset v ∩ C).card) + boundaryCount H C := by
  classical
  simp only [boundaryCount]
  calc
    _ = ∑ v ∈ C,
        ((H.neighborFinset v ∩ C).card + (H.neighborFinset v \ C).card) := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (Finset.card_inter_add_card_sdiff (H.neighborFinset v) C).symm
    _ = _ := by rw [Finset.sum_add_distrib]



end Erdos1016.Proof.DegreeTwoComponentCut
