import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.InteriorOwnership

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}

private theorem degree_eq_incidentEdges_card (v : G.Vertex) :
    G.degree v = (incidentEdges G v).card := by
  classical
  unfold incidentEdges PhysicalGraph.degree PhysicalGraph.selectedDegree
  congr 1
  ext e
  simp [PhysicalGraph.incident]

private theorem degree_ge_three_of_three_incident
    {v : G.Vertex} {e₁ e₂ e₃ : G.Edge}
    (hne₁₂ : e₁ ≠ e₂) (hne₁₃ : e₁ ≠ e₃) (hne₂₃ : e₂ ≠ e₃)
    (h₁ : G.incident e₁ v) (h₂ : G.incident e₂ v) (h₃ : G.incident e₃ v) :
    3 ≤ G.degree v := by
  classical
  let S : Finset G.Edge := {e₁, e₂, e₃}
  have hcard : S.card = 3 := by simp [S, hne₁₂, hne₁₃, hne₂₃]
  have hsub : S ⊆ incidentEdges G v := by
    intro e he
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₁⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₃⟩
  have hle := Finset.card_le_card hsub
  have hle' : 3 ≤ (incidentEdges G v).card := by simpa [hcard] using hle
  rw [← degree_eq_incidentEdges_card] at hle'
  exact hle'

/-- Distinct corridors of a partition cannot both pass through an internal
vertex.  The two edges immediately before and after an internal occurrence
already exhaust its physical degree; a second edge-disjoint corridor would
contribute a third incident label. Corridor endpoints are not constrained,
so shared endpoints remain permitted. -/
theorem distinct_corridors_cannot_share_interior_index
    (D : CorridorPartition G P W)
    {C E : PhysicalCorridor G}
    (hC : C ∈ D.corridors) (hE : E ∈ D.corridors) (hCE : C ≠ E)
    (i : Fin (C.vertices.length - 2)) (j : Fin (E.vertices.length - 2))
    (hmid : C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ =
      E.vertices.get ⟨j.val + 1, by have := E.vertices_length; omega⟩) :
    False := by
  classical
  let v := C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩
  have hdegree : G.degree v = 2 := by
    have h := D.internal_unprotected_degree_two C hC i
    rcases h with ⟨_, hdeg⟩
    change G.degree v = 2 at hdeg
    exact hdeg
  have hdegreeE : G.degree v = 2 := by
    have h := D.internal_unprotected_degree_two E hE j
    have hv : E.vertices.get ⟨j.val + 1, by
        have := E.vertices_length
        omega⟩ = v := hmid.symm
    rcases h with ⟨_, hdeg⟩
    rw [hv] at hdeg
    exact hdeg

  have hleftCbound : i.val < C.edges.length := by
    have := C.vertices_length
    have hi := i.isLt
    omega
  have hrightCbound : i.val + 1 < C.edges.length := by
    have := C.vertices_length
    have hi := i.isLt
    omega
  have hleftEbound : j.val < E.edges.length := by
    have := E.vertices_length
    have hj := j.isLt
    omega
  let eL : G.Edge := C.edges.get ⟨i.val, hleftCbound⟩
  let eR : G.Edge := C.edges.get ⟨i.val + 1, hrightCbound⟩
  let fL : G.Edge := E.edges.get ⟨j.val, hleftEbound⟩

  have hstepCleft := C.step ⟨i.val, hleftCbound⟩
  have hstepCright := C.step ⟨i.val + 1, hrightCbound⟩
  have hstepEleft := E.step ⟨j.val, hleftEbound⟩
  have hincidentL : G.incident eL v := by
    change (G.src eL = _ ∧ G.dst eL = _) ∨ (G.dst eL = _ ∧ G.src eL = _) at hstepCleft
    rcases hstepCleft with h | h
    · exact Or.inr h.2
    · exact Or.inl (by simpa [v] using h.2)
  have hincidentR : G.incident eR v := by
    change (G.src eR = _ ∧ G.dst eR = _) ∨ (G.dst eR = _ ∧ G.src eR = _) at hstepCright
    rcases hstepCright with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hincidentF : G.incident fL v := by
    change (G.src fL = _ ∧ G.dst fL = _) ∨ (G.dst fL = _ ∧ G.src fL = _) at hstepEleft
    rcases hstepEleft with h | h
    · exact Or.inr (h.2.trans hmid.symm)
    · exact Or.inl (h.2.trans hmid.symm)

  have hneLR : eL ≠ eR := by
    intro he
    have hidx : (⟨i.val, hleftCbound⟩ : Fin C.edges.length) ≠
        ⟨i.val + 1, hrightCbound⟩ := by simp
    exact hidx ((List.Nodup.get_inj_iff C.edges_nodup).mp he)
  have hmemEL : eL ∈ C.support := by
    simp [eL, PhysicalCorridor.support]
  have hmemER : eR ∈ C.support := by
    simp [eR, PhysicalCorridor.support]
  have hmemFL : fL ∈ E.support := by
    simp [fL, PhysicalCorridor.support]
  have hsuppDisj : Disjoint C.support E.support :=
    D.edge_disjoint C hC E hE hCE
  have hneLF : eL ≠ fL := by
    intro heq
    exact (Finset.disjoint_left.mp hsuppDisj) hmemEL (heq ▸ hmemFL)
  have hneRF : eR ≠ fL := by
    intro heq
    exact (Finset.disjoint_left.mp hsuppDisj) hmemER (heq ▸ hmemFL)
  have hdeg3 := degree_ge_three_of_three_incident hneLR hneLF hneRF
    hincidentL hincidentR hincidentF
  omega



end Erdos1016.Proof.InteriorOwnership
