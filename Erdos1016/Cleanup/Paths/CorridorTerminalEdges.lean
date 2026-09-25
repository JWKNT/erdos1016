import Erdos1016.Cleanup.Corridors.PhysicalPartition

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CorridorTerminalEdges

open Erdos1016
open Erdos1016.Proof.PhysicalPartition

variable {G : PhysicalGraph}

/-- The first recorded edge is incident to the first recorded vertex. -/
theorem corridor_first_edge_incident
    (C : PhysicalCorridor G) (hC : C.edges ≠ []) :
    G.incident (C.edges.head hC)
      (C.vertices.head (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))) := by
  have hlen : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hC
  have hstep := C.step ⟨0, hlen⟩
  have hedge : C.edges.head hC = C.edges.get ⟨0, hlen⟩ := by
    exact List.head_eq_getElem_zero hC
  have hvertex : C.vertices.head
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) =
        C.vertices.get ⟨0, by rw [C.vertices_length]; omega⟩ := by
    exact List.head_eq_getElem_zero _
  rw [hedge, hvertex]
  rcases hstep with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- The last recorded edge is incident to the last recorded vertex. -/
theorem corridor_last_edge_incident
    (C : PhysicalCorridor G) (hC : C.edges ≠ []) :
    G.incident (C.edges.getLast hC)
      (C.vertices.getLast (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))) := by
  have hlen : 0 < C.edges.length := List.length_pos_iff_ne_nil.mpr hC
  let i : Fin C.edges.length := ⟨C.edges.length - 1, by omega⟩
  have hstep := C.step i
  have hedge : C.edges.getLast hC = C.edges.get i := by
    simpa [i] using (List.getLast_eq_getElem hC)
  have hvertex : C.vertices.getLast
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) =
        C.vertices.get ⟨C.edges.length, by rw [C.vertices_length]; omega⟩ := by
    let hV : C.vertices ≠ [] :=
      List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)
    have hlastIndex : C.vertices.length - 1 = C.edges.length := by
      rw [C.vertices_length]
      omega
    calc
      C.vertices.getLast hV = C.vertices.get ⟨C.vertices.length - 1, by omega⟩ := by
        exact List.getLast_eq_getElem hV
      _ = C.vertices.get ⟨C.edges.length, by rw [C.vertices_length]; omega⟩ := by
        congr 1
        apply Fin.ext
        exact hlastIndex
  have hi : i.val + 1 = C.edges.length := by
    dsimp [i]
    omega
  have hstepLast :
      G.incident (C.edges.get i)
        (C.vertices.get ⟨C.edges.length, by rw [C.vertices_length]; omega⟩) := by
    rcases hstep with h | h
    · exact Or.inr (by simpa [hi] using h.2)
    · exact Or.inl (by simpa [hi] using h.2)
  rw [hedge, hvertex]
  exact hstepLast

/-- Every nonempty corridor has a physical support edge incident to each
recorded endpoint. This supplies the endpoint-label witnesses needed for
reduced cleanup event transport. -/
theorem endpoint_edges
    (C : PhysicalCorridor G) (hC : C.edges ≠ [])
    (s t : G.Vertex)
    (hstart : C.vertices.head? = some s)
    (hfinish : C.vertices.getLast? = some t) :
    ∃ p q : G.Edge,
      p ∈ C.support ∧ q ∈ C.support ∧
      G.incident p s ∧ G.incident q t := by
  classical
  have hneV : C.vertices ≠ [] := by
    intro h
    have hlen := C.vertices_length
    simp [h] at hlen
  have hstart' : C.vertices.head
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) = s :=
    (List.head_eq_iff_head?_eq_some
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega))).2 hstart
  have hfinish' : C.vertices.getLast
      (List.length_pos_iff_ne_nil.mp (by rw [C.vertices_length]; omega)) = t := by
    have hh := List.getLast?_eq_getLast_of_ne_nil hneV
    rw [hfinish] at hh
    exact Option.some.inj hh.symm
  refine ⟨C.edges.head hC, C.edges.getLast hC, ?_, ?_, ?_, ?_⟩
  · simp [PhysicalCorridor.support, hC]
  · simp [PhysicalCorridor.support, hC]
  · rw [← hstart']
    exact corridor_first_edge_incident C hC
  · rw [← hfinish']
    exact corridor_last_edge_incident C hC



end Erdos1016.Proof.CorridorTerminalEdges

end
