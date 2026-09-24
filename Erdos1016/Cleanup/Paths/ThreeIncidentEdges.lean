import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# Three distinct incident edges force degree at least three

This is a small counting lemma used by the Section 10 corridor simplicity
argument. The physical host is a simple graph, so distinct edge labels are
distinct neighbors at a fixed endpoint.
-/

namespace Erdos1016.Proof.ThreeIncidentEdges

open Erdos1016

theorem degree_ge_three_of_three_distinct_incident
    (G : PhysicalGraph) (v : G.Vertex)
    (e₁ e₂ e₃ : G.Edge)
    (h₁ : G.incident e₁ v) (h₂ : G.incident e₂ v) (h₃ : G.incident e₃ v)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    3 ≤ G.degree v := by
  classical
  let S : Finset G.Edge := Finset.univ.filter
    (fun e => (1 : F₂) ≠ 0 ∧ G.incident e v)
  have hsubset : ({e₁, e₂, e₃} : Finset G.Edge) ⊆ S := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · simp [S, h₁]
    · simp [S, h₂]
    · simp [S, h₃]
  have hcard : ({e₁, e₂, e₃} : Finset G.Edge).card = 3 := by
    simp [h₁₂, h₁₃, h₂₃]
  change 3 ≤ S.card
  rw [← hcard]
  exact Finset.card_le_card hsubset

end Erdos1016.Proof.ThreeIncidentEdges
