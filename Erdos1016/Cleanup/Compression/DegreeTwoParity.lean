import Erdos1016.Graph.Basic

set_option autoImplicit false

/-!
# The local parity constraint behind series suppression

The finite multigraph representation stores only a fixed finite edge and
vertex type; it has no vertex-deletion/edge-replacement operation.  This file
isolates the exact local boundary fact needed before constructing such an
operation: if the two incident edge coordinates are the whole boundary at a
degree-two vertex, a cycle word gives them equal values.
-/

namespace Erdos1016.Proof.DegreeTwoParity

open Erdos1016







/-- At degree two, the vertex boundary is exactly the sum of the two distinct
incident edge coordinates. This is the local expansion equation used below. -/
theorem boundary_eq_two_of_degree_two
    (G : PhysicalGraph) (y : G.Word) (v : G.Vertex)
    (e₁ e₂ : G.Edge) (h₁ : G.incident e₁ v) (h₂ : G.incident e₂ v)
    (hne : e₁ ≠ e₂) (hdegree : G.degree v = 2) :
    G.boundary y v = y e₁ + y e₂ := by
  classical
  let star : Finset G.Edge := Finset.univ.filter fun e => G.incident e v
  have hstar_card : star.card = 2 := by
    simpa [star, PhysicalGraph.degree, PhysicalGraph.selectedDegree] using hdegree
  have hmem₁ : e₁ ∈ star := by simp [star, h₁]
  have hmem₂ : e₂ ∈ star := by simp [star, h₂]
  have hstar : star = {e₁, e₂} := by
    ext e
    constructor
    · intro he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hn
      have hsub : insert e (insert e₁ ({e₂} : Finset G.Edge)) ⊆ star := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact he
        · exact hmem₁
        · exact hmem₂
      have hle := Finset.card_le_card hsub
      rw [hstar_card] at hle
      simp [hne, hn] at hle
    · intro he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact hmem₁
      · exact hmem₂
  have hterm (e : G.Edge) :
      (if G.incident e v then y e else 0) =
        (if G.src e = v then y e else 0) +
          (if G.dst e = v then y e else 0) := by
    by_cases hs : G.src e = v
    · have ht : G.dst e ≠ v := by
        intro h
        exact G.noLoops e (hs.trans h.symm)
      simp [PhysicalGraph.incident, hs, ht]
    · by_cases ht : G.dst e = v
      · simp [PhysicalGraph.incident, hs, ht]
      · simp [PhysicalGraph.incident, hs, ht]
  have hsum : (∑ e : G.Edge, if e ∈ star then y e else 0) =
      G.boundary y v := by
    calc
      (∑ e : G.Edge, if e ∈ star then y e else 0) =
          ∑ e : G.Edge, if G.incident e v then y e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        simp [star]
      _ = G.boundary y v := by
        simp only [PhysicalGraph.boundary]
        apply Finset.sum_congr rfl
        intro e _
        exact hterm e
  have hsum' : (∑ e ∈ star, y e) = G.boundary y v := by
    simpa only [← Finset.sum_filter, Finset.filter_univ_mem] using hsum
  calc
    G.boundary y v = ∑ e ∈ star, y e := hsum'.symm
    _ = ∑ e ∈ ({e₁, e₂} : Finset G.Edge), y e := by rw [hstar]
    _ = y e₁ + y e₂ := by simp [hne]



end Erdos1016.Proof.DegreeTwoParity
