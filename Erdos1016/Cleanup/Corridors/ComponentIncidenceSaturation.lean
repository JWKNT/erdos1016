import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ComponentIncidenceSaturation

open Erdos1016
open SimpleGraph
open Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge
open Erdos1016.Proof.PhysicalPartition

local instance {V : Type*} (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel _

private theorem incidentEdges_card_eq_degree (G : PhysicalGraph) (v : G.Vertex) :
    (incidentEdges G v).card = G.degree v := by
  classical
  letI := neighborFintype G v
  calc
    (incidentEdges G v).card = Fintype.card {e : G.Edge // e ∈ incidentEdges G v} :=
      (Fintype.card_coe (incidentEdges G v)).symm
    _ = Fintype.card {w : G.Vertex // w ∈ G.toSimpleGraph.neighborFinset v} :=
      Fintype.card_congr (incidentNeighborEquiv G v)
    _ = (G.toSimpleGraph.neighborFinset v).card := Fintype.card_coe _
    _ = G.degree v :=
      (PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v).symm

/-- At any internal corridor vertex of physical degree two, every incident
physical edge already belongs to the corridor. The two adjacent corridor steps
supply distinct incident labels, and simplicity plus degree two leaves no
third label. -/
theorem incident_edge_at_internal_vertex_mem_support
    (G : PhysicalGraph) (C : PhysicalCorridor G)
    (i : Fin (C.vertices.length - 2))
    (e : G.Edge)
    (hdegree : G.degree (C.vertices.get ⟨i.val + 1, by
      have hlen := C.vertices_length
      omega⟩) = 2)
    (he : G.incident e (C.vertices.get ⟨i.val + 1, by
      have hlen := C.vertices_length
      omega⟩)) :
    e ∈ C.support := by
  classical
  let j₀ : Fin C.edges.length := ⟨i.val, by
    have hlen := C.vertices_length
    omega⟩
  let j₁ : Fin C.edges.length := ⟨i.val + 1, by
    have hlen := C.vertices_length
    omega⟩
  let e₀ := C.edges.get j₀
  let e₁ := C.edges.get j₁
  have hidx : j₀ ≠ j₁ := by
    intro hh
    have : i.val = i.val + 1 := congrArg Fin.val hh
    omega
  have hedges_ne : e₀ ≠ e₁ := by
    intro hh
    have hh' := C.edges_nodup.get_inj_iff.mp hh
    exact hidx hh'
  have hv0 : G.incident e₀
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) := by
    have hs := C.step j₀
    dsimp [e₀, j₀] at hs
    rcases hs with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  have hv1 : G.incident e₁
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) := by
    have hs := C.step j₁
    dsimp [e₁, j₁] at hs
    rcases hs with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have he₀ : e₀ ∈ incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv0⟩
  have he₁ : e₁ ∈ incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv1⟩
  have hsub : ({e₀, e₁} : Finset G.Edge) ⊆ incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact he₀
    · exact he₁
  have hcard : ({e₀, e₁} : Finset G.Edge).card = 2 := by
    simp [hedges_ne]
  have hinc_card : (incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩)).card = 2 := by
    rw [incidentEdges_card_eq_degree, hdegree]
  have heq : ({e₀, e₁} : Finset G.Edge) = incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hinc_card, hcard]
  have he' : e ∈ incidentEdges G
      (C.vertices.get ⟨i.val + 1, by
        have hlen := C.vertices_length
        omega⟩) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  rw [← heq] at he'
  simp only [Finset.mem_insert, Finset.mem_singleton] at he'
  rcases he' with rfl | rfl
  · change C.edges.get j₀ ∈ C.edges.toFinset
    exact List.mem_toFinset.mpr (List.get_mem _ _)
  · change C.edges.get j₁ ∈ C.edges.toFinset
    exact List.mem_toFinset.mpr (List.get_mem _ _)


/-- The physical corridor supplied for an unprotected component contains
 every physical edge incident to any vertex of that component. Every such
vertex is an internal corridor vertex, and its two adjacent corridor steps
already exhaust its ambient degree-two incidence set. -/
theorem component_incident_edge_mem_support
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hdegree : ∀ v, v ∉ P → G.degree v = 2)
    (c : (G.toSimpleGraph.induce {v | v ∉ P}).ConnectedComponent)
    (a b u w : G.Vertex) (p : G.toSimpleGraph.Walk a b)
    (Ccorr : PhysicalCorridor G)
    (hsupport : p.support.toFinset = (c.supp.toFinset).map
      (Function.Embedding.subtype {v | v ∉ P}))
    (hverts : Ccorr.vertices = u :: p.support ++ [w]) :
    ∀ e : G.Edge,
      (G.src e ∈ (c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P}) ∨
       G.dst e ∈ (c.supp.toFinset).map
          (Function.Embedding.subtype {v | v ∉ P})) →
      e ∈ Ccorr.support := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let X : Finset G.Vertex := (c.supp.toFinset).map
    (Function.Embedding.subtype U)
  have hX_unprotected : ∀ v ∈ X, v ∉ P := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hv
    exact z.2
  intro e he
  rcases he with hs | ht
  · have hspath : G.src e ∈ p.support := by
      have hmem : G.src e ∈ p.support.toFinset := hsupport ▸ hs
      simpa using hmem
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hspath
    have hlen : Ccorr.vertices.length - 2 = p.support.length := by
      rw [hverts]
      simp
    let i : Fin (Ccorr.vertices.length - 2) := ⟨j.val, by
      rw [hlen]
      exact j.isLt⟩
    have hvertexElem : Ccorr.vertices[j.val + 1] = G.src e := by
      simpa [hverts, List.get_eq_getElem, List.getElem_append_left j.isLt] using hj
    have hvertex : Ccorr.vertices.get ⟨i.val + 1, by
        have hvl := Ccorr.vertices_length
        omega⟩ = G.src e := by
      simpa [i, List.get_eq_getElem] using hvertexElem
    have hsrcP : G.src e ∉ P := hX_unprotected (G.src e) hs
    exact incident_edge_at_internal_vertex_mem_support G Ccorr i e
      (by rw [hvertex]; exact hdegree (G.src e) hsrcP)
      (by rw [hvertex]; exact Or.inl rfl)
  · have hspath : G.dst e ∈ p.support := by
      have hmem : G.dst e ∈ p.support.toFinset := hsupport ▸ ht
      simpa using hmem
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hspath
    have hlen : Ccorr.vertices.length - 2 = p.support.length := by
      rw [hverts]
      simp
    let i : Fin (Ccorr.vertices.length - 2) := ⟨j.val, by
      rw [hlen]
      exact j.isLt⟩
    have hvertexElem : Ccorr.vertices[j.val + 1] = G.dst e := by
      simpa [hverts, List.get_eq_getElem, List.getElem_append_left j.isLt] using hj
    have hvertex : Ccorr.vertices.get ⟨i.val + 1, by
        have hvl := Ccorr.vertices_length
        omega⟩ = G.dst e := by
      simpa [i, List.get_eq_getElem] using hvertexElem
    have hdstP : G.dst e ∉ P := hX_unprotected (G.dst e) ht
    exact incident_edge_at_internal_vertex_mem_support G Ccorr i e
      (by rw [hvertex]; exact hdegree (G.dst e) hdstP)
      (by rw [hvertex]; exact Or.inr rfl)








end Erdos1016.Proof.ComponentIncidenceSaturation

end
