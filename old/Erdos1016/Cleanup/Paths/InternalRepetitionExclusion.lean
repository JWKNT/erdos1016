import Erdos1016.Cleanup.Corridors.PhysicalPartition
import Erdos1016.Graph.PhysicalDegree

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.InternalRepetitionExclusion

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge

variable {G : PhysicalGraph} {P₀ : Finset G.Vertex}

private theorem degree_eq_incidentEdges_card (v : G.Vertex) :
    G.degree v = (incidentEdges G v).card := by
  classical
  unfold incidentEdges PhysicalGraph.degree PhysicalGraph.selectedDegree
  congr 1
  ext e
  simp [PhysicalGraph.incident]





/-- A corridor cannot visit the same unprotected degree-two vertex at two
distinct internal positions. Each occurrence uses the two incident edge
labels; physical simplicity and `edges_nodup` make the resulting pair
equality impossible. -/
theorem no_repeated_internal_vertex
    (C : PhysicalCorridor G)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ P₀)
    (hdegree : ∀ v, v ∉ P₀ → G.degree v = 2)
    (k l : ℕ) (hleftK : 0 < k) (hrightK : k + 1 < C.vertices.length)
    (hleftL : 0 < l) (hrightL : l + 1 < C.vertices.length)
    (hkl : k < l)
    (hvertex : C.vertices.get ⟨k, by omega⟩ = C.vertices.get ⟨l, by omega⟩) :
    False := by
  classical
  let v := C.vertices.get ⟨k, by omega⟩
  let eₖₗ := C.edges.get ⟨k - 1, by have := C.vertices_length; omega⟩
  let eₖᵣ := C.edges.get ⟨k, by have := C.vertices_length; omega⟩
  let eₗₗ := C.edges.get ⟨l - 1, by have := C.vertices_length; omega⟩
  let eₗᵣ := C.edges.get ⟨l, by have := C.vertices_length; omega⟩
  let pairK : Finset G.Edge := {eₖₗ, eₖᵣ}
  let pairL : Finset G.Edge := {eₗₗ, eₗᵣ}
  have hkInternal : k - 1 < C.vertices.length - 2 := by
    have := C.vertices_length
    omega
  have hvnotP : v ∉ P₀ := by
    simpa [v, show k - 1 + 1 = k by omega] using hinternal ⟨k - 1, hkInternal⟩
  have hvdegree : G.degree v = 2 := hdegree v hvnotP
  have hleftDistinct : eₖₗ ≠ eₖᵣ := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have : k - 1 = k := congrArg Fin.val hidx
    omega
  have hrightDistinct : eₗₗ ≠ eₗᵣ := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have : l - 1 = l := congrArg Fin.val hidx
    omega
  have hincidentₖₗ : G.incident eₖₗ v := by
    have hs := C.step ⟨k - 1, by have := C.vertices_length; omega⟩
    have hsub : k - 1 + 1 = k := by omega
    simp only [hsub] at hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa [v, eₖₗ] using hs.2)
    · exact Or.inl (by simpa [v, eₖₗ] using hs.2)
  have hincidentₖᵣ : G.incident eₖᵣ v := by
    rcases C.step ⟨k, by have := C.vertices_length; omega⟩ with hs | hs
    · exact Or.inl (by simpa [v, eₖᵣ] using hs.1)
    · exact Or.inr (by simpa [v, eₖᵣ] using hs.1)
  have hincidentₗₗ : G.incident eₗₗ v := by
    have hs := C.step ⟨l - 1, by have := C.vertices_length; omega⟩
    have hsub : l - 1 + 1 = l := by omega
    simp only [hsub] at hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa [v, eₗₗ] using hs.2.trans hvertex.symm)
    · exact Or.inl (by simpa [v, eₗₗ] using hs.2.trans hvertex.symm)
  have hincidentₗᵣ : G.incident eₗᵣ v := by
    rcases C.step ⟨l, by have := C.vertices_length; omega⟩ with hs | hs
    · exact Or.inl (by simpa [v, eₗᵣ] using hs.1.trans hvertex.symm)
    · exact Or.inr (by simpa [v, eₗᵣ] using hs.1.trans hvertex.symm)
  have hpairKsub : pairK ⊆ incidentEdges G v := by
    intro e he
    simp only [pairK, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincidentₖₗ⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincidentₖᵣ⟩
  have hpairLsub : pairL ⊆ incidentEdges G v := by
    intro e he
    simp only [pairL, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincidentₗₗ⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hincidentₗᵣ⟩
  have hpairKcard : pairK.card = 2 := by simp [pairK, hleftDistinct]
  have hpairLcard : pairL.card = 2 := by simp [pairL, hrightDistinct]
  have hcard : (incidentEdges G v).card = 2 := by
    rw [← degree_eq_incidentEdges_card, hvdegree]
  have hpairKeq : pairK = incidentEdges G v := by
    apply Finset.eq_of_subset_of_card_le hpairKsub
    rw [hcard, hpairKcard]
  have hpairLeq : pairL = incidentEdges G v := by
    apply Finset.eq_of_subset_of_card_le hpairLsub
    rw [hcard, hpairLcard]
  have hmemK : eₖₗ ∈ pairK := by simp [pairK]
  have hpairs : pairK = pairL := hpairKeq.trans hpairLeq.symm
  have hmemL : eₖₗ ∈ pairL := by
    rw [← hpairs]
    exact hmemK
  simp only [pairL, Finset.mem_insert, Finset.mem_singleton] at hmemL
  rcases hmemL with heq | heq
  · have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp heq
    have : k - 1 = l - 1 := congrArg Fin.val hidx
    omega
  · have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp heq
    have : k - 1 = l := congrArg Fin.val hidx
    omega


end Erdos1016.Proof.InternalRepetitionExclusion

end
