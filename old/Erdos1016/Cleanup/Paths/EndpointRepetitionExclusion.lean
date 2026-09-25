import Erdos1016.Cleanup.Paths.ThreeIncidentEdges
import Erdos1016.Cleanup.Paths.InternalRepetitionExclusion
import Erdos1016.Cleanup.Packing.CorridorPairedPathCertificates

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.EndpointRepetitionExclusion

open Erdos1016
open Erdos1016.Proof.PhysicalPartition
open Erdos1016.Proof.ThreeIncidentEdges
open Erdos1016.Proof.InternalRepetitionExclusion
open Erdos1016.Proof.CorridorPairedPathCertificates

variable {G : PhysicalGraph} {P₀ : Finset G.Vertex}

private theorem corridor_left_incident (C : PhysicalCorridor G)
    (i : Fin C.edges.length) :
    G.incident (C.edges.get ⟨i.val, i.isLt⟩)
      (C.vertices.get ⟨i.val, by rw [C.vertices_length]; omega⟩) := by
  rcases C.step i with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem corridor_right_incident (C : PhysicalCorridor G)
    (i : Fin C.edges.length) :
    G.incident (C.edges.get ⟨i.val, i.isLt⟩)
      (C.vertices.get ⟨i.val + 1, by rw [C.vertices_length]; omega⟩) := by
  rcases C.step i with h | h
  · exact Or.inr h.2
  · exact Or.inl h.2

/-- An open corridor cannot revisit its first vertex at an internal position
when every internal vertex is unprotected and has degree two. The initial
edge and the two edges at the repeated internal position would be three
distinct edges incident to that vertex. -/
theorem no_repeated_start_internal_vertex
    (C : PhysicalCorridor G)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ P₀)
    (hdegree : ∀ v, v ∉ P₀ → G.degree v = 2)
    (k : ℕ) (hkpos : 0 < k) (hkLast : k + 1 < C.vertices.length)
    (hvertex : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ =
      C.vertices.get ⟨k, by omega⟩) : False := by
  classical
  let v := C.vertices.get ⟨k, by omega⟩
  let e0 := C.edges.get ⟨0, by have := C.vertices_length; omega⟩
  let ePrev := C.edges.get ⟨k - 1, by have := C.vertices_length; omega⟩
  let eNext := C.edges.get ⟨k, by have := C.vertices_length; omega⟩
  have hkInterior : k - 1 < C.vertices.length - 2 := by
    have hlen := C.vertices_length
    omega
  have hvnotP : v ∉ P₀ := by
    simpa [v, show k - 1 + 1 = k by omega] using hinternal ⟨k - 1, hkInterior⟩
  have hvdegree : G.degree v = 2 := hdegree v hvnotP
  have hkge2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by omega
    subst k
    have hs := C.step ⟨0, by have hlen := C.vertices_length; omega⟩
    have hloop : G.src e0 = G.dst e0 := by
      rcases hs with hs | hs
      · calc
          G.src e0 = C.vertices.get ⟨0, by have hlen := C.vertices_length; omega⟩ := hs.1
          _ = C.vertices.get ⟨1, by omega⟩ := hvertex
          _ = G.dst e0 := hs.2.symm
      · calc
          G.src e0 = C.vertices.get ⟨1, by omega⟩ := hs.2
          _ = C.vertices.get ⟨0, by have hlen := C.vertices_length; omega⟩ := hvertex.symm
          _ = G.dst e0 := hs.1.symm
    exact G.noLoops e0 hloop
  have h0Prev : e0 ≠ ePrev := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : (0 : ℕ) = k - 1 := congrArg Fin.val hidx
    omega
  have h0Next : e0 ≠ eNext := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : (0 : ℕ) = k := congrArg Fin.val hidx
    omega
  have hPrevNext : ePrev ≠ eNext := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : k - 1 = k := congrArg Fin.val hidx
    omega
  have hinc0 : G.incident e0 v := by
    change G.incident (C.edges.get ⟨0, by have := C.vertices_length; omega⟩)
      (C.vertices.get ⟨k, by omega⟩)
    rw [← hvertex]
    exact corridor_left_incident C ⟨0, by have := C.vertices_length; omega⟩
  have hincPrev : G.incident ePrev v := by
    change G.incident (C.edges.get ⟨k - 1, by have := C.vertices_length; omega⟩)
      (C.vertices.get ⟨k, by omega⟩)
    have hsub : k - 1 + 1 = k := by omega
    simpa only [hsub] using
      corridor_right_incident C ⟨k - 1, by have := C.vertices_length; omega⟩
  have hincNext : G.incident eNext v := by
    exact corridor_left_incident C ⟨k, by have := C.vertices_length; omega⟩
  have hdegree3 := degree_ge_three_of_three_distinct_incident
    G v e0 ePrev eNext hinc0 hincPrev hincNext h0Prev h0Next hPrevNext
  omega

/-- The last endpoint also cannot recur at an internal position of an open
corridor. The final edge and the two edges at the repeated internal position
would be three distinct incident edges. -/
theorem no_repeated_end_internal_vertex
    (C : PhysicalCorridor G)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ P₀)
    (hdegree : ∀ v, v ∉ P₀ → G.degree v = 2)
    (k : ℕ) (hkpos : 0 < k) (hkLast : k + 1 < C.vertices.length)
    (hvertex : C.vertices.get ⟨k, by omega⟩ =
      C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩) :
    False := by
  classical
  let v := C.vertices.get ⟨k, by omega⟩
  let ePrev := C.edges.get ⟨k - 1, by have := C.vertices_length; omega⟩
  let eNext := C.edges.get ⟨k, by have := C.vertices_length; omega⟩
  have hkInterior : k - 1 < C.vertices.length - 2 := by
    have hlen := C.vertices_length
    omega
  have hvnotP : v ∉ P₀ := by
    simpa [v, show k - 1 + 1 = k by omega] using hinternal ⟨k - 1, hkInterior⟩
  have hvdegree : G.degree v = 2 := hdegree v hvnotP
  have hkBeforeLast : k + 1 < C.edges.length := by
    by_contra h
    have heq : k + 1 = C.edges.length := by
      have hlen := C.vertices_length
      omega
    have hvertex' : C.vertices.get ⟨k, by omega⟩ =
        C.vertices.get ⟨k + 1, by have := C.vertices_length; omega⟩ := by
      simpa [heq] using hvertex
    have hs := C.step ⟨k, by have hlen := C.vertices_length; omega⟩
    have hloop : G.src (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) =
        G.dst (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) := by
      rcases hs with hs | hs
      · calc
          G.src (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) =
              C.vertices.get ⟨k, by have := C.vertices_length; omega⟩ := hs.1
          _ = C.vertices.get ⟨k + 1, by have := C.vertices_length; omega⟩ := hvertex'
          _ = G.dst (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) := hs.2.symm
      · calc
          G.src (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) =
              C.vertices.get ⟨k + 1, by have := C.vertices_length; omega⟩ := hs.2
          _ = C.vertices.get ⟨k, by have := C.vertices_length; omega⟩ := hvertex'.symm
          _ = G.dst (C.edges.get ⟨k, by have := C.vertices_length; omega⟩) := hs.1.symm
    exact G.noLoops _ hloop
  let eLast := C.edges.get ⟨C.edges.length - 1,
    by have hlen := C.vertices_length; omega⟩
  have hPrevNext : ePrev ≠ eNext := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : k - 1 = k := congrArg Fin.val hidx
    omega
  have hPrevLast : ePrev ≠ eLast := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : k - 1 = C.edges.length - 1 := congrArg Fin.val hidx
    omega
  have hNextLast : eNext ≠ eLast := by
    intro he
    have hidx := (List.Nodup.get_inj_iff C.edges_nodup).mp he
    have hval : k = C.edges.length - 1 := congrArg Fin.val hidx
    omega
  have hincPrev : G.incident ePrev v := by
    change G.incident (C.edges.get ⟨k - 1, by have := C.vertices_length; omega⟩)
      (C.vertices.get ⟨k, by omega⟩)
    have hsub : k - 1 + 1 = k := by omega
    simpa only [hsub] using
      corridor_right_incident C ⟨k - 1, by have := C.vertices_length; omega⟩
  have hincNext : G.incident eNext v := by
    exact corridor_left_incident C ⟨k, by have := C.vertices_length; omega⟩
  have hincLast : G.incident eLast v := by
    change G.incident (C.edges.get ⟨C.edges.length - 1, by have := C.vertices_length; omega⟩)
      (C.vertices.get ⟨k, by omega⟩)
    rw [hvertex]
    have hsub : C.edges.length - 1 + 1 = C.edges.length := by
      have hlen := C.vertices_length
      omega
    simpa only [hsub] using
      corridor_right_incident C ⟨C.edges.length - 1,
        by have hlen := C.vertices_length; omega⟩
  have hdegree3 := degree_ge_three_of_three_distinct_incident
    G v ePrev eNext eLast hincPrev hincNext hincLast
      hPrevNext hPrevLast hNextLast
  omega

private theorem no_equal_ordered_positions
    (C : PhysicalCorridor G)
    (hendpoints : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ ≠
      C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ P₀)
    (hdegree : ∀ v, v ∉ P₀ → G.degree v = 2)
    (i j : Fin C.vertices.length) (hij : C.vertices.get i = C.vertices.get j)
    (hlt : i.val < j.val) : False := by
  have hij' : C.vertices.get ⟨i.val, i.isLt⟩ = C.vertices.get ⟨j.val, j.isLt⟩ := hij
  have hjle : j.val ≤ C.edges.length := by
    have hlen := C.vertices_length
    omega
  by_cases hi0 : i.val = 0
  · rcases eq_or_lt_of_le hjle with hjend | hjinner
    · have heq : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ =
          C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ := by
        simpa [hi0, hjend] using hij'
      exact hendpoints heq
    · have hstart : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ =
          C.vertices.get ⟨j.val, by omega⟩ := by
        simpa [hi0] using hij'
      exact no_repeated_start_internal_vertex C hinternal hdegree j.val
        (by omega) (by
          have hlen := C.vertices_length
          omega) hstart
  · have hiPos : 0 < i.val := by omega
    rcases eq_or_lt_of_le hjle with hjend | hjinner
    · have hend : C.vertices.get ⟨i.val, i.isLt⟩ =
          C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩ := by
        simpa [hjend] using hij'
      exact no_repeated_end_internal_vertex C hinternal hdegree i.val hiPos
        (by
          have hlen := C.vertices_length
          omega) hend
    · have hleftLast : i.val + 1 < C.vertices.length := by
        have hlen := C.vertices_length
        omega
      have hrightLast : j.val + 1 < C.vertices.length := by
        have hlen := C.vertices_length
        omega
      have hbothInternal : C.vertices.get ⟨i.val, by omega⟩ =
          C.vertices.get ⟨j.val, by omega⟩ := by
        simpa using hij'
      exact no_repeated_internal_vertex C hinternal hdegree i.val j.val
        hiPos hleftLast (by omega) hrightLast hlt hbothInternal

/-- If the corridor has distinct endpoints and every internal vertex is
unprotected of degree two, its vertex list is simple. The three possible
locations of a repeated pair are handled by the endpoint lemmas and the
internal-degree-two lemma. -/
theorem corridor_vertices_nodup_of_distinct_endpoints
    (C : PhysicalCorridor G)
    (hendpoints : C.vertices.get ⟨0, by have := C.vertices_length; omega⟩ ≠
      C.vertices.get ⟨C.edges.length, by have := C.vertices_length; omega⟩)
    (hinternal : ∀ i : Fin (C.vertices.length - 2),
      C.vertices.get ⟨i.val + 1, by have := C.vertices_length; omega⟩ ∉ P₀)
    (hdegree : ∀ v, v ∉ P₀ → G.degree v = 2) : C.vertices.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  by_contra hne
  have hvalne : i.val ≠ j.val := by
    intro h
    exact hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvalne with hlt | hgt
  · exact (no_equal_ordered_positions C hendpoints hinternal hdegree i j hij hlt).elim
  · exact (no_equal_ordered_positions C hendpoints hinternal hdegree j i hij.symm hgt).elim



end Erdos1016.Proof.EndpointRepetitionExclusion

end
