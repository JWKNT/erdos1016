import Erdos1016.ExactMaximumSupport.PathForestProbability
import Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
import Erdos1016.Probability.Avoidance.GeodesicMarker
import Erdos1016.ExactMaximum.NetBridge

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The marker supplied by an actual shortest path word

Physical handshaking identifies the number of used vertices. A simple selected
walk then has the same length as the ambient distance and uses exactly those
vertices. No representation by a shortest walk is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.GeodesicPathMarker
open FiniteMultiGraph BoundaryTrace BoundaryTrace.Network

local instance geodesicPathDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

def support (A : G.EdgeWord) : Finset G.Vertex :=
  Finset.univ.filter fun v => 0 < G.selectedDegree A v

@[simp] theorem mem_support (A : G.EdgeWord) (v : G.Vertex) :
    v ∈ support G A ↔ 0 < G.selectedDegree A v := by simp [support]

theorem selected_src_pos (A : G.EdgeWord) (e : G.Edge) (he : A e ≠ 0) :
    0 < G.selectedDegree A (G.src e) := by
  have h : 0 < ((Finset.univ.filter fun f : G.Edge => A f ≠ 0).filter
      fun f => G.src f = G.src e).card :=
    Finset.card_pos.mpr ⟨e, by simp [he]⟩
  exact h.trans_le (Nat.le_add_right _ _)

theorem selected_dst_pos (A : G.EdgeWord) (e : G.Edge) (he : A e ≠ 0) :
    0 < G.selectedDegree A (G.dst e) := by
  have h : 0 < ((Finset.univ.filter fun f : G.Edge => A f ≠ 0).filter
      fun f => G.dst f = G.dst e).card :=
    Finset.card_pos.mpr ⟨e, by simp [he]⟩
  exact h.trans_le (Nat.le_add_left _ _)

theorem selected_edge_internal (A : G.EdgeWord) (e : G.Edge) (he : A e ≠ 0) :
    e ∈ G.internalEdges (support G A) := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and, mem_support]
  exact ⟨selected_src_pos G A e he, selected_dst_pos G A e he⟩

theorem path_support_card (hloop : G.IsLoopless) {s t : G.Vertex} {A : G.EdgeWord}
    (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A)) :
    (support G A).card = Network.size A + 1 := by
  have hd (v : G.Vertex) : G.selectedDegree A v = G.looplessNetwork.deg (G.nonloopWord A) v :=
    G.selectedDegree_eq_deg A (fun e he => (hloop e he).elim) v
  have hs : G.selectedDegree A s = 1 := (hd s).trans hA.2.1
  have ht : G.selectedDegree A t = 1 := (hd t).trans hA.2.2.1
  have hpoint (v : G.Vertex) : G.selectedDegree A v + (if v = s then 1 else 0) +
      (if v = t then 1 else 0) = if 0 < G.selectedDegree A v then 2 else 0 := by
    by_cases hvs : v = s
    · subst v
      simp [hs, hA.1]
    by_cases hvt : v = t
    · subst v
      simp [ht, hA.1.symm]
    rcases hA.2.2.2.1 v hvs hvt with hv | hv
    · simp [hd v, hv, hvs, hvt]
    · simp [hd v, hv, hvs, hvt]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => hpoint v)
  have hr : (∑ v : G.Vertex, if 0 < G.selectedDegree A v then 2 else 0) =
      2 * (support G A).card := by
    rw [← Finset.sum_filter]
    simp [support, Nat.mul_comm]
  rw [hr, Finset.sum_add_distrib, Finset.sum_add_distrib, G.sum_selectedDegree] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  change 2 * Network.size A + 1 + 1 = 2 * (support G A).card at hsum
  omega

theorem walk_support_subset {A : G.EdgeWord} {u v : G.Vertex}
    (p : (G.selectedGraph A).Walk u v) (hu : u ∈ support G A) :
    p.support.toFinset ⊆ support G A := by
  induction p with
  | nil => simpa using hu
  | @cons u w v h p ih =>
    have hw : w ∈ support G A := by
      rcases h with ⟨hne, e, he, h | h⟩
      · exact (mem_support G A w).mpr (h.2 ▸ selected_dst_pos G A e he)
      · exact (mem_support G A w).mpr (h.1 ▸ selected_src_pos G A e he)
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih hw hx

/-- Every shortest physical path word has an ordinary shortest walk with exactly its vertex support. -/
theorem exists_geodesic (hloop : G.IsLoopless) {s t : G.Vertex} {A : G.EdgeWord}
    (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A))
    (hshort : Network.size A = G.toSimpleGraph.dist s t) :
    ∃ p : G.toSimpleGraph.Walk s t, p.length = G.toSimpleGraph.dist s t ∧
      p.support.toFinset = support G A := by
  have hs : s ∈ support G A := by
    rw [mem_support, G.selectedDegree_eq_deg A (fun e he => (hloop e he).elim), hA.2.1]
    decide
  have hr : (G.selectedGraph A).Reachable s t := by
    rw [G.selectedGraph_eq]
    apply hA.2.2.2.2 t
    rw [hA.2.2.1]
    decide
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have hsub := walk_support_subset G p hs
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support,
    path_support_card G hloop hA] at hcard
  let f : G.selectedGraph A →g G.toSimpleGraph := {
    toFun := id
    map_rel' := fun h => ⟨h.1, by obtain ⟨e, he, hh⟩ := h.2; exact ⟨e, hh⟩⟩ }
  let q := p.map f
  have hlen : q.length = G.toSimpleGraph.dist s t := by
    have hl := G.toSimpleGraph.dist_le q
    change G.toSimpleGraph.dist s t ≤ q.length at hl
    simp only [q, SimpleGraph.Walk.length_map] at hl ⊢
    omega
  have hsupport : q.support.toFinset = support G A := by
    have he : q.support = p.support := by
      rw [SimpleGraph.Walk.support_map]
      change List.map id p.support = p.support
      exact List.map_id p.support
    rw [he]
    apply Finset.eq_of_subset_of_card_le hsub
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support,
      path_support_card G hloop hA]
    simpa only [q, SimpleGraph.Walk.length_map, ← hshort] using
      Nat.add_le_add_right (Nat.le_of_eq hlen.symm) 1
  exact ⟨q, hlen, hsupport⟩

/-- The path marker has at most one vertex in every actual distance layer. -/
theorem marked_layer_card_le_one (hloop : G.IsLoopless) (hG : G.toSimpleGraph.Connected)
    {s t : G.Vertex} {A : G.EdgeWord}
    (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A))
    (hshort : Network.size A = G.toSimpleGraph.dist s t) (j : ℤ) :
    (Probability.LevelWindowBoundary.markedLayer G (support G A)
      (fun v => (G.toSimpleGraph.dist s v : ℤ)) j).card ≤ 1 := by
  obtain ⟨p, hp, hsupport⟩ := exists_geodesic G hloop hA hshort
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  apply Probability.GeodesicMarker.dist_injective_on_support hG p hp
  · exact List.mem_toFinset.mp (hsupport ▸ hu'.1)
  · exact List.mem_toFinset.mp (hsupport ▸ hv'.1)
  · have he : (G.toSimpleGraph.dist s u : ℤ) = (G.toSimpleGraph.dist s v : ℤ) :=
      hu'.2.trans hv'.2.symm
    exact_mod_cast he

/-- Incidences on disjoint sets of physical labels add to at most the ambient degree. -/
theorem selectedDegree_add_le (A B : G.EdgeWord)
    (hdisj : ∀ e, A e ≠ 0 → B e = 0) (v : G.Vertex) :
    G.selectedDegree A v + G.selectedDegree B v ≤ G.degree v := by
  simp only [degree, selectedDegree_eq_sum_endpoints, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases ha : A e = 0
  · by_cases hb : B e = 0 <;> simp [ha, hb]
  · simp [ha, hdisj e ha]

/-- Every path-marker vertex has at most one incidence outside the marker. -/
theorem outside_incidence_le_one (hloop : G.IsLoopless) {s t : G.Vertex} {A : G.EdgeWord}
    (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A))
    (hs : G.degree s ≤ 2) (ht : G.degree t ≤ 2)
    (hdeg : ∀ v, v ≠ s → v ≠ t → G.degree v ≤ 3) :
    ∀ v ∈ support G A,
      G.selectedDegree (ThinIntervalBoundary.outsideWord G (support G A)) v ≤ 1 := by
  intro v hv
  have hbound := selectedDegree_add_le G A (ThinIntervalBoundary.outsideWord G (support G A))
    (fun e he => by
      have hi := selected_edge_internal G A e he
      simp [ThinIntervalBoundary.outsideWord, restrictEdges, hi]) v
  have hd := G.selectedDegree_eq_deg A (fun e he => (hloop e he).elim) v
  by_cases hvs : v = s
  · subst v
    rw [hd, hA.2.1] at hbound
    omega
  by_cases hvt : v = t
  · subst v
    rw [hd, hA.2.2.1] at hbound
    omega
  have hvpos := (mem_support G A v).mp hv
  have hvdeg := hdeg v hvs hvt
  rcases hA.2.2.2.1 v hvs hvt with h | h
  · omega
  · omega

end Erdos1016.ExactMaximumSupport.GeodesicPathMarker
