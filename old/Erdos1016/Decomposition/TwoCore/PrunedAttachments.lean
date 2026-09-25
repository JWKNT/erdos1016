import Erdos1016.Decomposition.TwoCore.PathConvexity
import Erdos1016.Cycles.Geometry.BoundaryContactGeometry

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.PrunedCoreAttachments

open Erdos1016.SafeCore Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.TwoCorePathGeometry
open Erdos1016.Proof.ConditionalComplementGeometry

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A cubic vertex with two neighbors left in the core has a literal lost
neighbor in the original graph. -/
theorem degreeTwo_has_lost_neighbor
    (G : PhysicalGraph) (K : Finset G.Vertex) (v : G.Vertex)
    (hcubic : G.degree v = 3) (hdegree : degreeWithin G.toSimpleGraph K v = 2) :
    ∃ w, G.toSimpleGraph.Adj v w ∧ w ∉ K := by
  by_contra hnot
  push_neg at hnot
  have hsets : G.toSimpleGraph.neighborFinset v = K.filter (G.toSimpleGraph.Adj v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hnot w h, h⟩, fun h => h.2⟩
  have hgraph := original_degree_eq_graph_degree G v
  have hcard := G.toSimpleGraph.card_neighborFinset_eq_degree v
  rw [hsets] at hcard
  change degreeWithin G.toSimpleGraph K v = G.toSimpleGraph.degree v at hcard
  omega

/-- A component pruned from the old core and attached at a vertex of the
new cycle becomes a literal component after that cycle is deleted. -/
theorem pruned_attachment_is_new_component
    (G : PhysicalGraph) (U D R : Finset G.Vertex)
    (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ)
    (hR : R ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ))
    {v w : G.Vertex} (hv : v ∈ D) (hw : w ∈ R) (hvw : G.toSimpleGraph.Adj v w) :
    R ∈ components G (U ∪ D)ᶜ := by
  have hRU := component_subset G hR
  apply (mem_components G (U ∪ D)ᶜ R).mpr
  refine ⟨?_, component_connected G hR, ?_⟩
  · intro z hz
    obtain ⟨hzU, hzK⟩ := Finset.mem_sdiff.mp (hRU hz)
    apply Finset.mem_compl.mpr
    intro hzUD
    rcases Finset.mem_union.mp hzUD with hzU' | hzD
    · exact Finset.mem_compl.mp hzU hzU'
    · exact hzK (hDK hzD)
  · intro z hz t ht hzt
    have htU : t ∈ Uᶜ := Finset.mem_compl.mpr
      (fun htU => Finset.mem_compl.mp ht (Finset.mem_union_left _ htU))
    by_cases htK : t ∈ vertices G.toSimpleGraph Uᶜ
    · have heq := outside_twoCore_attachment_unique G Uᶜ R
        (component_connected G hR) hRU hz hw htK (hDK hv) hzt hvw.symm
      exact (Finset.mem_compl.mp ht (Finset.mem_union_right _ (heq.2 ▸ hv))).elim
    · exact component_closed G hR z hz t (Finset.mem_sdiff.mpr ⟨htU, htK⟩) hzt

/-- Distinct core vertices cannot lose incidences to the same pruned tree. -/
theorem pruned_component_attachment_vertex_unique
    (G : PhysicalGraph) (U R : Finset G.Vertex)
    (hR : R ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ))
    {v v' w w' : G.Vertex}
    (hv : v ∈ vertices G.toSimpleGraph Uᶜ)
    (hv' : v' ∈ vertices G.toSimpleGraph Uᶜ)
    (hw : w ∈ R) (hw' : w' ∈ R)
    (hvw : G.toSimpleGraph.Adj v w) (hvw' : G.toSimpleGraph.Adj v' w') : v = v' :=
  (outside_twoCore_attachment_unique G Uᶜ R (component_connected G hR)
    (component_subset G hR) hw hw' hv hv' hvw.symm hvw'.symm).2

/-- A cubic tree whose only contact to `D` is one edge must also meet the
previously deleted region `U`. -/
theorem cubic_tree_contacts_previous_region
    (G : PhysicalGraph) (U D R : Finset G.Vertex)
    (hR : R ∈ components G (U ∪ D)ᶜ)
    (hcubic : ∀ v ∈ R, G.degree v = 3)
    (htree : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic)
    (hunique : ∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f) :
    (crossing G R U).Nonempty := by
  by_contra hn
  have htip : ∀ e : ownerCut G R, boundaryTip G R e ∈ D := by
    intro e
    have hUD : boundaryTip G R e ∈ U ∪ D := by
      by_contra h
      exact boundaryTip_not_mem G R e (component_closed G hR _ (boundaryBase G R e).2
        _ (Finset.mem_compl.mpr h) (boundary_adj G R e))
    rcases Finset.mem_union.mp hUD with hu | hd
    · exact (hn ((crossing_nonempty_iff G R U).mpr
        ⟨_, (boundaryBase G R e).2, _, hu, boundary_adj G R e⟩)).elim
    · exact hd
  have hsub : ownerCut G R ⊆ crossing G R D := by
    intro e he
    let e' : ownerCut G R := ⟨e, he⟩
    apply (mem_crossing G R D e).mpr
    rcases boundary_endpoints G R e' with h | h
    · exact Or.inl ⟨h.1 ▸ (boundaryBase G R e').2, h.2 ▸ htip e'⟩
    · exact Or.inr ⟨h.1 ▸ htip e', h.2 ▸ (boundaryBase G R e').2⟩
  have hcut : cutSize G R ≤ 1 := (Finset.card_le_card hsub).trans
    (Finset.card_le_one.mpr (fun e he f hf => hunique e f he hf))
  rw [cubic_tree_cut G hcubic (component_connected G hR) htree] at hcut
  omega

/-- The route from a new-cycle vertex through a small complementary tree to
an old deleted vertex is simple, short, and has all internal vertices in the
tree. These are the literal paths used for the degree-two labels. -/
theorem short_route_through_small_component
    (G : PhysicalGraph) (U D R : Finset G.Vertex) (K : ℕ)
    (hUD : Disjoint U D) (hR : R ∈ components G (U ∪ D)ᶜ)
    (hsize : R.card + 2 ≤ K) (hcontact : (crossing G R U).Nonempty)
    {v w : G.Vertex} (hv : v ∈ D) (hw : w ∈ R) (hvw : G.toSimpleGraph.Adj v w) :
    ∃ u ∈ U, ∃ p : G.toSimpleGraph.Walk v u,
      p.IsPath ∧ p.length ≤ K - 1 ∧
      ∀ z ∈ p.support, z = v ∨ z = u ∨ z ∈ R := by
  obtain ⟨r, hr, u, hu, hru⟩ := (crossing_nonempty_iff G R U).mp hcontact
  have hconn := (connectedRegion_iff_induce_connected G R).mp (component_connected G hR)
  obtain ⟨p, hp, _⟩ := hconn.exists_path_of_dist ⟨w, hw⟩ ⟨r, hr⟩
  let incl : G.toSimpleGraph.induce (↑R : Set G.Vertex) →g G.toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let q : G.toSimpleGraph.Walk w r := p.map incl
  have hq : q.IsPath :=
    (SimpleGraph.Walk.map_isPath_iff_of_injective Subtype.val_injective).mpr hp
  have hqR : ∀ z ∈ q.support, z ∈ R := by
    intro z hz
    obtain ⟨a, _, haz⟩ : ∃ a, a ∈ p.support ∧ incl a = z := by
      simpa [q, SimpleGraph.Walk.support_map] using hz
    exact haz ▸ a.2
  have houtside (z : G.Vertex) (hz : z ∈ U ∪ D) : z ∉ q.support := by
    intro hzq
    exact Finset.mem_compl.mp (component_subset G hR (hqR z hzq)) hz
  have huq := houtside u (Finset.mem_union_left _ hu)
  have hvq := houtside v (Finset.mem_union_right _ hv)
  have hvu : v ≠ u := fun h => Finset.disjoint_left.mp hUD (h ▸ hu) hv
  let tail := q.concat hru
  have htail : tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [tail, List.concat_eq_append] using
      (List.nodup_append.mpr ⟨hq.support_nodup, by simp, by
        rw [List.disjoint_left]
        intro z hz hzu
        have : z = u := by simpa using hzu
        exact huq (this ▸ hz)⟩)
  let route : G.toSimpleGraph.Walk v u := .cons hvw tail
  have hroute : route.IsPath := by
    apply htail.cons
    simpa only [tail, SimpleGraph.Walk.support_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton, not_or] using And.intro hvq hvu
  have hcardInduced : Fintype.card (↑R : Set G.Vertex) = R.card :=
    Fintype.card_ofFinset R (by intro v; rfl)
  have hplen : p.length < R.card := by simpa only [hcardInduced] using hp.length_lt
  have hrlen : route.length = p.length + 2 := by simp [route, tail, q]
  refine ⟨u, hu, route, hroute, by omega, ?_⟩
  intro z hz
  simp only [route, SimpleGraph.Walk.support_cons, List.mem_cons, tail,
    SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append,
    List.mem_singleton, List.not_mem_nil, or_false] at hz
  rcases hz with hz | hz | hz
  · exact Or.inl hz
  · exact Or.inr (Or.inr (hqR z hz))
  · exact Or.inr (Or.inl hz)

/-- A lost incidence either goes directly to an old cycle, goes into the
unique exceptional pruned component containing the giant, or supplies an
actual short label path through a small pruned tree. -/
theorem lost_incidence_route_or_giant
    (G : PhysicalGraph) (U D B : Finset G.Vertex) (K : ℕ)
    (hUD : Disjoint U D) (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    {v w : G.Vertex} (hv : v ∈ D) (hvw : G.toSimpleGraph.Adj v w)
    (hwK : w ∉ vertices G.toSimpleGraph Uᶜ) :
    w ∈ U ∨ ∃ R ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ), w ∈ R ∧
      (R = B ∨ ∃ u ∈ U, ∃ p : G.toSimpleGraph.Walk v u,
        p.IsPath ∧ p.length ≤ K - 1 ∧
        ∀ z ∈ p.support, z = v ∨ z = u ∨ z ∈ R) := by
  by_cases hwU : w ∈ U
  · exact Or.inl hwU
  · right
    obtain ⟨R, hR, hwR⟩ := components_cover G
      (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hwU, hwK⟩)
    refine ⟨R, hR, hwR, ?_⟩
    by_cases hRB : R = B
    · exact Or.inl hRB
    · right
      have hRnew := pruned_attachment_is_new_component G U D R hDK hR hv hwR hvw
      obtain ⟨htree, hcubic, hsize, hunique⟩ := hsmall R hRnew hRB
      have hcontact := cubic_tree_contacts_previous_region G U D R hRnew hcubic htree hunique
      exact short_route_through_small_component G U D R K hUD hRnew hsize hcontact hv hwR hvw

/-- The potential unlabelled vertices are attachments to the one pruned
component equal to the new giant. -/
def exceptionalAttachments (G : PhysicalGraph) (U D B : Finset G.Vertex) :
    Finset G.Vertex := D.filter (fun v =>
      B ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ) ∧
      ∃ w ∈ B, G.toSimpleGraph.Adj v w)

theorem exceptionalAttachments_card_le_one
    (G : PhysicalGraph) (U D B : Finset G.Vertex)
    (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ) :
    (exceptionalAttachments G U D B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv v' hv'
  obtain ⟨hvD, hB, w, hw, hvw⟩ := Finset.mem_filter.mp hv
  obtain ⟨hv'D, _, w', hw', hvw'⟩ := Finset.mem_filter.mp hv'
  exact pruned_component_attachment_vertex_unique G U B hB
    (hDK hvD) (hDK hv'D) hw hw' hvw hvw'

/-- Every nonexceptional degree-two vertex has a short path to the old
selected support. The path has either no internal vertices, or all its
internal vertices lie in its own attached pruned component. -/
theorem degreeTwo_nonexceptional_has_short_route
    (G : PhysicalGraph) (U D B : Finset G.Vertex) (K : ℕ) (hK : 2 ≤ K)
    (hUD : Disjoint U D) (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    (v : G.Vertex) (hv : v ∈ D) (hcubic : G.degree v = 3)
    (hdegree : degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph Uᶜ) v = 2)
    (hexception : v ∉ exceptionalAttachments G U D B) :
    ∃ u ∈ U, ∃ R : Finset G.Vertex,
      (R = ∅ ∨ R ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ) ∧
        ∃ w ∈ R, G.toSimpleGraph.Adj v w) ∧
      ∃ p : G.toSimpleGraph.Walk v u, p.IsPath ∧ p.length ≤ K - 1 ∧
        ∀ z ∈ p.support, z = v ∨ z = u ∨ z ∈ R := by
  obtain ⟨w, hvw, hwK⟩ := degreeTwo_has_lost_neighbor G _ v hcubic hdegree
  rcases lost_incidence_route_or_giant G U D B K hUD hDK hsmall hv hvw hwK with
    hwU | ⟨R, hR, hwR, hRB | hroute⟩
  · refine ⟨w, hwU, ∅, Or.inl rfl, .cons hvw .nil, ?_, ?_, ?_⟩
    · exact SimpleGraph.Walk.IsPath.of_adj hvw
    · simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      omega
    · intro z hz
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz
      exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))
  · subst R
    exact (hexception (Finset.mem_filter.mpr ⟨hv, hR, w, hwR, hvw⟩)).elim
  · obtain ⟨u, hu, p, hp, hplen, hsup⟩ := hroute
    exact ⟨u, hu, R, Or.inr ⟨hR, w, hwR, hvw⟩, p, hp, hplen, hsup⟩

end Erdos1016.Proof.PrunedCoreAttachments

end
