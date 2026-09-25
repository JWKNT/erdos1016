import Erdos1016.Decomposition.TwoCore.CycleSupport
import Erdos1016.Decomposition.Regions.Basic

set_option autoImplicit false

/-!
# Paths and components of the full finite two-core

A simple path whose endpoints are in the two-core is contained in the core:
adding its support preserves minimum degree two. In particular the nonempty
two-core of a connected induced graph is connected.
-/

noncomputable section
namespace Erdos1016.Proof.TwoCorePathGeometry

open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.CycleSupport
open Erdos1016.SafeCore

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem degreeWithin_mono {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) {A B : Finset V} (hAB : A ⊆ B) (v : V) :
    degreeWithin J A v ≤ degreeWithin J B v := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

/-- Every simple path between vertices of the full two-core stays in the
core, provided it stays in the original region. -/
theorem path_support_subset_twoCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (region : Finset V)
    {u v : V} (p : J.Walk u v) (hp : p.IsPath)
    (hu : u ∈ vertices J region) (hv : v ∈ vertices J region)
    (hsupport : ∀ z ∈ p.support, z ∈ region) :
    ∀ z ∈ p.support, z ∈ vertices J region := by
  let C := vertices J region
  let A := C ∪ p.support.toFinset
  have hAreg : A ⊆ region := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact vertices_subset J region hz
    · exact hsupport z (List.mem_toFinset.mp hz)
  have hmin : MinTwo J A := by
    intro z hz
    by_cases hzC : z ∈ C
    · exact (vertices_minTwo J region z hzC).trans
        (degreeWithin_mono J Finset.subset_union_left z)
    · have hzpath : z ∈ p.support := by
        exact List.mem_toFinset.mp ((Finset.mem_union.mp hz).resolve_left hzC)
      obtain ⟨i, hi, hib⟩ := (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hzpath
      have hi0 : i ≠ 0 := by
        intro h
        have huz : u = z := by simpa [h] using hi
        exact hzC (huz ▸ hu)
      have hil : i < p.length := by
        have hine : i ≠ p.length := by
          intro h
          have hvz : v = z := by simpa [h] using hi
          exact hzC (hvz ▸ hv)
        omega
      have htwo := hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
      rw [hi] at htwo
      have hsub : p.toSubgraph.neighborSet z ⊆
          (↑(A.filter (fun w => J.Adj z w)) : Set V) := by
        intro w hw
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union_right _ (List.mem_toFinset.mpr
          ((p.mem_verts_toSubgraph).mp (p.toSubgraph.edge_vert hw.symm))),
          p.toSubgraph.adj_sub hw⟩
      have hcard := Set.ncard_le_ncard hsub
      rw [htwo] at hcard
      simpa only [Set.ncard_coe_Finset] using hcard
  have hAC := maximal J region A hAreg hmin
  intro z hz
  exact hAC (Finset.mem_union_right _ (List.mem_toFinset.mpr hz))







/-- A connected pruned region has at most one attachment incidence to the
full two-core. Two incidences would create either a core-to-core path or a
cycle through a pruned vertex, contradicting core maximality. -/
theorem outside_twoCore_attachment_unique
    (G : PhysicalGraph) (U R : Finset G.Vertex)
    (hR : ConnectedRegion G R) (hRU : R ⊆ U \ vertices G.toSimpleGraph U)
    {r s u v : G.Vertex} (hr : r ∈ R) (hs : s ∈ R)
    (hu : u ∈ vertices G.toSimpleGraph U) (hv : v ∈ vertices G.toSimpleGraph U)
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v) :
    r = s ∧ u = v := by
  have hconn := (connectedRegion_iff_induce_connected G R).mp hR
  obtain ⟨p, hp, _⟩ := hconn.exists_path_of_dist ⟨r, hr⟩ ⟨s, hs⟩
  let incl : G.toSimpleGraph.induce (↑R : Set G.Vertex) →g G.toSimpleGraph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  let q : G.toSimpleGraph.Walk r s := p.map incl
  have hq : q.IsPath :=
    (SimpleGraph.Walk.map_isPath_iff_of_injective Subtype.val_injective).mpr hp
  have hqR : ∀ z ∈ q.support, z ∈ R := by
    intro z hz
    obtain ⟨w, _, hwz⟩ : ∃ w, w ∈ p.support ∧ incl w = z := by
      simpa [q, SimpleGraph.Walk.support_map] using hz
    exact hwz ▸ w.2
  have hqU : ∀ z ∈ q.support, z ∈ U := fun z hz => (Finset.mem_sdiff.mp (hRU (hqR z hz))).1
  have huq : u ∉ q.support := fun h => (Finset.mem_sdiff.mp (hRU (hqR u h))).2 hu
  have hvq : v ∉ q.support := fun h => (Finset.mem_sdiff.mp (hRU (hqR v h))).2 hv
  let tail : G.toSimpleGraph.Walk r v := q.concat hsv
  have htail : tail.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [tail, List.concat_eq_append] using
      (List.nodup_append.mpr ⟨hq.support_nodup, by simp,
        by
          rw [List.disjoint_left]
          intro z hz hzv
          have : z = v := by simpa using hzv
          exact hvq (this ▸ hz)⟩)
  let w : G.toSimpleGraph.Walk u v := .cons hru.symm tail
  have hwU : ∀ z ∈ w.support, z ∈ U := by
    intro z hz
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons,
      tail, SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | hz | rfl
    · exact vertices_subset G.toSimpleGraph U hu
    · exact hqU z hz
    · exact vertices_subset G.toSimpleGraph U hv
  have hrw : r ∈ w.support := by
    simp only [w, SimpleGraph.Walk.support_cons, List.mem_cons]
    exact Or.inr tail.start_mem_support
  have hrnot := (Finset.mem_sdiff.mp (hRU hr)).2
  by_cases huv : u = v
  · subst v
    by_cases hrs : r = s
    · exact ⟨hrs, rfl⟩
    · have hcycle : w.IsCycle := by
        apply (SimpleGraph.Walk.cons_isCycle_iff tail hru.symm).mpr
        refine ⟨htail, ?_⟩
        intro hedge
        simp only [tail, SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hedge
        rcases hedge with hedge | hedge
        · exact huq (q.fst_mem_support_of_mem_edges hedge)
        · have hends := Sym2.eq_iff.mp hedge
          rcases hends with hends | hends
          · exact hru.ne hends.2
          · exact hrs hends.2
      have hsub := cycle_support_subset_twoCore G.toSimpleGraph G.toSimpleGraph U
        le_rfl w hcycle hwU
      exact (hrnot (hsub (Set.mem_toFinset.mpr ((w.mem_verts_toSubgraph).mpr hrw)))).elim
  · have hpath : w.IsPath := by
      apply htail.cons
      simpa only [tail, SimpleGraph.Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton, not_or] using
        And.intro huq huv
    exact (hrnot (path_support_subset_twoCore G.toSimpleGraph U w hpath hu hv hwU r hrw)).elim

end Erdos1016.Proof.TwoCorePathGeometry

end
