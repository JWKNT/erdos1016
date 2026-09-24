import Erdos1016.Decomposition.Regions.CutIncidences
import Erdos1016.Graph.PhysicalDegree
import Erdos1016.Cleanup.Support.VertexSupportedWitness

set_option autoImplicit false

/-!
# Regions traced by two paths

This module derives cyclicity and the two-cut bound from a paired-path
certificate. The walks are recorded in the induced host graph on the region;
the induced embedding maps them to walks in the physical host graph.
-/

noncomputable section

namespace Erdos1016.Proof.PairedPathRegions

open Erdos1016
open SimpleGraph

local instance (G : PhysicalGraph) (v : G.Vertex) :
    Fintype (G.toSimpleGraph.neighborSet v) :=
  PhysicalSimpleGraphDegreeBridge.neighborFintype G v

variable (G : PhysicalGraph) (U : Finset G.Vertex)

/-- Two simple paths in the induced host region, with distinct common
endpoints, disjoint interiors and edges, and covering the region. -/
structure PairedPathCertificate (G : PhysicalGraph) (U : Finset G.Vertex) where
  source : {v : G.Vertex // v ∈ U}
  target : {v : G.Vertex // v ∈ U}
  endpoints_ne : source.1 ≠ target.1
  path₁ : (G.toSimpleGraph.induce (U : Set G.Vertex)).Walk source target
  path₂ : (G.toSimpleGraph.induce (U : Set G.Vertex)).Walk source target
  path₁_simple : path₁.IsPath
  path₂_simple : path₂.IsPath
  interiors_disjoint :
    Disjoint path₁.support.tail.toFinset path₂.reverse.support.tail.toFinset
  edges_disjoint : Disjoint path₁.edges.toFinset path₂.edges.toFinset
  covers_region : ∀ w : {v : G.Vertex // v ∈ U},
    w ∈ path₁.support ∨ w ∈ path₂.support

namespace PairedPathCertificate

variable {G U}

private theorem append_support_tail_nodup (P : PairedPathCertificate G U) :
    (P.path₁.append P.path₂.reverse).support.tail.Nodup := by
  rw [Walk.tail_support_append]
  apply List.Nodup.append
  · exact P.path₁_simple.support_nodup.tail
  · exact P.path₂_simple.reverse.support_nodup.tail
  · apply List.disjoint_left.mpr
    intro w hw₁ hw₂
    exact (Finset.disjoint_left.mp P.interiors_disjoint)
      (List.mem_toFinset.mpr hw₁) (List.mem_toFinset.mpr hw₂)

private theorem append_isTrail (P : PairedPathCertificate G U) :
    (P.path₁.append P.path₂.reverse).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append]
  apply List.nodup_append.mpr
  refine ⟨P.path₁_simple.isTrail.edges_nodup, ?_, ?_⟩
  · exact (Walk.IsTrail.reverse P.path₂ P.path₂_simple.isTrail).edges_nodup
  · intro e he₁ he₂
    have h₁ : e ∈ P.path₁.edges.toFinset := List.mem_toFinset.mpr he₁
    have h₂r : e ∈ P.path₂.reverse.edges.toFinset := List.mem_toFinset.mpr he₂
    have h₂ : e ∈ P.path₂.edges.toFinset := by simpa using h₂r
    exact (Finset.disjoint_left.mp P.edges_disjoint) h₁ h₂

private theorem append_isCycle (P : PairedPathCertificate G U) :
    (P.path₁.append P.path₂.reverse).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨P.append_isTrail, ?_, P.append_support_tail_nodup⟩
  intro hnil
  have hlen := congrArg Walk.length hnil
  have hpath : P.path₁.length = 0 := by
    have := Walk.length_append P.path₁ P.path₂.reverse
    rw [this] at hlen
    simp at hlen
    omega
  have hend := Walk.eq_of_length_eq_zero hpath
  exact P.endpoints_ne (congrArg Subtype.val hend)

private theorem append_support_covers (P : PairedPathCertificate G U)
    (w : {v : G.Vertex // v ∈ U}) :
    w ∈ (P.path₁.append P.path₂.reverse).support := by
  rcases P.covers_region w with hp | hq
  · rw [Walk.support_append]
    exact List.mem_append.mpr (Or.inl hp)
  · have hr : w ∈ P.path₂.reverse.support := by
      rw [Walk.support_reverse]
      exact List.mem_reverse.mpr hq
    rcases (Walk.mem_support_iff (p := P.path₂.reverse)).mp hr with hstart | htail
    · rw [Walk.support_append]
      apply List.mem_append.mpr
      left
      subst w
      have ht : P.target ∈ P.path₁.support := by
        rw [Walk.mem_support_iff_exists_getVert]
        exact ⟨P.path₁.length, Walk.getVert_length P.path₁, le_rfl⟩
      exact ht
    · rw [Walk.support_append]
      exact List.mem_append.mpr (Or.inr htail)

/-- The path certificate gives every region vertex at least two internal
neighbors. The concatenated cycle supplies those neighbors uniformly,
including at its common endpoints. -/
theorem internalNeighborCount_ge_two (P : PairedPathCertificate G U) :
    ∀ v ∈ U, 2 ≤ (G.toSimpleGraph.neighborFinset v ∩ U).card := by
  classical
  intro v hv
  let w : {x : G.Vertex // x ∈ U} := ⟨v, hv⟩
  let c := P.path₁.append P.path₂.reverse
  have hw : w ∈ c.support := by
    simpa [c] using P.append_support_covers w
  have hcycle : c.IsCycle := by
    simpa [c] using P.append_isCycle
  let f : (G.toSimpleGraph.induce (U : Set G.Vertex)) ↪g G.toSimpleGraph :=
    SimpleGraph.Embedding.induce (G := G.toSimpleGraph) (U : Set G.Vertex)
  let c' := Walk.map f.toHom c
  have hc' : c'.IsCycle :=
    (Walk.map_isCycle_iff_of_injective f.injective).2 hcycle
  have hvC : v ∈ c'.support.toFinset := by
    apply List.mem_toFinset.mpr
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  let K : SimpleGraph G.Vertex := c'.toSubgraph.spanningCoe
  have hKcycles : K.IsCycles :=
    Walk.IsCycle.isCycles_spanningCoe_toSubgraph hc'
  have hcycleCard : (K.neighborFinset v).card = 2 := by
    have hnc := hc'.ncard_neighborSet_toSubgraph_eq_two
      (List.mem_toFinset.mp hvC)
    rw [Set.ncard_eq_toFinset_card] at hnc
    simpa [K, SimpleGraph.neighborFinset] using hnc
  have hneigh_subset : K.neighborFinset v ⊆ G.toSimpleGraph.neighborFinset v := by
    intro z hz
    apply (SimpleGraph.mem_neighborFinset G.toSimpleGraph v z).mpr
    have hadjK : K.Adj v z := (SimpleGraph.mem_neighborFinset K v z).mp hz
    exact c'.toSubgraph.adj_sub (by
      simpa [K, SimpleGraph.Subgraph.spanningCoe_adj] using hadjK)
  have hneigh_U : ∀ z ∈ K.neighborFinset v, z ∈ U := by
    intro z hz
    have hadjK : K.Adj v z := (SimpleGraph.mem_neighborFinset K v z).mp hz
    have hadj : c'.toSubgraph.Adj v z := by
      simpa [K, SimpleGraph.Subgraph.spanningCoe_adj] using hadjK
    have hver := c'.toSubgraph.edge_vert (v := z) (w := v)
      (c'.toSubgraph.symm hadj)
    have hvSupport : z ∈ c'.support :=
      (Walk.mem_verts_toSubgraph c').1 hver
    rw [Walk.support_map] at hvSupport
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp hvSupport
    change (y : G.Vertex) = z at hval
    rw [← hval]
    exact y.2
  have hsub : K.neighborFinset v ⊆ G.toSimpleGraph.neighborFinset v ∩ U := by
    intro z hz
    simp only [Finset.mem_inter]
    exact ⟨hneigh_subset hz, hneigh_U z hz⟩
  calc
    2 = (K.neighborFinset v).card := hcycleCard.symm
    _ ≤ (G.toSimpleGraph.neighborFinset v ∩ U).card := Finset.card_le_card hsub

theorem exists_cycle (P : PairedPathCertificate G U) :
    ∃ c : (G.toSimpleGraph.induce (U : Set G.Vertex)).Walk
      P.source P.source, c.IsCycle :=
  ⟨P.path₁.append P.path₂.reverse, P.append_isCycle⟩

/-- The paired paths cover the whole induced region, so that region is
connected. -/
theorem induced_connected (P : PairedPathCertificate G U) :
    (G.toSimpleGraph.induce (U : Set G.Vertex)).Connected := by
  let emb := SimpleGraph.Embedding.induce (G := G.toSimpleGraph) (U : Set G.Vertex)
  let p := Walk.map emb.toHom P.path₁
  let q := Walk.map emb.toHom P.path₂
  let S₁ : Set G.Vertex := {w | w ∈ p.support}
  let S₂ : Set G.Vertex := {w | w ∈ q.support}
  have h₁ : (G.toSimpleGraph.induce S₁).Connected := by
    simpa [S₁] using Walk.connected_induce_support p
  have h₂ : (G.toSimpleGraph.induce S₂).Connected := by
    simpa [S₂] using Walk.connected_induce_support q
  have hinter : (S₁ ∩ S₂).Nonempty := by
    refine ⟨P.source.1, ?_⟩
    change emb P.source ∈ p.support ∧ emb P.source ∈ q.support
    constructor
    · rw [Walk.support_map]
      exact List.mem_map.mpr ⟨P.source, by simp, rfl⟩
    · rw [Walk.support_map]
      exact List.mem_map.mpr ⟨P.source, by simp, rfl⟩
  have hUnion : (G.toSimpleGraph.induce (S₁ ∪ S₂)).Connected :=
    SimpleGraph.induce_union_connected h₁ h₂ hinter
  have hcover : (U : Set G.Vertex) = S₁ ∪ S₂ := by
    ext v
    constructor
    · intro hv
      let w : {x : G.Vertex // x ∈ U} := ⟨v, hv⟩
      rcases P.covers_region w with hp | hq
      · left
        change v ∈ p.support
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨w, hp, rfl⟩
      · right
        change v ∈ q.support
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨w, hq, rfl⟩
    · intro hv
      rcases hv with hp | hq
      · change v ∈ p.support at hp
        rw [Walk.support_map] at hp
        obtain ⟨w, hw, hval⟩ := List.mem_map.mp hp
        simpa [emb] using (hval ▸ w.2)
      · change v ∈ q.support at hq
        rw [Walk.support_map] at hq
        obtain ⟨w, hw, hval⟩ := List.mem_map.mp hq
        simpa [emb] using (hval ▸ w.2)
  rw [hcover]
  exact hUnion

/-- Two internally vertex-disjoint simple paths with common distinct
endpoints make the induced physical region cyclic. -/
theorem isCyclicRegion (P : PairedPathCertificate G U) :
    G.IsCyclicRegion U := by
  refine ⟨P.induced_connected, ?_⟩
  intro hacyclic
  obtain ⟨c, hc⟩ := P.exists_cycle
  exact hacyclic c hc

/-- If every region vertex has at least two neighbors inside the region,
then subcubic ambient degree, with degree two away from two endpoints, gives
an actual host cut of size at most two. The internal-neighbor premise is the
local incidence fact supplied by the paired-path construction. -/
theorem actualCut_le_two_of_path_region
    (P : PairedPathCertificate G U)
    (hmax : ∀ v ∈ U, G.degree v ≤ 3)
    (hdegree : ∀ v ∈ U, v ≠ P.source.1 → v ≠ P.target.1 → G.degree v = 2)
    (hinternal : ∀ v ∈ U,
      2 ≤ (G.toSimpleGraph.neighborFinset v ∩ U).card) :
    G.actualCut U ≤ 2 := by
  classical
  have hcount :
      Erdos1016.Proof.PhysicalCutBoundaryCount.externalIncidenceCount G U ≤ 2 := by
    rw [Erdos1016.Proof.PhysicalCutBoundaryCount.externalIncidenceCount]
    calc
      (∑ v ∈ U, (G.toSimpleGraph.neighborFinset v \ U).card) ≤
          (∑ v ∈ U, if v = P.source.1 ∨ v = P.target.1 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        let ns : Finset G.Vertex :=
          @SimpleGraph.neighborFinset G.Vertex G.toSimpleGraph v
            (PhysicalSimpleGraphDegreeBridge.neighborFintype G v)
        have hns : ns = G.toSimpleGraph.neighborFinset v := by
          ext w
          simp [ns, SimpleGraph.mem_neighborFinset]
        by_cases hend : v = P.source.1 ∨ v = P.target.1
        · have hdegree_le : (G.toSimpleGraph.neighborFinset v).card ≤ 3 := by
            have hdegree_le' : G.degree v ≤ 3 := hmax v hv
            have heq : G.degree v = ns.card := by
              simpa [ns] using
                PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v
            rw [heq, hns] at hdegree_le'
            exact hdegree_le'
          have hinter' := hinternal v hv
          have hinter : 2 ≤ (G.toSimpleGraph.neighborFinset v ∩ U).card := by
            change 2 ≤ (ns ∩ U).card at hinter'
            rw [hns] at hinter'
            exact hinter'
          have hsum := Finset.card_inter_add_card_sdiff
            (G.toSimpleGraph.neighborFinset v) U
          have houter :
              (G.toSimpleGraph.neighborFinset v \ U).card ≤ 1 := by
            omega
          simp [hend, houter]
        · have hdeg := hdegree v hv (by
            intro h
            exact hend (Or.inl h)) (by
            intro h
            exact hend (Or.inr h))
          have hdegree_eq : (G.toSimpleGraph.neighborFinset v).card = 2 := by
            have heq : G.degree v = ns.card := by
              simpa [ns] using
                PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v
            rw [heq, hns] at hdeg
            exact hdeg
          have hsum := Finset.card_inter_add_card_sdiff
            (G.toSimpleGraph.neighborFinset v) U
          have houter : (G.toSimpleGraph.neighborFinset v \ U).card = 0 := by
            have hinter' := hinternal v hv
            have hinter : 2 ≤ (G.toSimpleGraph.neighborFinset v ∩ U).card := by
              change 2 ≤ (ns ∩ U).card at hinter'
              rw [hns] at hinter'
              exact hinter'
            omega
          simp [hend, houter]
      _ ≤ 2 := by
        calc
          _ ≤ ∑ v ∈ U,
              ((if v = P.source.1 then 1 else 0) +
                (if v = P.target.1 then 1 else 0)) := by
                apply Finset.sum_le_sum
                intro v hv
                by_cases hs : v = P.source.1 <;> by_cases ht : v = P.target.1 <;>
                  simp [hs, ht] <;> omega
          _ = (∑ v ∈ U, if v = P.source.1 then 1 else 0) +
                (∑ v ∈ U, if v = P.target.1 then 1 else 0) := by
                rw [Finset.sum_add_distrib]
          _ = 1 + 1 := by simp [P.source.2, P.target.2]
          _ = 2 := by omega
  exact le_trans
    (Erdos1016.Proof.PhysicalCutBoundaryCount.actualCut_le_externalIncidenceCount G U)
    hcount

/-- The paired paths themselves supply the internal incidence premise, so a
subcubic physical graph with degree two away from their endpoints has actual
labelled cut at most two. -/
theorem actualCut_le_two_of_paths
    (P : PairedPathCertificate G U)
    (hmax : ∀ v ∈ U, G.degree v ≤ 3)
    (hdegree : ∀ v ∈ U, v ≠ P.source.1 → v ≠ P.target.1 → G.degree v = 2) :
    G.actualCut U ≤ 2 :=
  P.actualCut_le_two_of_path_region hmax hdegree P.internalNeighborCount_ge_two

/-- Physical edges whose two endpoints lie inside a vertex region. -/
def pairedRegionInternalEdges (G : PhysicalGraph) (U : Finset G.Vertex) :
    Finset G.Edge :=
  Finset.univ.filter fun e => G.src e ∈ U ∧ G.dst e ∈ U



end PairedPathCertificate

end Erdos1016.Proof.PairedPathRegions
