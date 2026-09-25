import Erdos1016.Cycles.Geometry.ShortJoiningPaths

set_option autoImplicit false

/-! At a cycle vertex of ambient degree at most three there is at most one
 neighbor outside that cycle. Thus distinct exterior components attach at
 distinct cycle vertices. -/
noncomputable section
namespace Erdos1016.Proof.ShortJoiningPaths
open SimpleGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The two actual cycle edges leave room for at most one exterior edge. -/
theorem cycle_external_neighbor_unique {r v a b : V}
    (C : G.Walk r r) (hC : C.IsCycle) (hv : v ∈ C.support)
    (hdegree : G.degree v ≤ 3) (ha : G.Adj v a) (hb : G.Adj v b)
    (haout : a ∉ C.support) (hbout : b ∉ C.support) : a = b := by
  classical
  have hcyclecard := hC.ncard_neighborSet_toSubgraph_eq_two hv
  have hsub : (C.toSubgraph.neighborSet v).toFinset ⊆
      G.neighborFinset v ∩ C.support.toFinset := by
    intro x hx
    have hadj : C.toSubgraph.Adj v x := by simpa only [Set.mem_toFinset] using hx
    exact Finset.mem_inter.mpr ⟨(by simpa only [SimpleGraph.mem_neighborFinset] using C.toSubgraph.adj_sub hadj),
      List.mem_toFinset.mpr (C.mem_verts_toSubgraph.mp (C.toSubgraph.edge_vert hadj.symm))⟩
  have htwo : 2 ≤ (G.neighborFinset v ∩ C.support.toFinset).card := by
    have hc := Finset.card_le_card hsub
    simpa only [← Set.ncard_eq_toFinset_card', hcyclecard] using hc
  have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset v) C.support.toFinset
  rw [G.card_neighborFinset_eq_degree] at hsplit
  have hcut : (G.neighborFinset v \ C.support.toFinset).card ≤ 1 := by omega
  have hma : a ∈ G.neighborFinset v \ C.support.toFinset := by simp [ha, haout]
  have hmb : b ∈ G.neighborFinset v \ C.support.toFinset := by simp [hb, hbout]
  exact Finset.card_le_one.mp hcut a hma b hmb

/-- Any selection of one attachment from each of disjoint exterior regions
 has distinct cycle endpoints. The region choices need not be canonical. -/
theorem region_attachment_starts_injective {I : Type*} {r : V}
    (C : G.Walk r r) (hC : C.IsCycle)
    (hdegree : ∀ v ∈ C.support, G.degree v ≤ 3)
    (F : I → Finset V) (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (houtside : ∀ i x, x ∈ F i → x ∉ C.support)
    (start next : I → V) (hstart : ∀ i, start i ∈ C.support)
    (hnext : ∀ i, next i ∈ F i) (hadj : ∀ i, G.Adj (start i) (next i)) :
    Function.Injective start := by
  intro i j heq
  have hnext_eq : next i = next j := cycle_external_neighbor_unique C hC (hstart i)
    (hdegree _ (hstart i)) (hadj i) (by simpa only [heq] using hadj j)
    (houtside i _ (hnext i)) (houtside j _ (hnext j))
  by_contra hne
  exact Finset.disjoint_left.mp (hdisjoint hne) (hnext i) (hnext_eq ▸ hnext j)

end Erdos1016.Proof.ShortJoiningPaths
