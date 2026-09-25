import Erdos1016.Graph.PhysicalDegree
import Erdos1016.Cleanup.Corridors.DegreeTwoComponentCut
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace Erdos1016.Proof.UnprotectedDegreeTwoAcyclicity

open Erdos1016
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem cycles_neighborFinset_card_two (K : SimpleGraph V)
    [DecidableRel K.Adj] (hK : K.IsCycles) (v : V)
    (hne : (K.neighborSet v).Nonempty) : (K.neighborFinset v).card = 2 := by
  have hc := hK hne
  rw [Set.ncard_eq_toFinset_card] at hc
  simpa [SimpleGraph.neighborFinset] using hc


/-- The induced graph on the unprotected degree-two vertices is acyclic.
Consequently each of its connected components is a finite tree/path. -/
theorem induced_unprotected_isAcyclic
    (G : PhysicalGraph) (P : Finset G.Vertex)
    (hconn : G.toSimpleGraph.Connected) (hP : P.Nonempty)
    (hdeg : ∀ v, v ∉ P → G.degree v = 2) :
    (G.toSimpleGraph.induce {v | v ∉ P}).IsAcyclic := by
  classical
  let U : Set G.Vertex := {v | v ∉ P}
  let D : SimpleGraph U := G.toSimpleGraph.induce U
  change D.IsAcyclic
  intro u p hp
  let f : D ↪g G.toSimpleGraph := @SimpleGraph.Embedding.induce G.Vertex G.toSimpleGraph U
  let c := p.map f.toHom
  have hc : c.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective f.injective).2 hp
  let C : Finset G.Vertex := c.support.toFinset
  have hC : C.Nonempty := ⟨f.toHom u, by
    exact List.mem_toFinset.mpr c.start_mem_support⟩
  have hCsub : ∀ v ∈ C, v ∉ P := by
    intro v hv
    have hv' : v ∈ c.support := List.mem_toFinset.mp hv
    rw [SimpleGraph.Walk.support_map] at hv'
    rcases List.mem_map.mp hv' with ⟨x, hx, rfl⟩
    exact x.2
  have hdisj : Disjoint C P := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvP
    exact hCsub v hvC hvP
  let K : SimpleGraph G.Vertex := c.toSubgraph.spanningCoe
  have hKcycles : K.IsCycles := SimpleGraph.Walk.IsCycle.isCycles_spanningCoe_toSubgraph hc
  have hverts (v : G.Vertex) (hv : v ∈ C) : v ∈ c.toSubgraph.verts := by
    apply (SimpleGraph.Walk.mem_verts_toSubgraph c).2
    exact List.mem_toFinset.mp hv
  have hcycleCard (v : G.Vertex) (hv : v ∈ C) :
      (K.neighborFinset v).card = 2 := by
    apply cycles_neighborFinset_card_two K hKcycles v
    have hnc := hc.ncard_neighborSet_toSubgraph_eq_two (List.mem_toFinset.mp hv)
    by_contra hn
    have he : c.toSubgraph.neighborSet v = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, Set.ncard_empty] at hnc
    omega
  have hAmbientCard (v : G.Vertex) (hv : v ∈ C) :
      (G.toSimpleGraph.neighborFinset v).card = 2 := by
    calc
      _ = G.degree v := (Erdos1016.Proof.PhysicalSimpleGraphDegreeBridge.degree_eq_neighborFinset_card G v).symm
      _ = 2 := hdeg v (hCsub v hv)
  have hneigh_subset (v : G.Vertex) (hv : v ∈ C) :
      K.neighborFinset v ⊆ G.toSimpleGraph.neighborFinset v := by
    intro w hw
    apply (SimpleGraph.mem_neighborFinset G.toSimpleGraph v _).mpr
    have hadjK : K.Adj v w := (SimpleGraph.mem_neighborFinset K v _).mp hw
    exact c.toSubgraph.adj_sub (by simpa [K, SimpleGraph.Subgraph.spanningCoe_adj] using hadjK)
  have hneigh_eq (v : G.Vertex) (hv : v ∈ C) :
      K.neighborFinset v = G.toSimpleGraph.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le (hneigh_subset v hv)
    rw [hcycleCard v hv, hAmbientCard v hv]
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Erdos1016.Proof.DegreeTwoComponentCut.exists_boundary_adjacency_of_connected
      G.toSimpleGraph hconn C P hC hP hdisj
  have hba : b ∈ G.toSimpleGraph.neighborFinset a :=
    (SimpleGraph.mem_neighborFinset G.toSimpleGraph a b).mpr hab
  rw [← hneigh_eq a ha] at hba
  have hadjK : K.Adj a b := (SimpleGraph.mem_neighborFinset K a b).mp hba
  have hbC : b ∈ C := by
    have hraw : c.toSubgraph.Adj a b := by
      simpa [K, SimpleGraph.Subgraph.spanningCoe_adj] using hadjK
    have hvert := c.toSubgraph.edge_vert (v := b) (w := a) (c.toSubgraph.symm hraw)
    exact List.mem_toFinset.mpr ((SimpleGraph.Walk.mem_verts_toSubgraph c).1 hvert)
  exact hb hbC

end Erdos1016.Proof.UnprotectedDegreeTwoAcyclicity
