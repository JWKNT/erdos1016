import Erdos1016.CycleSpace.Graphical.LinkMap

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalComponentCutParity

open Erdos1016
open Erdos1016.Proof.GraphicalLinkMap

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The physical vertices belonging to a component after deleting `u` and `v`. -/
def componentVertexSet (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) : Finset G.Vertex :=
  Finset.univ.filter fun z =>
    ∃ hz : z ≠ u ∧ z ≠ v,
      (deletedGraph G u v).connectedComponentMk ⟨z, hz⟩ = c

/-- Edges from `a` into one component of the two-vertex deletion. -/
def componentCutAt (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (a : G.Vertex) (e : G.Edge) : Prop :=
  (G.src e = a ∧ G.dst e ∈ componentVertexSet G u v c) ∨
  (G.dst e = a ∧ G.src e ∈ componentVertexSet G u v c)

/-- Parity of a component's attachments at a marked vertex. -/
def componentCutParity (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (a : G.Vertex) (x : G.Word) : F₂ :=
  ∑ e : G.Edge, if componentCutAt G u v c a e then x e else 0

private theorem componentVertexSet_spec (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) {z : G.Vertex}
    (hz : z ∈ componentVertexSet G u v c) :
    ∃ h : z ≠ u ∧ z ≠ v,
      (deletedGraph G u v).connectedComponentMk ⟨z, h⟩ = c := by
  simpa [componentVertexSet] using hz

private theorem physical_edge_adj (G : PhysicalGraph) (e : G.Edge) :
    G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
  change ∃ f, (fun _ : G.Edge => (1 : F₂)) f ≠ 0 ∧
    ((G.src f = G.src e ∧ G.dst f = G.dst e) ∨
      (G.src f = G.dst e ∧ G.dst f = G.src e))
  exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

private theorem component_mem_of_edge_neighbor (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hs : G.src e ∈ componentVertexSet G u v c)
    (hd : G.dst e ≠ u ∧ G.dst e ≠ v) :
    G.dst e ∈ componentVertexSet G u v c := by
  obtain ⟨hs', hcomp⟩ := componentVertexSet_spec G u v c hs
  let a : DeletedVertex G u v := ⟨G.src e, hs'⟩
  let b : DeletedVertex G u v := ⟨G.dst e, hd⟩
  have hadj : (deletedGraph G u v).Adj a b := physical_edge_adj G e
  have hreach := SimpleGraph.Adj.reachable hadj
  have hsame := SimpleGraph.ConnectedComponent.sound hreach
  have hcomp' : (deletedGraph G u v).connectedComponentMk b = c := hsame.symm.trans hcomp
  simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hd, hcomp'⟩

private theorem component_mem_of_reverse_edge_neighbor (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hd : G.dst e ∈ componentVertexSet G u v c)
    (hs : G.src e ≠ u ∧ G.src e ≠ v) :
    G.src e ∈ componentVertexSet G u v c := by
  obtain ⟨hd', hcomp⟩ := componentVertexSet_spec G u v c hd
  let a : DeletedVertex G u v := ⟨G.src e, hs⟩
  let b : DeletedVertex G u v := ⟨G.dst e, hd'⟩
  have hadj : (deletedGraph G u v).Adj b a := G.toSimpleGraph.symm (physical_edge_adj G e)
  have hreach := SimpleGraph.Adj.reachable hadj
  have hsame := SimpleGraph.ConnectedComponent.sound hreach
  have hcomp' : (deletedGraph G u v).connectedComponentMk a = c := hsame.symm.trans hcomp
  simp only [componentVertexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hs, hcomp'⟩

private theorem component_not_marked_left (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) :
    u ∉ componentVertexSet G u v c := by simp [componentVertexSet]

private theorem component_not_marked_right (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) :
    v ∉ componentVertexSet G u v c := by simp [componentVertexSet]

private theorem other_endpoint_is_marked (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hs : G.src e ∈ componentVertexSet G u v c)
    (hd : G.dst e ∉ componentVertexSet G u v c) :
    G.dst e = u ∨ G.dst e = v := by
  by_cases hu : G.dst e = u
  · exact Or.inl hu
  · by_cases hv : G.dst e = v
    · exact Or.inr hv
    · have hmem := component_mem_of_edge_neighbor G u v c e hs ⟨hu, hv⟩
      exact (hd hmem).elim

private theorem source_endpoint_is_marked (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hd : G.dst e ∈ componentVertexSet G u v c)
    (hs : G.src e ∉ componentVertexSet G u v c) :
    G.src e = u ∨ G.src e = v := by
  by_cases hu : G.src e = u
  · exact Or.inl hu
  · by_cases hv : G.src e = v
    · exact Or.inr hv
    · have hmem := component_mem_of_reverse_edge_neighbor G u v c e hd ⟨hu, hv⟩
      exact (hs hmem).elim

private theorem boundary_sum_eq_cut (G : PhysicalGraph) (x : G.Word)
    (S : Finset G.Vertex) :
    (∑ z ∈ S, G.boundary x z) =
      ∑ e : G.Edge,
        ((if G.src e ∈ S then x e else 0) + (if G.dst e ∈ S then x e else 0)) := by
  classical
  calc
    (∑ z ∈ S, G.boundary x z) =
        ∑ z ∈ S, ∑ e : G.Edge,
          ((if G.src e = z then x e else 0) + (if G.dst e = z then x e else 0)) := rfl
    _ = ∑ e : G.Edge, ∑ z ∈ S,
          ((if G.src e = z then x e else 0) + (if G.dst e = z then x e else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ e : G.Edge,
          ((if G.src e ∈ S then x e else 0) + (if G.dst e ∈ S then x e else 0)) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]

/-- Summing the cycle-boundary equations over one deleted component leaves
only its attachment parities at `u` and `v`. -/
theorem component_boundary_cut_decomposition (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (c : (deletedGraph G u v).ConnectedComponent) (x : G.Word) :
    (∑ z ∈ componentVertexSet G u v c, G.boundary x z) =
      componentCutParity G u v c u x + componentCutParity G u v c v x := by
  classical
  rw [boundary_sum_eq_cut]
  simp only [componentCutParity]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e ∈ componentVertexSet G u v c
  · by_cases hd : G.dst e ∈ componentVertexSet G u v c
    · have hsu := component_not_marked_left G u v c
      have hsv := component_not_marked_right G u v c
      have hsu' : G.src e ≠ u := by intro h; exact hsu (h ▸ hs)
      have hsv' : G.src e ≠ v := by intro h; exact hsv (h ▸ hs)
      have hdu : G.dst e ≠ u := by intro h; exact hsu (h ▸ hd)
      have hdv : G.dst e ≠ v := by intro h; exact hsv (h ▸ hd)
      simp [componentCutAt, hs, hd, hsu', hsv', hdu, hdv, componentCutParity,
        ZModModule.add_self]
    · rcases other_endpoint_is_marked G u v c e hs hd with hu | hv
      · simp [componentCutAt, hs, hd, hu, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
      · simp [componentCutAt, hs, hd, hv, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
  · by_cases hd : G.dst e ∈ componentVertexSet G u v c
    · rcases source_endpoint_is_marked G u v c e hd hs with hu | hv
      · simp [componentCutAt, hs, hd, hu, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
      · simp [componentCutAt, hs, hd, hv, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
    · simp [componentCutAt, hs, hd]

/-- A component is attached to `a` if a physical edge joins `a` to it in
 the two-vertex-deleted graph. -/
def componentAttachedAt (G : PhysicalGraph) (u v a : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) : Prop :=
  ∃ e : G.Edge, ∃ x : DeletedVertex G u v,
    (G.src e = a ∧ G.dst e = x.1 ∨ G.dst e = a ∧ G.src e = x.1) ∧
      (deletedGraph G u v).connectedComponentMk x = c

/-- If a component has no attachment at a marked vertex, its cut parity there
is zero. -/
theorem componentCutParity_zero_of_no_attachment (G : PhysicalGraph)
    (u v a : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent) (x : G.Word)
    (hno : ¬ componentAttachedAt G u v a c) :
    componentCutParity G u v c a x = 0 := by
  classical
  unfold componentCutParity
  apply Finset.sum_eq_zero
  intro e he
  by_cases hcut : componentCutAt G u v c a e
  · have hattach : componentAttachedAt G u v a c := by
      rcases hcut with ⟨ha, hx⟩ | ⟨ha, hx⟩
      · obtain ⟨hz, hcomp⟩ := componentVertexSet_spec G u v c hx
        exact ⟨e, ⟨G.dst e, hz⟩, Or.inl ⟨ha, rfl⟩, hcomp⟩
      · obtain ⟨hz, hcomp⟩ := componentVertexSet_spec G u v c hx
        exact ⟨e, ⟨G.src e, hz⟩, Or.inr ⟨ha, rfl⟩, hcomp⟩
    exact (hno hattach).elim
  · simp [hcut]

private theorem double_zero (a : F₂) : a + a = 0 := ZModModule.add_self a

/-- Every cycle crosses the `u` and `v` sides of a deleted component with the
same parity. -/
theorem componentCutParity_eq_on_cycle (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (c : (deletedGraph G u v).ConnectedComponent) (x : G.CycleSpace) :
    componentCutParity G u v c u x.1 = componentCutParity G u v c v x.1 := by
  have hboundary : (∑ z ∈ componentVertexSet G u v c, G.boundary x.1 z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    have hx : G.boundary x.1 = 0 := x.2
    exact congrArg (fun d : G.Demand => d z) hx
  rw [component_boundary_cut_decomposition G u v hne c x.1] at hboundary
  have hsum : componentCutParity G u v c u x.1 +
      componentCutParity G u v c v x.1 = 0 := hboundary
  have h := congrArg (fun z : F₂ => z + componentCutParity G u v c v x.1) hsum
  simpa [double_zero, add_assoc] using h

/-- A component attached to `u` but not `v` contributes zero at `u` on cycles. -/
theorem componentCutParity_zero_of_no_v_attachment (G : PhysicalGraph)
    (u v : G.Vertex) (hne : u ≠ v) (c : (deletedGraph G u v).ConnectedComponent)
    (x : G.CycleSpace) (hno : ¬ componentAttachedAt G u v v c) :
    componentCutParity G u v c u x.1 = 0 := by
  rw [componentCutParity_eq_on_cycle G u v hne c x]
  exact componentCutParity_zero_of_no_attachment G u v v c x.1 hno

end Erdos1016.Proof.GraphicalComponentCutParity
