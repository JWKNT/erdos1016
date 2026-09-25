import Erdos1016.CycleSpace.Graphical.VertexStarSpaces
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.GraphicalLinkMap

open Erdos1016
open Erdos1016.Proof.GraphicalCommonInformation

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev DeletedVertex (G : PhysicalGraph) (u v : G.Vertex) :=
  {z : G.Vertex // z ≠ u ∧ z ≠ v}

/-- The induced graph after deleting two marked vertices. -/
def deletedGraph (G : PhysicalGraph) (u v : G.Vertex) :
    SimpleGraph (DeletedVertex G u v) where
  Adj x y := G.toSimpleGraph.Adj x.1 y.1
  symm := fun x y h => G.toSimpleGraph.symm h
  loopless := fun x h => G.toSimpleGraph.loopless x h

/-- A direct physical edge between the two marked vertices. -/
def DirectLink (G : PhysicalGraph) (u v : G.Vertex) :=
  {e : G.Edge // (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)}

private def attached (G : PhysicalGraph) (u v : G.Vertex)
    (marked : G.Vertex) (c : (deletedGraph G u v).ConnectedComponent) : Prop :=
  ∃ e : G.Edge, ∃ x : DeletedVertex G u v,
    (G.src e = marked ∧ G.dst e = x.1 ∨ G.dst e = marked ∧ G.src e = x.1) ∧
      (deletedGraph G u v).connectedComponentMk x = c

/-- A component of the two-vertex deletion attached to both marked vertices. -/
def ComponentLink (G : PhysicalGraph) (u v : G.Vertex) :=
  {c : (deletedGraph G u v).ConnectedComponent //
    attached G u v u c ∧ attached G u v v c}

/-- The finite set of direct and component links for a pair of vertices. -/
def LinkIndex (G : PhysicalGraph) (u v : G.Vertex) :=
  Sum (DirectLink G u v) (ComponentLink G u v)

noncomputable instance (G : PhysicalGraph) (u v : G.Vertex) :
    Fintype ((deletedGraph G u v).ConnectedComponent) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance (G : PhysicalGraph) (u v : G.Vertex) :
    Fintype (ComponentLink G u v) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun c => attached G u v u c ∧ attached G u v v c)
    (by intro c; simp)

noncomputable instance (G : PhysicalGraph) (u v : G.Vertex) :
    Fintype (DirectLink G u v) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun e =>
      (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u))
    (by intro e; simp)

noncomputable instance (G : PhysicalGraph) (u v : G.Vertex) :
    Fintype (LinkIndex G u v) := by
  change Fintype (DirectLink G u v ⊕ ComponentLink G u v)
  exact instFintypeSum _ _

def componentVertices (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun z =>
    ∃ hz : z ≠ u ∧ z ≠ v,
      (deletedGraph G u v).connectedComponentMk ⟨z, hz⟩ = c

private def componentCutAt (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (a : G.Vertex) (e : G.Edge) : Prop :=
  (G.src e = a ∧ G.dst e ∈ componentVertices G u v c) ∨
  (G.dst e = a ∧ G.src e ∈ componentVertices G u v c)

def componentCutCondition (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge) : Prop :=
  componentCutAt G u v c u e

theorem componentVertices_spec (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) {z : G.Vertex}
    (hz : z ∈ componentVertices G u v c) :
    ∃ h : z ≠ u ∧ z ≠ v,
      (deletedGraph G u v).connectedComponentMk ⟨z, h⟩ = c := by
  simpa [componentVertices] using hz

private theorem physical_edge_adj (G : PhysicalGraph) (e : G.Edge) :
    G.toSimpleGraph.Adj (G.src e) (G.dst e) := by
  change ∃ f, (fun _ : G.Edge => (1 : F₂)) f ≠ 0 ∧
    ((G.src f = G.src e ∧ G.dst f = G.dst e) ∨
      (G.src f = G.dst e ∧ G.dst f = G.src e))
  exact ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩

private theorem component_closed_under_deleted_adj (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (x y : DeletedVertex G u v)
    (hx : (deletedGraph G u v).connectedComponentMk x = c)
    (hxy : (deletedGraph G u v).Adj x y) :
    (deletedGraph G u v).connectedComponentMk y = c := by
  have hxy' := SimpleGraph.Adj.reachable hxy
  have heq := SimpleGraph.ConnectedComponent.sound hxy'
  exact heq.symm.trans hx

private theorem component_mem_of_edge_neighbor (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hs : G.src e ∈ componentVertices G u v c)
    (hd : G.dst e ≠ u ∧ G.dst e ≠ v) :
    G.dst e ∈ componentVertices G u v c := by
  obtain ⟨hs', hcomp⟩ := componentVertices_spec G u v c hs
  let a : DeletedVertex G u v := ⟨G.src e, hs'⟩
  let b : DeletedVertex G u v := ⟨G.dst e, hd⟩
  have hadj : (deletedGraph G u v).Adj a b := physical_edge_adj G e
  have hsame := component_closed_under_deleted_adj G u v c a b hcomp hadj
  simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hd, hsame⟩

private theorem component_mem_of_reverse_edge_neighbor (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hd : G.dst e ∈ componentVertices G u v c)
    (hs : G.src e ≠ u ∧ G.src e ≠ v) :
    G.src e ∈ componentVertices G u v c := by
  obtain ⟨hd', hcomp⟩ := componentVertices_spec G u v c hd
  let a : DeletedVertex G u v := ⟨G.src e, hs⟩
  let b : DeletedVertex G u v := ⟨G.dst e, hd'⟩
  have hadj : (deletedGraph G u v).Adj b a :=
    G.toSimpleGraph.symm (physical_edge_adj G e)
  have hsame := component_closed_under_deleted_adj G u v c b a hcomp hadj
  simp only [componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hs, hsame⟩

private theorem component_not_marked_left (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) :
    u ∉ componentVertices G u v c := by
  simp [componentVertices]

private theorem component_not_marked_right (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) :
    v ∉ componentVertices G u v c := by
  simp [componentVertices]

private theorem other_endpoint_is_marked (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hs : G.src e ∈ componentVertices G u v c)
    (hd : G.dst e ∉ componentVertices G u v c) :
    G.dst e = u ∨ G.dst e = v := by
  by_cases hu : G.dst e = u
  · exact Or.inl hu
  · by_cases hv : G.dst e = v
    · exact Or.inr hv
    · have hmem := component_mem_of_edge_neighbor G u v c e hs ⟨hu, hv⟩
      exact (hd hmem).elim

private theorem source_endpoint_is_marked (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (hd : G.dst e ∈ componentVertices G u v c)
    (hs : G.src e ∉ componentVertices G u v c) :
    G.src e = u ∨ G.src e = v := by
  by_cases hu : G.src e = u
  · exact Or.inl hu
  · by_cases hv : G.src e = v
    · exact Or.inr hv
    · have hmem := component_mem_of_reverse_edge_neighbor G u v c e hd ⟨hu, hv⟩
      exact (hs hmem).elim

private theorem f2_double_zero (a : F₂) : a + a = 0 := ZModModule.add_self a

/-- The boundary cut of a deleted component consists precisely of its
attachments to the two marked vertices. -/
private theorem component_cut_decomposition (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (c : (deletedGraph G u v).ConnectedComponent) (x : G.Word) :
    (∑ e : G.Edge,
      ((if G.src e ∈ componentVertices G u v c then x e else 0) +
       (if G.dst e ∈ componentVertices G u v c then x e else 0))) =
    (∑ e : G.Edge, if componentCutAt G u v c u e then x e else 0) +
      (∑ e : G.Edge, if componentCutAt G u v c v e then x e else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : G.src e ∈ componentVertices G u v c
  · by_cases hd : G.dst e ∈ componentVertices G u v c
    · have hsu := component_not_marked_left G u v c
      have hsv := component_not_marked_right G u v c
      have hsu' : G.src e ≠ u := by intro h; exact hsu (h ▸ hs)
      have hsv' : G.src e ≠ v := by intro h; exact hsv (h ▸ hs)
      have hdu : G.dst e ≠ u := by intro h; exact hsu (h ▸ hd)
      have hdv : G.dst e ≠ v := by intro h; exact hsv (h ▸ hd)
      simp [componentCutAt, hs, hd, hsu', hsv', hdu, hdv, f2_double_zero]
    · rcases other_endpoint_is_marked G u v c e hs hd with hu | hv
      · simp [componentCutAt, hs, hd, hu, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
      · simp [componentCutAt, hs, hd, hv, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
  · by_cases hd : G.dst e ∈ componentVertices G u v c
    · rcases source_endpoint_is_marked G u v c e hd hs with hu | hv
      · simp [componentCutAt, hs, hd, hu, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
      · simp [componentCutAt, hs, hd, hv, component_not_marked_left,
          component_not_marked_right, hne, hne.symm]
    · simp [componentCutAt, hs, hd]

/-- Summing the cycle-boundary equations over a finite vertex set counts
exactly the selected edges crossing its cut, with one contribution per side. -/
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

/-- Link bit: a direct-edge bit, or the parity of edges from `u` into a
component link. -/
def linkCoordinate (G : PhysicalGraph) (u v : G.Vertex) (x : G.CycleSpace)
    (i : LinkIndex G u v) : F₂ := by
  classical
  cases i with
  | inl e => exact x.1 e.1
  | inr c => exact ∑ e : G.Edge,
      if componentCutCondition G u v c.1 e then x.1 e else 0

/-- The link-bit observation map from the physical cycle space. -/
def linkMap (G : PhysicalGraph) (u v : G.Vertex) :
    G.CycleSpace →ₗ[F₂] (LinkIndex G u v → F₂) where
  toFun x i := linkCoordinate G u v x i
  map_add' x y := by
    classical
    funext i
    cases i with
    | inl e => rfl
    | inr c =>
        change linkCoordinate G u v (x + y) (Sum.inr c) =
          linkCoordinate G u v x (Sum.inr c) + linkCoordinate G u v y (Sum.inr c)
        simp only [linkCoordinate]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : componentCutCondition G u v c.1 e <;> simp [h]
  map_smul' a x := by
    classical
    funext i
    cases i with
    | inl e => rfl
    | inr c =>
        change (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then a * x.1 e else 0) =
          a * (∑ e : G.Edge,
            if componentCutCondition G u v c.1 e then x.1 e else 0)
        calc
          (∑ e : G.Edge,
              if componentCutCondition G u v c.1 e then a * x.1 e else 0) =
              ∑ e : G.Edge, a * (if componentCutCondition G u v c.1 e then x.1 e else 0) := by
                apply Finset.sum_congr rfl
                intro e he
                by_cases h : componentCutCondition G u v c.1 e <;> simp [h]
          _ = _ := by rw [Finset.mul_sum]

@[simp] theorem linkMap_apply (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) (i : LinkIndex G u v) :
    linkMap G u v x i = linkCoordinate G u v x i := rfl

private theorem componentCut_incident (G : PhysicalGraph) (u v : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (h : componentCutCondition G u v c e) : G.incident e u := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem componentCutAt_incident (G : PhysicalGraph) (u v a : G.Vertex)
    (c : (deletedGraph G u v).ConnectedComponent) (e : G.Edge)
    (h : componentCutAt G u v c a e) : G.incident e a := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Any cycle word avoiding `u` has zero bit on every link coordinate.
Every link coordinate is supported on edges incident to `u`. -/
theorem linkMap_eq_zero_of_avoiding_first (G : PhysicalGraph) (u v : G.Vertex)
    (x : G.CycleSpace) (hx : x ∈ cyclesAvoidingVertex G u) :
    linkMap G u v x = 0 := by
  classical
  have hrestriction : vertexStarRestriction G u x = 0 := by
    simpa [cyclesAvoidingVertex] using hx
  have hcoord (e : G.Edge) (he : G.incident e u) : x.1 e = 0 := by
    have h := congrArg (fun f : VertexStarEdges G u → F₂ => f ⟨e, he⟩) hrestriction
    simpa [vertexStarRestriction] using h
  ext i
  cases i with
  | inl e => exact hcoord e.1 (by
      rcases e.2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2)
  | inr c =>
      simp only [linkMap_apply, linkCoordinate]
      apply Finset.sum_eq_zero
      intro e he
      by_cases hc : componentCutCondition G u v c.1 e
      · simp [hc, hcoord e (componentCut_incident G u v c.1 e hc)]
      · simp [hc]

/-- A cycle avoiding the second marked vertex has even attachment parity on
every first-side component link. The parity is the boundary sum over the
deleted component; internal edges cancel and there are no exits except at
the two marked vertices. -/
theorem linkMap_eq_zero_of_avoiding_second (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) (x : G.CycleSpace) (hx : x ∈ cyclesAvoidingVertex G v) :
    linkMap G u v x = 0 := by
  classical
  have hrestriction : vertexStarRestriction G v x = 0 := by
    simpa [cyclesAvoidingVertex] using hx
  have hcoord (e : G.Edge) (he : G.incident e v) : x.1 e = 0 := by
    have h := congrArg (fun f : VertexStarEdges G v → F₂ => f ⟨e, he⟩) hrestriction
    simpa [vertexStarRestriction] using h
  ext i
  cases i with
  | inl e =>
      exact hcoord e.1 (by
        rcases e.2 with h | h
        · exact Or.inr h.2
        · exact Or.inl h.1)
  | inr c =>
      let S := componentVertices G u v c.1
      have hboundary : (∑ z ∈ S, G.boundary x.1 z) = 0 := by
        apply Finset.sum_eq_zero
        intro z hz
        have hzero : G.boundary x.1 = 0 := x.2
        exact congrArg (fun d : G.Demand => d z) hzero
      rw [boundary_sum_eq_cut] at hboundary
      rw [component_cut_decomposition G u v hne c.1 x.1] at hboundary
      have hvsum :
          (∑ e : G.Edge, if componentCutAt G u v c.1 v e then x.1 e else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        by_cases hc : componentCutAt G u v c.1 v e
        · simp [hc, hcoord e (componentCutAt_incident G u v v c.1 e hc)]
        · simp [hc]
      have husum :
          (∑ e : G.Edge, if componentCutAt G u v c.1 u e then x.1 e else 0) = 0 := by
        simpa [hvsum] using hboundary
      simpa [linkCoordinate, componentCutCondition] using husum

/-- The sum of the two vertex-avoiding cycle spaces lies in the kernel of the
two-vertex link observation. -/
theorem avoiding_first_le_linkMap_ker (G : PhysicalGraph) (u v : G.Vertex) :
    cyclesAvoidingVertex G u ≤ LinearMap.ker (linkMap G u v) := by
  intro x hx
  change linkMap G u v x = 0
  exact linkMap_eq_zero_of_avoiding_first G u v x hx

/-- The sum of the two vertex-avoiding cycle spaces lies in the kernel of the
two-vertex link observation. -/
theorem avoiding_sum_le_linkMap_ker (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) :
    cyclesAvoidingVertex G u ⊔ cyclesAvoidingVertex G v ≤
      LinearMap.ker (linkMap G u v) := by
  refine sup_le ?_ ?_
  · exact avoiding_first_le_linkMap_ker G u v
  · intro x hx
    change linkMap G u v x = 0
    exact linkMap_eq_zero_of_avoiding_second G u v hne x hx

end Erdos1016.Proof.GraphicalLinkMap
