import Erdos1016.Graph.Multigraph.Components

set_option autoImplicit false

/-!
# Componentwise parity of multigraph boundaries

This file develops the necessary half of the image characterization for the
binary incidence boundary: every boundary has even total on each connected
component.  The statement is valid with loops and parallel labelled edges.
-/

namespace Erdos1016
namespace FiniteMultiGraph

noncomputable section

/-- The vertices belonging to a given connected component. -/
abbrev ComponentVertex (G : FiniteMultiGraph) (c : G.ConnectedComponent) :=
  {v : G.Vertex // G.componentOf v = c}

noncomputable instance componentVertexFintype (G : FiniteMultiGraph)
    (c : G.ConnectedComponent) : Fintype (G.ComponentVertex c) :=
  Fintype.ofFinite _

/-- Total binary demand on one connected component. -/
noncomputable def componentDemandSum (G : FiniteMultiGraph) (y : G.Demand)
    (c : G.ConnectedComponent) : F₂ := by
  classical
  exact ∑ v : G.ComponentVertex c, y v.1

/-- A demand is componentwise even when each connected component has total
zero in `F₂`. -/
def ComponentEven (G : FiniteMultiGraph) (y : G.Demand) : Prop :=
  ∀ c, G.componentDemandSum y c = 0

private theorem endpoint_component_sum (G : FiniteMultiGraph) (x : G.EdgeWord)
    (c : G.ConnectedComponent) (e : G.Edge) (source : Bool)
    [Decidable (G.componentOf (if source then G.src e else G.dst e) = c)] :
    (∑ v : G.ComponentVertex c,
      if (if source then G.src e else G.dst e) = v.1 then x e else 0) =
      (if G.componentOf (if source then G.src e else G.dst e) = c then x e else 0) := by
  classical
  by_cases h : G.componentOf (if source then G.src e else G.dst e) = c
  · let a : G.ComponentVertex c := ⟨(if source then G.src e else G.dst e), h⟩
    have hiff (v : G.ComponentVertex c) :
        ((if source then G.src e else G.dst e) = v.1) ↔ a = v := by
      constructor
      · intro hv
        apply Subtype.ext
        exact hv
      · intro hv
        exact congrArg Subtype.val hv
    simp_rw [hiff]
    simp [h]
  · simp [h]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : (if source then G.src e else G.dst e) ≠ v.1 := by
      intro heq
      apply h
      rw [heq]
      exact v.2
    simp [hne]

theorem boundary_componentDemandSum (G : FiniteMultiGraph) (x : G.EdgeWord)
    (c : G.ConnectedComponent) :
    G.componentDemandSum (G.boundary x) c = 0 := by
  classical
  change (∑ v : G.ComponentVertex c,
    ∑ e : G.Edge, ((if G.src e = v.1 then x e else 0) +
      (if G.dst e = v.1 then x e else 0))) = 0
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib]
  have hs (e : G.Edge) :
      (∑ v : G.ComponentVertex c,
        if G.src e = v.1 then x e else 0) =
      (if G.componentOf (G.src e) = c then x e else 0) := by
    simpa using endpoint_component_sum G x c e true
  have ht (e : G.Edge) :
      (∑ v : G.ComponentVertex c,
        if G.dst e = v.1 then x e else 0) =
      (if G.componentOf (G.dst e) = c then x e else 0) := by
    simpa using endpoint_component_sum G x c e false
  simp_rw [hs, ht]
  have hcomp (e : G.Edge) : G.componentOf (G.dst e) = G.componentOf (G.src e) :=
    (G.componentOf_src_eq_dst e).symm
  simp_rw [hcomp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e he
  by_cases h : G.componentOf (G.src e) = c
  · simp [h]
    have htwo : (2 : F₂) = 0 := by decide
    calc
      x e + x e = (2 : F₂) * x e := by ring
      _ = 0 := by rw [htwo]; simp
  · simp [h]



/-- The unit demand at a vertex. -/
def vertexUnit (G : FiniteMultiGraph) (v : G.Vertex) : G.Demand :=
  Pi.single v 1

/-- Select one labelled edge witnessing a simple adjacency in the underlying
graph. -/
noncomputable def edgeForAdj (G : FiniteMultiGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) : G.Edge := Classical.choose h.2

theorem edgeForAdj_endpoints (G : FiniteMultiGraph) {u v : G.Vertex}
    (h : G.toSimpleGraph.Adj u v) :
    (G.src (G.edgeForAdj h) = u ∧ G.dst (G.edgeForAdj h) = v) ∨
    (G.src (G.edgeForAdj h) = v ∧ G.dst (G.edgeForAdj h) = u) :=
  Classical.choose_spec h.2

theorem boundary_singleEdge (G : FiniteMultiGraph) (e : G.Edge) :
    G.boundary (Pi.single e 1) =
      G.vertexUnit (G.src e) + G.vertexUnit (G.dst e) := by
  classical
  ext v
  change (∑ f : G.Edge,
      ((if G.src f = v then (Pi.single e 1) f else 0) +
       (if G.dst f = v then (Pi.single e 1) f else 0))) = _
  simp only [Pi.single_apply]
  rw [Finset.sum_add_distrib]
  change (∑ f : G.Edge,
      if G.src f = v then if f = e then 1 else 0 else 0) +
    (∑ f : G.Edge, if G.dst f = v then if f = e then 1 else 0 else 0) = _
  rw [Finset.sum_eq_single e, Finset.sum_eq_single e]
  · simp [vertexUnit, Pi.single_apply, eq_comm]
  · intro f hf hfe
    simp [hfe]
  · simp
  · intro f hf hfe
    simp [hfe]
  · simp

theorem vertexUnit_add_self (G : FiniteMultiGraph) (v : G.Vertex) :
    G.vertexUnit v + G.vertexUnit v = 0 := by
  ext z
  by_cases h : z = v
  · subst z
    change G.vertexUnit v v + G.vertexUnit v v = (0 : F₂)
    simp only [vertexUnit, Pi.single_apply, if_true]
    have htwo : (1 : F₂) + 1 = 0 := by decide
    exact htwo
  · simp [vertexUnit, Pi.single_apply, h]

/-- A walk in the underlying graph gives an edge word whose boundary is the
sum of the unit demands at its endpoints. -/
noncomputable def walkWord (G : FiniteMultiGraph) {u v : G.Vertex} :
    G.toSimpleGraph.Walk u v → G.EdgeWord
  | .nil => 0
  | .cons h p => Pi.single (G.edgeForAdj h) 1 + G.walkWord p

theorem boundary_walkWord (G : FiniteMultiGraph) {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    G.boundary (G.walkWord p) = G.vertexUnit u + G.vertexUnit v := by
  induction p with
  | nil =>
      simp only [walkWord, LinearMap.map_zero]
      change 0 = G.vertexUnit _ + G.vertexUnit _
      exact (G.vertexUnit_add_self _).symm
  | @cons a b c h p ih =>
      rw [walkWord, G.boundary.map_add, G.boundary_singleEdge, ih]
      rcases G.edgeForAdj_endpoints h with hh | hh
      · rw [hh.1, hh.2]
        calc
          G.vertexUnit a + G.vertexUnit b + (G.vertexUnit b + G.vertexUnit c) =
              G.vertexUnit a + (G.vertexUnit b + G.vertexUnit b) + G.vertexUnit c := by abel
          _ = G.vertexUnit a + G.vertexUnit c := by rw [G.vertexUnit_add_self b]; simp
      · rw [hh.1, hh.2]
        calc
          G.vertexUnit b + G.vertexUnit a + (G.vertexUnit b + G.vertexUnit c) =
              G.vertexUnit a + (G.vertexUnit b + G.vertexUnit b) + G.vertexUnit c := by abel
          _ = G.vertexUnit a + G.vertexUnit c := by rw [G.vertexUnit_add_self b]; simp

/-- The sum of the two endpoint unit demands lies in the boundary image
whenever the endpoints are in the same component. -/
theorem boundary_pair_mem_range_of_component_eq (G : FiniteMultiGraph)
    (u v : G.Vertex) (h : G.componentOf u = G.componentOf v) :
    G.vertexUnit u + G.vertexUnit v ∈ LinearMap.range G.boundary := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact h
  refine ⟨G.walkWord p, ?_⟩
  exact G.boundary_walkWord p

/-- A chosen representative vertex for each connected component. -/
def componentRoot (G : FiniteMultiGraph) (c : G.ConnectedComponent) : G.Vertex := c.out

@[simp] theorem componentOf_root (G : FiniteMultiGraph) (c : G.ConnectedComponent) :
    G.componentOf (G.componentRoot c) = c := c.out_eq

/-- The demand obtained by summing endpoint pairs from a component root to
each vertex, weighted by the given demand. -/
noncomputable def componentPairDemand (G : FiniteMultiGraph) (y : G.Demand)
    (c : G.ConnectedComponent) : G.Demand := by
  classical
  exact ∑ v : G.ComponentVertex c,
    y v.1 • (G.vertexUnit (G.componentRoot c) + G.vertexUnit v.1)

theorem componentPairDemand_mem_range (G : FiniteMultiGraph) (y : G.Demand)
    (c : G.ConnectedComponent) :
    G.componentPairDemand y c ∈ LinearMap.range G.boundary := by
  classical
  unfold componentPairDemand
  apply Submodule.sum_mem
  intro v hv
  apply Submodule.smul_mem
  exact G.boundary_pair_mem_range_of_component_eq (G.componentRoot c) v.1
    ((G.componentOf_root c).trans v.2.symm)

private theorem componentVertex_single_sum (G : FiniteMultiGraph) (y : G.Demand)
    (c : G.ConnectedComponent) (z : G.Vertex)
    [Decidable (G.componentOf z = c)] :
    (∑ v : G.ComponentVertex c, y v.1 * (if v.1 = z then (1 : F₂) else 0)) =
      (if G.componentOf z = c then y z else 0) := by
  classical
  by_cases hz : G.componentOf z = c
  · let w : G.ComponentVertex c := ⟨z, hz⟩
    rw [Finset.sum_eq_single w]
    · rw [if_pos hz]
      simp [w]
    · intro v hv hne
      have hvz : v.1 ≠ z := by
        intro hEq
        apply hne
        apply Subtype.ext
        exact hEq
      simp [hvz]
    · simp [hz]
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro v hv
    have hvz : v.1 ≠ z := by
      intro hEq
      apply hz
      rw [← hEq]
      exact v.2
    simp [hvz]

theorem componentPairDemand_eq_restrict (G : FiniteMultiGraph) (y : G.Demand)
    (c : G.ConnectedComponent) (hEven : G.componentDemandSum y c = 0)
    [DecidableEq G.ConnectedComponent] :
    G.componentPairDemand y c = fun z =>
      if G.componentOf z = c then y z else 0 := by
  classical
  ext z
  unfold componentPairDemand
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hsum : (∑ v : G.ComponentVertex c, y v.1) = G.componentDemandSum y c := rfl
  rw [hsum, hEven]
  have hsingle := G.componentVertex_single_sum y c z
  have hsingle' :
      (∑ v : G.ComponentVertex c, y v.1 * G.vertexUnit v.1 z) =
        (if G.componentOf z = c then y z else 0) := by
    have hsingleFlip :
        (∑ v : G.ComponentVertex c, y v.1 *
          (if z = v.1 then (1 : F₂) else 0)) =
        (∑ v : G.ComponentVertex c, y v.1 *
          (if v.1 = z then (1 : F₂) else 0)) := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases h : z = v.1
      · simp [h]
      · have h' : v.1 ≠ z := fun hEq => h hEq.symm
        simp [h, h']
    calc
      _ = ∑ v : G.ComponentVertex c, y v.1 *
          (if z = v.1 then (1 : F₂) else 0) := by
        simp [vertexUnit, Pi.single_apply]
      _ = ∑ v : G.ComponentVertex c, y v.1 *
          (if v.1 = z then (1 : F₂) else 0) := hsingleFlip
      _ = _ := hsingle
  rw [hsingle']
  simp [vertexUnit]

/-- Sum the root-to-vertex pair constructions over all components. -/
noncomputable def totalComponentPairDemand (G : FiniteMultiGraph) (y : G.Demand) :
    G.Demand := by
  classical
  exact ∑ c : G.ConnectedComponent, G.componentPairDemand y c

theorem totalComponentPairDemand_mem_range (G : FiniteMultiGraph) (y : G.Demand) :
    G.totalComponentPairDemand y ∈ LinearMap.range G.boundary := by
  classical
  unfold totalComponentPairDemand
  apply Submodule.sum_mem
  intro c hc
  exact G.componentPairDemand_mem_range y c

theorem totalComponentPairDemand_eq_of_componentEven (G : FiniteMultiGraph)
    (y : G.Demand) (hy : G.ComponentEven y) :
    G.totalComponentPairDemand y = y := by
  classical
  ext z
  unfold totalComponentPairDemand
  simp only [Finset.sum_apply]
  simp_rw [G.componentPairDemand_eq_restrict y _ (hy _)]
  simp

/-- The componentwise parity condition is sufficient for a demand to be a
boundary. -/
theorem componentEven_mem_range (G : FiniteMultiGraph) (y : G.Demand)
    (hy : G.ComponentEven y) :
    y ∈ LinearMap.range G.boundary := by
  classical
  rw [← G.totalComponentPairDemand_eq_of_componentEven y hy]
  exact G.totalComponentPairDemand_mem_range y



private theorem componentDemandSum_rootUnit (G : FiniteMultiGraph)
    (c d : G.ConnectedComponent) [DecidableEq G.ConnectedComponent] :
    G.componentDemandSum (G.vertexUnit (G.componentRoot c)) d =
      if c = d then 1 else 0 := by
  classical
  unfold componentDemandSum
  simp only [vertexUnit, Pi.single_apply]
  by_cases hcd : c = d
  · subst d
    let w : G.ComponentVertex c := ⟨G.componentRoot c, G.componentOf_root c⟩
    rw [Finset.sum_eq_single w]
    · simp [w]
    · intro v hv hne
      have hvne : v.1 ≠ G.componentRoot c := by
        intro heq
        apply hne
        apply Subtype.ext
        exact heq
      simp [hvne]
    · simp
  · rw [if_neg hcd]
    apply Finset.sum_eq_zero
    intro v hv
    have hvne : v.1 ≠ G.componentRoot c := by
      intro heq
      apply hcd
      calc
        c = G.componentOf (G.componentRoot c) := (G.componentOf_root c).symm
        _ = G.componentOf v.1 := by rw [heq]
        _ = d := v.2
    simp [hvne]

/-- The map sending a vertex demand to its total on each component. -/
def componentTotalMap (G : FiniteMultiGraph) :
    G.Demand →ₗ[F₂] (G.ConnectedComponent → F₂) where
  toFun y c := G.componentDemandSum y c
  map_add' y z := by
    funext c
    simp [componentDemandSum, Finset.sum_add_distrib]
  map_smul' a y := by
    funext c
    simp [componentDemandSum, Finset.mul_sum]

theorem componentTotalMap_vertexUnit_root (G : FiniteMultiGraph)
    (c : G.ConnectedComponent) [DecidableEq G.ConnectedComponent] :
    G.componentTotalMap (G.vertexUnit (G.componentRoot c)) = Pi.single c 1 := by
  classical
  ext d
  rw [Pi.single_apply]
  simp [componentTotalMap, componentDemandSum_rootUnit, Pi.single_apply, eq_comm]

theorem componentTotalMap_surjective (G : FiniteMultiGraph)
    : Function.Surjective G.componentTotalMap := by
  classical
  intro f
  let y : G.Demand := ∑ c : G.ConnectedComponent, f c • G.vertexUnit (G.componentRoot c)
  refine ⟨y, ?_⟩
  calc
    G.componentTotalMap y =
        ∑ c : G.ConnectedComponent,
          f c • G.componentTotalMap (G.vertexUnit (G.componentRoot c)) := by
            simp [y]
    _ = ∑ c : G.ConnectedComponent, f c • Pi.single c 1 := by
          simp [G.componentTotalMap_vertexUnit_root]
    _ = f := by
          ext c
          simp [Pi.single_apply]

theorem range_boundary_eq_ker_componentTotalMap (G : FiniteMultiGraph)
    :
    LinearMap.range G.boundary = LinearMap.ker G.componentTotalMap := by
  classical
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    funext c
    exact G.boundary_componentDemandSum x c
  · intro hy
    rw [LinearMap.mem_ker] at hy
    apply G.componentEven_mem_range y
    intro c
    exact congrFun hy c

theorem boundaryRank_add_componentCount_eq_vertexCount (G : FiniteMultiGraph)
    :
    G.boundaryRank + G.componentCount = G.vertexCount := by
  classical
  have hnull := G.componentTotalMap.finrank_range_add_finrank_ker
  have hsurj := G.componentTotalMap_surjective
  have htop : LinearMap.range G.componentTotalMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrange : Module.finrank F₂ (LinearMap.range G.componentTotalMap) =
      G.componentCount := by
    rw [htop]
    simp [componentCount, Module.finrank_fintype_fun_eq_card]
  have hker : Module.finrank F₂ (LinearMap.ker G.componentTotalMap) =
      G.boundaryRank := by
    rw [← G.range_boundary_eq_ker_componentTotalMap]
    rfl
  have hdom : Module.finrank F₂ G.Demand = G.vertexCount := by
    simp [Demand]
  rw [hrange, hker, hdom] at hnull
  omega

/-- Euler's formula for the binary cycle rank of a finite labelled
multigraph. Loops and parallel edge labels are counted in `edgeCount`. -/
theorem euler_formula (G : FiniteMultiGraph) :
    G.cycleRank + G.vertexCount = G.edgeCount + G.componentCount := by
  classical
  apply G.euler_of_boundaryRank_add_componentCount
  exact G.boundaryRank_add_componentCount_eq_vertexCount

end
end FiniteMultiGraph
end Erdos1016
