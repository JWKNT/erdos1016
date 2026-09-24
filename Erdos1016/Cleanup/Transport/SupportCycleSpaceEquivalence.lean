import Erdos1016.Cleanup.Support.RestrictedComponentGraph

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.SupportCycleSpaceEquivalence

open Erdos1016
open Erdos1016.Proof.ActivePhysicalComponents
open Erdos1016.Proof.RestrictedComponentGraph

local notation "F₂" => ZMod 2

/-- Relabel the edge words of the support-induced component graph by the
existing edge-restricted physical graph. -/
def componentSupportWordEquiv (G : PhysicalGraph) (c : ActiveComponent G) :
    (componentSupportPhysical G c).Word ≃ₗ[F₂]
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).Word where
  toFun x e := x ((componentSupportEdgeEquiv G c).symm e)
  invFun x e := x (componentSupportEdgeEquiv G c e)
  left_inv x := by
    funext e
    simp
  right_inv x := by
    funext e
    simp
  map_add' x y := by
    funext e
    rfl
  map_smul' a x := by
    funext e
    rfl

@[simp] theorem componentSupportWordEquiv_apply
    (G : PhysicalGraph) (c : ActiveComponent G)
    (x : (componentSupportPhysical G c).Word)
    (e : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Edge) :
    componentSupportWordEquiv G c x e =
      x ((componentSupportEdgeEquiv G c).symm e) := rfl

/-- At a support vertex, the boundary sum is unchanged by edge relabelling. -/
theorem componentSupport_boundary_eq
    (G : PhysicalGraph) (c : ActiveComponent G)
    (x : (componentSupportPhysical G c).Word)
    (u : (componentSupportPhysical G c).Vertex) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).boundary
        (componentSupportWordEquiv G c x)
        (componentSupportVertexMap G c u) =
      (componentSupportPhysical G c).boundary x u := by
  classical
  let H := componentSupportPhysical G c
  let R := (activeSubgraph G).restrictPhysical (componentEdges G c)
  let φ := componentSupportEdgeEquiv G c
  let f := componentSupportVertexMap G c
  change (∑ e : R.Edge,
      ((if R.src e = f u then (componentSupportWordEquiv G c x) e else 0) +
       (if R.dst e = f u then (componentSupportWordEquiv G c x) e else 0))) =
    ∑ e : H.Edge,
      ((if H.src e = u then x e else 0) +
       (if H.dst e = u then x e else 0))
  calc
    _ = ∑ e : H.Edge,
        ((if R.src (φ e) = f u then (componentSupportWordEquiv G c x) (φ e) else 0) +
         (if R.dst (φ e) = f u then (componentSupportWordEquiv G c x) (φ e) else 0)) := by
      symm
      apply Fintype.sum_equiv φ
      intro e
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      have hsrc : f (H.src e) = f u ↔ H.src e = u := by
        constructor
        · intro h
          exact componentSupportVertexMap_injective G c h
        · intro h
          rw [h]
      have hdst : f (H.dst e) = f u ↔ H.dst e = u := by
        constructor
        · intro h
          exact componentSupportVertexMap_injective G c h
        · intro h
          rw [h]
      simp [H, R, φ, f, componentSupportWordEquiv,
        componentSupportEdgeEquiv_src, componentSupportEdgeEquiv_dst,
        hsrc, hdst]

/-- Outside the chosen component support, every edge of its restricted graph
has zero incidence, so its boundary coordinate is zero. -/
theorem componentSupport_boundary_eq_zero_off
    (G : PhysicalGraph) (c : ActiveComponent G)
    (x : (componentSupportPhysical G c).Word)
    (v : ((activeSubgraph G).restrictPhysical (componentEdges G c)).Vertex)
    (hv : v ∉ componentSupportFinset G c) :
    ((activeSubgraph G).restrictPhysical (componentEdges G c)).boundary
      (componentSupportWordEquiv G c x) v = 0 := by
  classical
  let H := componentSupportPhysical G c
  let R := (activeSubgraph G).restrictPhysical (componentEdges G c)
  let φ := componentSupportEdgeEquiv G c
  have hsrc : ∀ e : R.Edge, R.src e ≠ v := by
    intro e he
    have hmem : R.src e ∈ componentSupportFinset G c := by
      rw [← φ.apply_symm_apply e]
      rw [componentSupportEdgeEquiv_src]
      exact componentSupportVertexMap_mem_support G c _
    exact hv (he ▸ hmem)
  have hdst : ∀ e : R.Edge, R.dst e ≠ v := by
    intro e he
    have hmem : R.dst e ∈ componentSupportFinset G c := by
      rw [← φ.apply_symm_apply e]
      rw [componentSupportEdgeEquiv_dst]
      exact componentSupportVertexMap_mem_support G c _
    exact hv (he ▸ hmem)
  change (∑ e : R.Edge,
      ((if R.src e = v then (componentSupportWordEquiv G c x) e else 0) +
       (if R.dst e = v then (componentSupportWordEquiv G c x) e else 0))) = 0
  apply Finset.sum_eq_zero
  intro e _
  simp [hsrc e, hdst e]

/-- The support-induced graph and the old edge-restricted graph have
isomorphic binary cycle spaces. Vertices outside the active component support
are isolated in the old graph and impose only the zero boundary equation. -/
def componentSupportCycleSpaceEquiv (G : PhysicalGraph) (c : ActiveComponent G) :
    (componentSupportPhysical G c).CycleSpace ≃ₗ[F₂]
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).CycleSpace where
  toFun x := by
    refine ⟨componentSupportWordEquiv G c x.1, ?_⟩
    funext v
    by_cases hv : v ∈ componentSupportFinset G c
    · obtain ⟨u, hu⟩ := componentSupportVertexMap_surj_on_support G c hv
      rw [← hu]
      rw [componentSupport_boundary_eq]
      exact congrFun x.2 u
    · exact componentSupport_boundary_eq_zero_off G c x.1 v hv
  invFun y := by
    refine ⟨(componentSupportWordEquiv G c).symm y.1, ?_⟩
    funext u
    have hboundary := congrFun y.2 (componentSupportVertexMap G c u)
    have heq : componentSupportWordEquiv G c
        ((componentSupportWordEquiv G c).symm y.1) = y.1 :=
      (componentSupportWordEquiv G c).apply_symm_apply y.1
    rw [← heq, componentSupport_boundary_eq] at hboundary
    exact hboundary
  left_inv x := by
    apply Subtype.ext
    exact (componentSupportWordEquiv G c).left_inv x.1
  right_inv y := by
    apply Subtype.ext
    exact (componentSupportWordEquiv G c).right_inv y.1
  map_add' x y := by
    apply Subtype.ext
    exact (componentSupportWordEquiv G c).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact (componentSupportWordEquiv G c).map_smul a x.1

/-- Consequently the cycle rank used in the active-component share estimate
is exactly the rank of its support-induced physical graph. -/
theorem componentSupport_cycleRank_eq
    (G : PhysicalGraph) (c : ActiveComponent G) :
    (componentSupportPhysical G c).cycleRank =
      ((activeSubgraph G).restrictPhysical (componentEdges G c)).cycleRank := by
  unfold PhysicalGraph.cycleRank
  exact (componentSupportCycleSpaceEquiv G c).finrank_eq

end Erdos1016.Proof.SupportCycleSpaceEquivalence
end
