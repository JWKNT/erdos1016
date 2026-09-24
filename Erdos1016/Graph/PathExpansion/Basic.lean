import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false

/-!
# Abstract edge-disjoint path expansion

This file isolates the linear-algebra part of replacing each edge of a finite
auxiliary multigraph by an edge-disjoint route in a physical multigraph.  A
route is represented by its physical-edge support, together with its exact
mod-two endpoint boundary.  Thus all conclusions below are conditional on
such support and endpoint data being constructed; this file does not assert
connectedness of arbitrary supports or construct routes in a particular graph.
-/

noncomputable section

namespace Erdos1016
namespace FiniteMultiGraph

variable (A P : FiniteMultiGraph)

/-- The indicator edge-word of a finite physical-edge set. -/
def edgeSetWord (S : Finset P.Edge) : P.EdgeWord := fun p =>
  if p ∈ S then 1 else 0

/-- The endpoint demand of one auxiliary edge, in characteristic two. -/
def endpointDemand (φ : A.Vertex → P.Vertex) (e : A.Edge) : P.Demand := fun v =>
  (if φ (A.src e) = v then 1 else 0) + (if φ (A.dst e) = v then 1 else 0)

/-- Push a vertex demand through a vertex map by summing over each fiber. -/
def pushDemand (φ : A.Vertex → P.Vertex) : A.Demand →ₗ[F₂] P.Demand where
  toFun d p := ∑ v, if φ v = p then d v else 0
  map_add' d₁ d₂ := by
    classical
    ext p
    simp only [Finset.sum_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp
  map_smul' c d := by
    classical
    ext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    split_ifs <;> simp [mul_comm]

/-- Summing the two endpoint slots of an edge over a vertex fiber gives the
two endpoint slots after mapping the vertices. -/
theorem pushDemand_endpoint (φ : A.Vertex → P.Vertex) (e : A.Edge) :
    pushDemand A P φ (endpointDemand A A (fun v => v) e) =
      endpointDemand A P φ e := by
  classical
  ext p
  simp only [pushDemand, LinearMap.coe_mk, AddHom.coe_mk, endpointDemand]
  calc
    (∑ v, if φ v = p then
        (if A.src e = v then (1 : F₂) else 0) +
          (if A.dst e = v then (1 : F₂) else 0) else 0) =
      (∑ v, (if φ v = p then if A.src e = v then (1 : F₂) else 0 else 0)) +
        (∑ v, (if φ v = p then if A.dst e = v then (1 : F₂) else 0 else 0)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v hv
          by_cases h : φ v = p <;> simp [h]
    _ = (if φ (A.src e) = p then 1 else 0) +
          (if φ (A.dst e) = p then 1 else 0) := by
          have hs : (∑ v, if φ v = p then
              if A.src e = v then (1 : F₂) else 0 else 0) =
              (if φ (A.src e) = p then 1 else 0) := by
            rw [Finset.sum_eq_single (A.src e)]
            · simp
            · intro v hv hne
              simp [ne_comm, hne]
            · intro hmem
              exact (hmem (Finset.mem_univ _)).elim
          have ht : (∑ v, if φ v = p then
              if A.dst e = v then (1 : F₂) else 0 else 0) =
              (if φ (A.dst e) = p then 1 else 0) := by
            rw [Finset.sum_eq_single (A.dst e)]
            · simp
            · intro v hv hne
              simp [ne_comm, hne]
            · intro hmem
              exact (hmem (Finset.mem_univ _)).elim
          rw [hs, ht]

/-- The auxiliary boundary is the sum of its individual endpoint demands. -/
theorem boundary_eq_endpoint_sum (x : A.EdgeWord) :
    A.boundary x = ∑ e, x e • endpointDemand A A (fun v => v) e := by
  classical
  ext v
  simp only [FiniteMultiGraph.boundary, LinearMap.coe_mk, AddHom.coe_mk,
    endpointDemand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : A.src e = v <;> by_cases ht : A.dst e = v <;>
    simp [hs, ht] <;> ring

/-- A support assignment for replacement routes. `endpoint` says that each
route has exactly the boundary prescribed by its two auxiliary endpoints;
`disjoint` says distinct routes share no physical edge; and `nonempty` rules
out a zero-length route, which is needed for injectivity. -/
structure EdgeDisjointRouteSystem where
  vertexMap : A.Vertex → P.Vertex
  support : A.Edge → Finset P.Edge
  endpoint : ∀ e, P.boundary (edgeSetWord P (support e)) =
    endpointDemand A P vertexMap e
  disjoint : ∀ ⦃e f⦄, e ≠ f → Disjoint (support e) (support f)
  nonempty : ∀ e, (support e).Nonempty

/-- The mapped endpoint demands of an auxiliary word are the push-forward of
its incidence boundary. No injectivity assumption on `vertexMap` is needed. -/
theorem endpoint_sum_eq_pushDemand_boundary
    (R : EdgeDisjointRouteSystem A P) (x : A.EdgeWord) :
    (∑ e, x e • endpointDemand A P R.vertexMap e) =
      pushDemand A P R.vertexMap (A.boundary x) := by
  classical
  rw [boundary_eq_endpoint_sum A x, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_smul, pushDemand_endpoint A P R.vertexMap e]

/-- Expand an auxiliary edge-word by putting its coefficient on every edge of
the corresponding replacement route. -/
def expand (R : EdgeDisjointRouteSystem A P) : A.EdgeWord →ₗ[F₂] P.EdgeWord where
  toFun x := ∑ e, x e • edgeSetWord P (R.support e)
  map_add' x y := by
    classical
    ext p
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [edgeSetWord, mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  map_smul' c x := by
    classical
    ext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hp : p ∈ R.support e <;> simp [edgeSetWord, hp]

@[simp] theorem expand_apply (R : EdgeDisjointRouteSystem A P)
    (x : A.EdgeWord) (p : P.Edge) :
    expand A P R x p = ∑ e, if p ∈ R.support e then x e else 0 := by
  classical
  simp [expand, edgeSetWord, smul_eq_mul]

/-- At a physical edge of a given route, expansion reads exactly that route's
coefficient, because the route supports are pairwise disjoint. -/
theorem expand_apply_of_mem_support (R : EdgeDisjointRouteSystem A P)
    (x : A.EdgeWord) (e : A.Edge) (p : P.Edge) (hp : p ∈ R.support e) :
    expand A P R x p = x e := by
  classical
  rw [expand_apply]
  rw [Finset.sum_eq_single e]
  · simp [hp]
  · intro f hf hfe
    have hdis := R.disjoint (Ne.symm hfe)
    have hnot : p ∉ R.support f := by
      intro hpf
      exact (Finset.disjoint_left.mp hdis) hp hpf
    simp [hnot]
  · intro he
    exact (he (Finset.mem_univ e)).elim

/-- Edge-disjoint nonempty routes make expansion injective. -/
theorem expand_injective (R : EdgeDisjointRouteSystem A P) :
    Function.Injective (expand A P R) := by
  classical
  intro x y h
  funext e
  obtain ⟨p, hp⟩ := R.nonempty e
  have hxy := congrFun h p
  rw [expand_apply_of_mem_support A P R x e p hp,
    expand_apply_of_mem_support A P R y e p hp] at hxy
  exact hxy





/-- Boundary is the sum of the route endpoint demands, with the auxiliary
edge coefficients. This is the precise interface needed to transport cycle
words once the endpoint map is identified with the auxiliary vertex set. -/
theorem boundary_expand_eq_endpoint_sum (R : EdgeDisjointRouteSystem A P)
    (x : A.EdgeWord) :
    P.boundary (expand A P R x) =
      ∑ e, x e • endpointDemand A P R.vertexMap e := by
  classical
  change P.boundary (∑ e, x e • edgeSetWord P (R.support e)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_smul, R.endpoint]



/-- A boundary-zero auxiliary word expands to a physical cycle. -/
theorem expand_cycle_of_boundary_zero (R : EdgeDisjointRouteSystem A P)
    (x : A.EdgeWord) (hx : A.boundary x = 0) :
    expand A P R x ∈ P.CycleSpace := by
  change P.boundary (expand A P R x) = 0
  rw [boundary_expand_eq_endpoint_sum, endpoint_sum_eq_pushDemand_boundary, hx]
  ext p
  simp [pushDemand]

end FiniteMultiGraph
end Erdos1016
