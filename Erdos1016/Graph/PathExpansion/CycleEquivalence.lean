import Erdos1016.Graph.PathExpansion.Basic

set_option autoImplicit false

/-!
# Cycle-space equivalence for edge-disjoint route systems

If the route supports partition the physical edges, and every physical cycle
word is constant on each route support, then expansion gives an isomorphism of
the auxiliary and physical cycle spaces, provided the vertex map is bijective.
The constancy condition is an explicit graph-construction hypothesis: it is
not implied by edge-disjointness and endpoint data alone.
-/

noncomputable section

namespace Erdos1016
namespace FiniteMultiGraph

variable {A P : FiniteMultiGraph}

/-- Evaluation of a pushed demand at the image of a vertex, when the vertex
map is injective. -/
theorem pushDemand_apply_at_image (φ : A.Vertex → P.Vertex)
    (hφ : Function.Injective φ) (d : A.Demand) (v : A.Vertex) :
    pushDemand A P φ d (φ v) = d v := by
  classical
  simp only [pushDemand, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hwv
    have hne : φ w ≠ φ v := fun h => hwv (hφ h)
    simp [hne]
  · intro h
    exact (h (Finset.mem_univ v)).elim

/-- Pushing demands through an injective finite vertex map is injective. -/
theorem pushDemand_injective_of_injective (φ : A.Vertex → P.Vertex)
    (hφ : Function.Injective φ) :
    Function.Injective (pushDemand A P φ) := by
  intro d₁ d₂ h
  funext v
  have hv := congrFun h (φ v)
  rw [pushDemand_apply_at_image φ hφ d₁ v,
    pushDemand_apply_at_image φ hφ d₂ v] at hv
  exact hv

/-- Pick one physical edge from each route and read a physical word there. -/
def contractWord (R : EdgeDisjointRouteSystem A P) (y : P.EdgeWord) :
    A.EdgeWord := fun e => y (Classical.choose (R.nonempty e))

/-- If supports cover all physical edges and `y` is constant on each support,
expanding its contraction recovers `y`. Pairwise disjointness is part of `R`.
-/
theorem expand_contractWord_eq (R : EdgeDisjointRouteSystem A P)
    (hcover : ∀ p, ∃ e, p ∈ R.support e)
    (hconstant : ∀ (y : P.EdgeWord), y ∈ P.CycleSpace →
      ∀ e p q, p ∈ R.support e → q ∈ R.support e → y p = y q)
    (y : P.EdgeWord) (hy : y ∈ P.CycleSpace) :
    expand A P R (contractWord R y) = y := by
  classical
  funext p
  obtain ⟨e, hp⟩ := hcover p
  have hrepr : Classical.choose (R.nonempty e) ∈ R.support e :=
    Classical.choose_spec (R.nonempty e)
  rw [expand_apply_of_mem_support A P R (contractWord R y) e p hp]
  exact (hconstant y hy e p (Classical.choose (R.nonempty e)) hp hrepr).symm

/-- The expansion map restricted to cycle spaces. -/
def cycleExpandMap (R : EdgeDisjointRouteSystem A P) :
    A.CycleSpace →ₗ[F₂] P.CycleSpace where
  toFun x := ⟨expand A P R x.1, expand_cycle_of_boundary_zero A P R x.1 x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (expand A P R) x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (expand A P R) c x.1







end FiniteMultiGraph
end Erdos1016
