import Erdos1016.Graph.PathExpansion.CycleEquivalence

set_option autoImplicit false

noncomputable section

namespace Erdos1016.FiniteMultiGraph

variable {A P : FiniteMultiGraph}

/-- Route expansion is bijective on cycle spaces when the auxiliary vertex
map is injective. Surjectivity is unnecessary: physical vertices inside a
suppressed route need not survive as auxiliary vertices. -/
theorem cycleExpandMap_bijective_of_injective
    (R : EdgeDisjointRouteSystem A P)
    (hφ : Function.Injective R.vertexMap)
    (hcover : ∀ p, ∃ e, p ∈ R.support e)
    (hconstant : ∀ (y : P.EdgeWord), y ∈ P.CycleSpace →
      ∀ e p q, p ∈ R.support e → q ∈ R.support e → y p = y q) :
    Function.Bijective (cycleExpandMap R) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply expand_injective A P R
    exact congrArg Subtype.val h
  · intro y
    let x : A.EdgeWord := contractWord R y.1
    have hxy : expand A P R x = y.1 :=
      expand_contractWord_eq R hcover hconstant y.1 y.2
    have hboundary : P.boundary (expand A P R x) = 0 := by
      rw [hxy]
      exact y.2
    have hsum : (∑ e, x e • endpointDemand A P R.vertexMap e) = 0 := by
      rw [← boundary_expand_eq_endpoint_sum A P R x]
      exact hboundary
    have hpush : pushDemand A P R.vertexMap (A.boundary x) = 0 := by
      rw [← endpoint_sum_eq_pushDemand_boundary A P R x]
      exact hsum
    have hxzero : A.boundary x = 0 := by
      apply pushDemand_injective_of_injective R.vertexMap hφ
      simpa using hpush
    refine ⟨⟨x, hxzero⟩, ?_⟩
    apply Subtype.ext
    exact hxy



end Erdos1016.FiniteMultiGraph

end
