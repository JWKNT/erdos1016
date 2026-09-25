import Erdos1016.CycleSpace.EvenForestZero
import Erdos1016.Probability.Conditional.UniformReveal

set_option autoImplicit false

/-!
# Affine parity fibers for separated regions

Once outside coordinates are fixed, splitting the remaining boundary equations
by region identifies the reveal fiber with a product of local affine fibers.
This module supplies that exact equivalence and the local zero-boundary forest
estimate used for cyclic factors. Geometric hypotheses that yield the split
remain explicit in callers.
-/

noncomputable section

namespace Erdos1016.Proof.ConditionalRegionProduct







/-- A zero-boundary local factor on an edge set `S` has forest density at
most one half as soon as its restricted cycle space is nonzero. -/
theorem restrictedCycleSpace_forest_density_le_half
    (G : Erdos1016.PhysicalGraph) (S : Finset G.Edge)
    (hz : ∃ z : G.RestrictedCycleSpace S, z ≠ 0) :
    Erdos1016.Finite.density
      (fun x : G.RestrictedCycleSpace S =>
        (G.restrictedSelectedGraph S x.1).IsAcyclic) ≤ (1 / 2 : ℝ) := by
  let f : G.RestrictedCycleSpace S →ₗ[ZMod 2] G.RestrictedCycleSpace S :=
    LinearMap.id
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨z, hz⟩ := hz
    have hz' := congrArg (fun g : G.RestrictedCycleSpace S →ₗ[ZMod 2]
      G.RestrictedCycleSpace S => g z) h
    exact hz (by simpa [f] using hz')
  apply Erdos1016.Proof.NonzeroProjectionLoss.density_le_half_of_nonzero_linear_obstruction
    f hf _
  intro x hx
  have hzero := Erdos1016.Proof.CycleSpaceForestZero.restrictedWord_eq_zero_of_boundary_zero_of_acyclic
    G S x.1 x.2 hx
  apply Subtype.ext
  exact hzero





/-- Restricting an outside linear forest to any smaller edge set preserves
acyclicity. This is the event implication needed for a selected local factor
after all coordinates outside the regions have been revealed. -/
theorem outsideForest_implies_local_acyclic
    (G : Erdos1016.PhysicalGraph) (E S : Finset G.Edge)
    (hS : S ⊆ Eᶜ) (x : G.CycleSpace)
    (hx : x ∈ G.outsideLinearForestStates E) :
    (G.restrictedSelectedGraph S (G.restrictWord S x.1)).IsAcyclic := by
  classical
  have hforest : G.IsRestrictedLinearForest Eᶜ
      (G.restrictWord Eᶜ x.1) := by
    simpa [Erdos1016.PhysicalGraph.outsideLinearForestStates] using hx
  let A := G.restrictedSelectedGraph S (G.restrictWord S x.1)
  let B := G.restrictedSelectedGraph Eᶜ (G.restrictWord Eᶜ x.1)
  have hAB : A ≤ B := by
    intro u v hadj
    change ∃ e : G.RestrictedEdge S,
      G.restrictWord S x.1 e ≠ 0 ∧
        ((G.src e.1 = u ∧ G.dst e.1 = v) ∨
         (G.src e.1 = v ∧ G.dst e.1 = u)) at hadj
    rcases hadj with ⟨e, he, hsrc | hdst⟩
    · refine ⟨⟨e.1, hS e.2⟩, ?_, Or.inl hsrc⟩
      simpa [PhysicalGraph.restrictWord] using he
    · refine ⟨⟨e.1, hS e.2⟩, ?_, Or.inr hdst⟩
      simpa [PhysicalGraph.restrictWord] using he
  intro v p hp
  let inc : A →g B := {
    toFun := id
    map_rel' := by intro u v huv; exact hAB huv }
  have hinj : Function.Injective inc := by
    intro a b h
    simpa [inc] using h
  have hmap : (p.map inc).IsCycle := by
    exact (SimpleGraph.Walk.map_isCycle_iff_of_injective hinj).2 hp
  exact hforest.1 (p.map inc) hmap



end Erdos1016.Proof.ConditionalRegionProduct
