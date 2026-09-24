import Erdos1016.Extremal.Capacity.CompositionProbability

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalEmbeddingForestProbability

open Erdos1016

/-- Restriction through an injective physical graph embedding preserves
acyclicity and the degree-at-most-two condition, including arbitrary witness
edge restrictions. -/
theorem forest_pullback
    (H G : PhysicalGraph) (vertex : H.Vertex → G.Vertex) (edge : H.Edge → G.Edge)
    (hvertex : Function.Injective vertex) (hedge : Function.Injective edge)
    (hsrc : ∀ e, G.src (edge e) = vertex (H.src e))
    (hdst : ∀ e, G.dst (edge e) = vertex (H.dst e))
    (W : Finset G.Edge) (V : Finset H.Edge)
    (hW : ∀ e, e ∈ V ↔ edge e ∈ W)
    (x : G.Word) (y : H.Word) (hcoord : ∀ e, y e = x (edge e))
    (hgood : G.IsRestrictedLinearForest Wᶜ (G.restrictWord Wᶜ x)) :
    H.IsRestrictedLinearForest Vᶜ (H.restrictWord Vᶜ y) := by
  classical
  let f : H.RestrictedEdge Vᶜ → G.RestrictedEdge Wᶜ := fun e =>
    ⟨edge e.1, Finset.mem_compl.mpr (fun h =>
      (Finset.mem_compl.mp e.2) ((hW e.1).mpr h))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact hedge (congrArg Subtype.val h)
  let J := H.restrictedSelectedGraph Vᶜ (H.restrictWord Vᶜ y)
  let K := G.restrictedSelectedGraph Wᶜ (G.restrictWord Wᶜ x)
  let hom : J →g K := {
    toFun := vertex
    map_rel' := by
      intro a b h
      rcases h with ⟨e, he, hs | hs⟩
      · refine ⟨f e, ?_, Or.inl ⟨?_, ?_⟩⟩
        · simpa [f, PhysicalGraph.restrictWord, hcoord] using he
        · exact (hsrc e.1).trans (congrArg vertex hs.1)
        · exact (hdst e.1).trans (congrArg vertex hs.2)
      · refine ⟨f e, ?_, Or.inr ⟨?_, ?_⟩⟩
        · simpa [f, PhysicalGraph.restrictWord, hcoord] using he
        · exact (hsrc e.1).trans (congrArg vertex hs.1)
        · exact (hdst e.1).trans (congrArg vertex hs.2) }
  constructor
  · intro v p hp
    exact hgood.1 (p.map hom) (hp.map hvertex)
  · intro v
    have hle : H.restrictedSelectedDegree Vᶜ (H.restrictWord Vᶜ y) v ≤
        G.restrictedSelectedDegree Wᶜ (G.restrictWord Wᶜ x) (vertex v) := by
      apply Finset.card_le_card_of_injOn f
      · intro e he
        have he' : y e.1 ≠ 0 ∧ H.incident e.1 v := (Finset.mem_filter.mp he).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · simpa [f, PhysicalGraph.restrictWord, hcoord] using he'.1
        · rcases he'.2 with hs | ht
          · exact Or.inl ((hsrc e.1).trans (congrArg vertex hs))
          · exact Or.inr ((hdst e.1).trans (congrArg vertex ht))
      · intro a ha b hb h
        exact hf h
    exact hle.trans (hgood.2 (vertex v))

/-- The graph's outside-forest probability is its uniform finite density. -/
theorem outside_probability_eq_density (G : PhysicalGraph) (W : Finset G.Edge) :
    G.outsideLinearForestProbability W = Finite.density (fun x : G.CycleSpace =>
      G.IsRestrictedLinearForest Wᶜ (G.restrictWord Wᶜ x.1)) := by
  have hcard : (Fintype.card G.CycleSpace : ℝ) = (2 : ℝ) ^ G.cycleRank := by
    exact_mod_cast G.cycleSpace_card
  unfold PhysicalGraph.outsideLinearForestProbability PhysicalGraph.outsideLinearForestStates
    Finite.density Finite.count
  rw [hcard]
  simp [Finset.sum_boole]

/-- A surjective cycle marginal along a physical embedding can only increase
the probability of being a linear forest outside the pulled-back witness. -/
theorem outside_probability_le_of_surjective_marginal
    (H G : PhysicalGraph) (vertex : H.Vertex → G.Vertex) (edge : H.Edge → G.Edge)
    (hvertex : Function.Injective vertex) (hedge : Function.Injective edge)
    (hsrc : ∀ e, G.src (edge e) = vertex (H.src e))
    (hdst : ∀ e, G.dst (edge e) = vertex (H.dst e))
    (W : Finset G.Edge) (V : Finset H.Edge)
    (hW : ∀ e, e ∈ V ↔ edge e ∈ W)
    (marginal : G.CycleSpace →ₗ[ZMod 2] H.CycleSpace)
    (hsurj : Function.Surjective marginal)
    (hcoord : ∀ x e, (marginal x).1 e = x.1 (edge e)) :
    G.outsideLinearForestProbability W ≤ H.outsideLinearForestProbability V := by
  classical
  rw [outside_probability_eq_density, outside_probability_eq_density]
  rw [← BoundaryTrace.density_surjective_linear marginal hsurj]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finite.count_mono (fun x hx =>
    forest_pullback H G vertex edge hvertex hedge hsrc hdst W V hW
      x.1 (marginal x).1 (hcoord x) hx)

end Erdos1016.Proof.PhysicalEmbeddingForestProbability

end
