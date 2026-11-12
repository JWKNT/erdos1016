import Erdos1016.PolynomialBound.Product

set_option autoImplicit false

/-!
# Two local forest bounds below the two-fifths threshold

These are numerical consequences of the proved product theorem. They do not
assert the existence of the required regions or derive their affine bounds.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport.Product

open FiniteMultiGraph

local instance productDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- Two disjoint regions whose every affine forest proportion is at most
three fifths force the ambient forest proportion below two fifths. -/
theorem forest_density_lt_two_fifths_of_two_regions
    (U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (E : Finset G.Edge) (hE₁ : G.internalEdges U₁ ⊆ E) (hE₂ : G.internalEdges U₂ ⊆ E)
    (h₁ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₁ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₁) (x.1 + z.1.1))) ≤ (3 / 5 : ℝ))
    (h₂ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₂ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₂) (x.1 + z.1.1))) ≤ (3 / 5 : ℝ)) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) <
      (2 / 5 : ℝ) := by
  have h := PolynomialBound.Product.forest_density_le_mul G U₁ U₂ hdisj E hE₁ hE₂
    (3 / 5) (3 / 5) h₁ h₂
  linarith

/-- A forest density of at least two fifths excludes two disjoint regions
whose affine forest proportions are each at most one half. -/
theorem not_two_half_regions
    (U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (E : Finset G.Edge) (hE₁ : G.internalEdges U₁ ⊆ E) (hE₂ : G.internalEdges U₂ ⊆ E)
    (h₁ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₁ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₁) (x.1 + z.1.1))) ≤ (1 / 2 : ℝ))
    (h₂ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₂ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₂) (x.1 + z.1.1))) ≤ (1 / 2 : ℝ))
    (hambient : (2 / 5 : ℝ) ≤
      Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1))) :
    False := by
  have h := PolynomialBound.Product.forest_density_le_mul G U₁ U₂ hdisj E hE₁ hE₂
    (1 / 2) (1 / 2) h₁ h₂
  linarith

end Erdos1016.ExactMaximumSupport.Product
