import Erdos1016.Probability.Cylinders.Affine
import Erdos1016.Graph.Basic

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ActiveEdgeUniform

open Erdos1016

local notation "F₂" => ZMod 2

/-- The coordinate of an edge, restricted to the host cycle space. -/
def edgeCoordinate (G : PhysicalGraph) (e : G.Edge) :
    G.CycleSpace →ₗ[F₂] F₂ where
  toFun x := x.1 e
  map_add' x y := rfl
  map_smul' a x := rfl

/-- An edge is active when some cycle-space word uses it. -/
def ActiveEdge (G : PhysicalGraph) (e : G.Edge) : Prop :=
  ∃ x : G.CycleSpace, x.1 e = 1





/-- Uniform cycle-space density of the event that a specified edge is used. -/
def selectedDensity (G : PhysicalGraph) (e : G.Edge) : ℝ :=
  (Fintype.card {x : G.CycleSpace // x.1 e = 1} : ℝ) /
    (Fintype.card G.CycleSpace : ℝ)

/-- Every active physical edge is selected by exactly half of the uniform
cycle-space words. This is rank-nullity for its nonzero coordinate functional. -/
theorem selectedDensity_eq_half_of_active (G : PhysicalGraph) (e : G.Edge)
    (hactive : ActiveEdge G e) :
    selectedDensity G e = (1 / 2 : ℝ) := by
  classical
  let f := edgeCoordinate G e
  have hsurj : Function.Surjective f := by
    intro b
    by_cases hb : b = 0
    · exact ⟨0, by simp [f, hb]⟩
    · obtain ⟨x, hx⟩ := hactive
      have hb1 : b = 1 := by
        fin_cases b <;> simp_all
      refine ⟨x, ?_⟩
      rw [hb1]
      simpa [f, edgeCoordinate] using hx
  obtain ⟨x₁, hx₁⟩ := hsurj (1 : F₂)
  have hfiber := Erdos1016.Proof.AffineCylinders.fiber_card f
    (⟨x₁, hx₁⟩ : {x : G.CycleSpace // f x = 1})
  have htotal : Fintype.card G.CycleSpace =
      2 ^ Module.finrank F₂ G.CycleSpace := by
    have h := Module.natCard_eq_pow_finrank (K := F₂) (V := G.CycleSpace)
    simpa [Nat.card_eq_fintype_card] using h
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrank
  have hdim : Module.finrank F₂ (LinearMap.ker f) + 1 =
      Module.finrank F₂ G.CycleSpace := by
    rw [finrank_top, Module.finrank_self] at hrank
    omega
  have hden : (Fintype.card G.CycleSpace : ℝ) ≠ 0 := by
    rw [htotal]
    positivity
  have hcardEq : Fintype.card {x : G.CycleSpace // x.1 e = 1} =
      Fintype.card {x : G.CycleSpace // f x = 1} := by
    apply Fintype.card_congr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact ⟨x.1, by simpa [f, edgeCoordinate] using x.2⟩
    · intro x
      exact ⟨x.1, by simpa [f, edgeCoordinate] using x.2⟩
    · intro x
      rfl
    · intro x
      rfl
  unfold selectedDensity
  rw [hcardEq, hfiber, htotal]
  push_cast
  rw [← hdim, pow_succ]
  field_simp

end Erdos1016.Proof.ActiveEdgeUniform
