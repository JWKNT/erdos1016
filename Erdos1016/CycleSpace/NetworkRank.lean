import Erdos1016.CycleSpace.Incidence

set_option autoImplicit false

/-!
# Euler rank for the actual labelled networks used by cycle events

Isolated vertices and disconnected exteriors are counted. The statement is
proved from incidence solvability and rank-nullity, not supplied as an input.
The network may have parallel labelled edges; no degree bound is used here.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace
local instance networkRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev networkRank (N : Network V E) : ℕ := Module.finrank Bit N.CycleSpace

@[simp] theorem cycleSpace_card_network (N : Network V E) :
    Fintype.card N.CycleSpace = 2 ^ networkRank N := by
  simpa [Bit] using Module.card_eq_pow_finrank (K := Bit) (V := N.CycleSpace)

theorem componentBoundary_surjective (N : Network V E) :
    Function.Surjective N.componentBoundary := by
  intro y
  refine ⟨push N.representative y, ?_⟩
  change push N.component (push N.representative y) = y
  rw [push_comp]
  have heq : N.component ∘ N.representative = id := by
    funext c
    exact N.component_representative c
  rw [heq, push_id]

theorem range_boundary_eq_ker_components (N : Network V E) :
    LinearMap.range N.boundary = LinearMap.ker N.componentBoundary := by
  ext t
  exact N.mem_range_boundary_iff t

/-- Addition form avoids truncated natural subtraction in empty graphs. -/
theorem network_rank_euler (N : Network V E) :
    networkRank N + Fintype.card V = Fintype.card E + Fintype.card N.Component := by
  have h₁ := N.boundary.finrank_range_add_finrank_ker
  have h₂ := N.componentBoundary.finrank_range_add_finrank_ker
  have hrange : LinearMap.range N.componentBoundary = ⊤ :=
    LinearMap.range_eq_top.2 (componentBoundary_surjective N)
  rw [hrange] at h₂
  rw [range_boundary_eq_ker_components N] at h₁
  have hv : Module.finrank Bit (V → Bit) = Fintype.card V := by simp
  have he : Module.finrank Bit (E → Bit) = Fintype.card E := by simp
  have hc : Module.finrank Bit (N.Component → Bit) = Fintype.card N.Component := by simp
  simp only [finrank_top, hv, he, hc] at h₁ h₂
  change Module.finrank Bit (LinearMap.ker N.componentBoundary) + networkRank N =
    Fintype.card E at h₁
  omega

theorem network_rank_int (N : Network V E) :
    (networkRank N : ℤ) =
      (Fintype.card E : ℤ) - Fintype.card V + Fintype.card N.Component := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (network_rank_euler N)
  push_cast at h
  omega

theorem connected_component_card (N : Network V E) (hN : N.graph.Connected) :
    Fintype.card N.Component = 1 := by
  haveI : Nonempty V := hN.nonempty
  haveI : Nonempty N.Component := ⟨N.component (Classical.choice hN.nonempty)⟩
  haveI : Subsingleton N.Component := hN.preconnected.subsingleton_connectedComponent
  letI : Unique N.Component :=
    ⟨⟨Classical.choice (inferInstance : Nonempty N.Component)⟩, fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique

/-- A connected owner has a single component even if the exterior is disconnected. -/
theorem connected_network_rank_int (N : Network V E) (hN : N.graph.Connected) :
    (networkRank N : ℤ) = (Fintype.card E : ℤ) - Fintype.card V + 1 := by
  rw [network_rank_int, connected_component_card N hN]
  norm_num

/-- Signed powers are used only for exact probabilities; negative exponents
are not represented by truncated natural-number subtraction. -/
def dyadic (k : ℤ) : ℝ := (2 : ℝ) ^ k

@[simp] theorem dyadic_zero : dyadic 0 = 1 := by simp [dyadic]

@[simp] theorem dyadic_nat (k : ℕ) : dyadic (k : ℤ) = (2 : ℝ) ^ k := by
  simp [dyadic]

theorem dyadic_pos (k : ℤ) : 0 < dyadic k := by
  unfold dyadic
  positivity

theorem dyadic_add (k l : ℤ) : dyadic (k + l) = dyadic k * dyadic l := by
  exact zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) k l

theorem dyadic_sub (k l : ℤ) : dyadic (k - l) = dyadic k / dyadic l := by
  simp [dyadic, sub_eq_add_neg, zpow_add₀, zpow_neg, div_eq_mul_inv]

theorem dyadic_mono {k l : ℤ} (h : k ≤ l) : dyadic k ≤ dyadic l := by
  have hn : 0 ≤ l - k := sub_nonneg.2 h
  let n := Int.toNat (l - k)
  have hn' : (n : ℤ) = l - k := Int.toNat_of_nonneg hn
  have heq : l = k + (n : ℤ) := by omega
  rw [heq, dyadic_add, dyadic_nat]
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  nlinarith [dyadic_pos k]

@[simp] theorem dyadic_neg_nat (k : ℕ) : dyadic (-(k : ℤ)) = 1 / (2 : ℝ) ^ k := by
  simp [dyadic, zpow_neg, div_eq_mul_inv]

end Erdos1016.BoundaryDecay
