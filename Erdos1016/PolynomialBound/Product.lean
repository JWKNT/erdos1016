import Erdos1016.Probability.Cylinders.RegionCycleEvents
import Erdos1016.Probability.Moments.SecondMoments

set_option autoImplicit false

/-!
# Two disjoint regions multiply

Let `U₁` and `U₂` be disjoint vertex regions of a multigraph. Fix an even
word `x`. The even words that agree with `x` outside the internal edges of
the two regions are the words `x + z₁ + z₂`, where `z_i` is an even word
supported on the internal edges of `U_i`. So, given the edges outside the two
regions, the two internal parts are independent and each is uniform in its
parity class.

Suppose that in each region every such class has forest proportion at most
`a_i`. Then the probability that a uniform even word is a forest on an edge
set that contains both regions is at most `a₁ a₂`.

In the proof of the exact one-half bound the two regions are two clean
pieces, and `a₁ = a₂ = 3 / 5`.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.PolynomialBound.Product

open FiniteMultiGraph BoundaryDecay

local instance productDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- **Product of two regions.** If every parity class of each of two disjoint
regions has forest proportion at most `a_i`, then the forest probability on
any edge set that contains the internal edges of both regions is at most
`a₁ a₂`. -/
theorem forest_density_le_mul (U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (E : Finset G.Edge) (hE₁ : G.internalEdges U₁ ⊆ E) (hE₂ : G.internalEdges U₂ ⊆ E)
    (a₁ a₂ : ℝ)
    (h₁ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₁ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₁) (x.1 + z.1.1))) ≤ a₁)
    (h₂ : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U₂ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₂) (x.1 + z.1.1))) ≤ a₂) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      a₁ * a₂ := by
  classical
  let f : G.CycleSpace → ℝ :=
    indicator (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1))
  let g₁ : G.CycleSpace → G.internalCycleSpace U₁ → ℝ := fun x =>
    indicator (fun z : G.internalCycleSpace U₁ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₁) (x.1 + z.1.1)))
  let g₂ : G.CycleSpace → G.internalCycleSpace U₂ → ℝ := fun x =>
    indicator (fun z : G.internalCycleSpace U₂ =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U₂) (x.1 + z.1.1)))
  have hg₁0 (x : G.CycleSpace) (z : G.internalCycleSpace U₁) : 0 ≤ g₁ x z := by
    simp only [g₁, indicator]
    split_ifs <;> norm_num
  have hg₂0 (x : G.CycleSpace) (z : G.internalCycleSpace U₂) : 0 ≤ g₂ x z := by
    simp only [g₂, indicator]
    split_ifs <;> norm_num
  -- a forest on `E` is a forest in each region, and the other region does not matter
  have hpoint (x : G.CycleSpace) (z₁ : G.internalCycleSpace U₁)
      (z₂ : G.internalCycleSpace U₂) : f (x + z₁.1 + z₂.1) ≤ g₁ x z₁ * g₂ x z₂ := by
    by_cases hx : G.IsForestWord (G.restrictEdges E (x + z₁.1 + z₂.1).1)
    · have h1 : G.IsForestWord (G.restrictEdges (G.internalEdges U₁) (x.1 + z₁.1.1)) := by
        apply hx.mono
        intro e he
        by_cases hmem : e ∈ G.internalEdges U₁
        · have hz : z₂.1.1 e = 0 := G.internal_vanish_on_disjoint U₂ U₁ hdisj.symm z₂ e hmem
          have hval : (x + z₁.1 + z₂.1).1 e = (x.1 + z₁.1.1) e := by
            show x.1 e + z₁.1.1 e + z₂.1.1 e = x.1 e + z₁.1.1 e
            rw [hz, add_zero]
          have hE := hE₁ hmem
          simp only [restrictEdges, hmem, hE, if_true] at he ⊢
          rw [hval]
          exact he
        · simp [restrictEdges, hmem] at he
      have h2 : G.IsForestWord (G.restrictEdges (G.internalEdges U₂) (x.1 + z₂.1.1)) := by
        apply hx.mono
        intro e he
        by_cases hmem : e ∈ G.internalEdges U₂
        · have hz : z₁.1.1 e = 0 := G.internal_vanish_on_disjoint U₁ U₂ hdisj z₁ e hmem
          have hval : (x + z₁.1 + z₂.1).1 e = (x.1 + z₂.1.1) e := by
            show x.1 e + z₁.1.1 e + z₂.1.1 e = x.1 e + z₂.1.1 e
            rw [hz, add_zero]
          have hE := hE₂ hmem
          simp only [restrictEdges, hmem, hE, if_true] at he ⊢
          rw [hval]
          exact he
        · simp [restrictEdges, hmem] at he
      have e0 : f (x + z₁.1 + z₂.1) = 1 := by
        simp only [f, indicator]
        rw [if_pos hx]
      have e1 : g₁ x z₁ = 1 := by
        simp only [g₁, indicator]
        rw [if_pos h1]
      have e2 : g₂ x z₂ = 1 := by
        simp only [g₂, indicator]
        rw [if_pos h2]
      rw [e0, e1, e2, mul_one]
    · have e0 : f (x + z₁.1 + z₂.1) = 0 := by
        simp only [f, indicator]
        rw [if_neg hx]
      rw [e0]
      exact mul_nonneg (hg₁0 x z₁) (hg₂0 x z₂)
  -- translation by an even word preserves the uniform law
  have hshift (z : G.CycleSpace) : (∑ x, f (x + z)) = ∑ x, f x :=
    Fintype.sum_equiv (Equiv.addRight z) _ _ (fun x => rfl)
  have hsum1 (z₁ : G.internalCycleSpace U₁) (z₂ : G.internalCycleSpace U₂) :
      (∑ x, f (x + z₁.1 + z₂.1)) = ∑ x, f x := by
    have h := hshift (z₁.1 + z₂.1)
    simpa only [add_assoc] using h
  have hcount : (Fintype.card (G.internalCycleSpace U₁) : ℝ) *
      (Fintype.card (G.internalCycleSpace U₂) : ℝ) * ∑ x, f x =
      ∑ x, ∑ z₁ : G.internalCycleSpace U₁, ∑ z₂ : G.internalCycleSpace U₂,
        f (x + z₁.1 + z₂.1) := by
    symm
    calc
      (∑ x, ∑ z₁ : G.internalCycleSpace U₁, ∑ z₂ : G.internalCycleSpace U₂,
          f (x + z₁.1 + z₂.1)) =
          ∑ z₁ : G.internalCycleSpace U₁, ∑ x, ∑ z₂ : G.internalCycleSpace U₂,
            f (x + z₁.1 + z₂.1) := Finset.sum_comm
      _ = ∑ z₁ : G.internalCycleSpace U₁, ∑ z₂ : G.internalCycleSpace U₂, ∑ x,
            f (x + z₁.1 + z₂.1) := Finset.sum_congr rfl fun z₁ _ => Finset.sum_comm
      _ = ∑ _z₁ : G.internalCycleSpace U₁, ∑ _z₂ : G.internalCycleSpace U₂, ∑ x, f x := by
        simp only [hsum1]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hW₁ : (0 : ℝ) < Fintype.card (G.internalCycleSpace U₁) := by
    exact_mod_cast Fintype.card_pos
  have hW₂ : (0 : ℝ) < Fintype.card (G.internalCycleSpace U₂) := by
    exact_mod_cast Fintype.card_pos
  have hV : (0 : ℝ) < Fintype.card G.CycleSpace := by
    exact_mod_cast Fintype.card_pos
  have hrow₁ (x : G.CycleSpace) :
      (∑ z, g₁ x z) ≤ a₁ * Fintype.card (G.internalCycleSpace U₁) := by
    have h : average (g₁ x) ≤ a₁ := h₁ x
    unfold average at h
    exact (div_le_iff₀ hW₁).mp h
  have hrow₂ (x : G.CycleSpace) :
      (∑ z, g₂ x z) ≤ a₂ * Fintype.card (G.internalCycleSpace U₂) := by
    have h : average (g₂ x) ≤ a₂ := h₂ x
    unfold average at h
    exact (div_le_iff₀ hW₂).mp h
  have hmain : (Fintype.card (G.internalCycleSpace U₁) : ℝ) *
      (Fintype.card (G.internalCycleSpace U₂) : ℝ) * ∑ x, f x ≤
      (Fintype.card G.CycleSpace : ℝ) *
        ((a₁ * Fintype.card (G.internalCycleSpace U₁)) *
          (a₂ * Fintype.card (G.internalCycleSpace U₂))) := by
    rw [hcount]
    calc
      (∑ x, ∑ z₁ : G.internalCycleSpace U₁, ∑ z₂ : G.internalCycleSpace U₂,
          f (x + z₁.1 + z₂.1)) ≤
          ∑ x, ∑ z₁ : G.internalCycleSpace U₁, ∑ z₂ : G.internalCycleSpace U₂,
            g₁ x z₁ * g₂ x z₂ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z₁ _ =>
          Finset.sum_le_sum fun z₂ _ => hpoint x z₁ z₂
      _ = ∑ x : G.CycleSpace, (∑ z₁, g₁ x z₁) * (∑ z₂, g₂ x z₂) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul_sum]
      _ ≤ ∑ _x : G.CycleSpace, (a₁ * Fintype.card (G.internalCycleSpace U₁)) *
            (a₂ * Fintype.card (G.internalCycleSpace U₂)) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul (hrow₁ x) (hrow₂ x)
          (Finset.sum_nonneg fun z _ => hg₂0 x z)
          (le_trans (Finset.sum_nonneg fun z _ => hg₁0 x z) (hrow₁ x))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : (∑ x, f x) ≤ a₁ * a₂ * Fintype.card G.CycleSpace := by
    have hpos := mul_pos hW₁ hW₂
    have hrewrite : (Fintype.card G.CycleSpace : ℝ) *
        ((a₁ * Fintype.card (G.internalCycleSpace U₁)) *
          (a₂ * Fintype.card (G.internalCycleSpace U₂))) =
        (Fintype.card (G.internalCycleSpace U₁) : ℝ) *
          (Fintype.card (G.internalCycleSpace U₂) : ℝ) *
          (a₁ * a₂ * Fintype.card G.CycleSpace) := by ring
    rw [hrewrite] at hmain
    exact le_of_mul_le_mul_left hmain hpos
  have hgoal : average f ≤ a₁ * a₂ := by
    unfold average
    exact (div_le_iff₀ hV).mpr hsum
  exact hgoal

end Erdos1016.PolynomialBound.Product
