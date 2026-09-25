import Erdos1016.Nonbacktracking.Girth.CubicDeficit

set_option autoImplicit false

/-!
# Section 7.1 deficit-shrink corollary

This packages the quantitative arbitrary-subcubic pruning/Moore estimate as
the source's constant-factor conclusion (7.2). The full 2-core construction,
including isolated vertices and leaves, and the cubic-deficit ledger are
provided by `GirthDeficit` and `FiniteTwoCorePhysical`.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking
open FiniteTwoCore

local instance deficitShrinkDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Source Lemma 7.1's constant-factor form. Under its logarithmic gap
condition, the order of a high-girth subcubic physical graph is at most `C`
times its cubic deficit. The graph need not be connected. -/
theorem order_le_constant_cubicDeficit_of_girth
    (G : PhysicalGraph) (hmax : ∀ v, G.degree v ≤ 3)
    (M D : ℕ) (hM : 2 ≤ M) (hGM : G.vertexCount ≤ M)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (C : ℝ) (hC : 2 < C)
    (hgap : (((D / 2 - 1 : ℕ) : ℝ) *
        (1 - 1 / (C - 1))) > Real.logb 2 ((M : ℝ) / 2)) :
    (G.vertexCount : ℝ) ≤
      C * (FiniteTwoCore.cubicDeficit G.toSimpleGraph Finset.univ : ℝ) := by
  let A : ℝ := ((D / 2 - 1 : ℕ) : ℝ)
  let B : ℝ := Real.logb 2 ((M : ℝ) / 2)
  let δ : ℝ := (FiniteTwoCore.cubicDeficit G.toSimpleGraph Finset.univ : ℝ)
  have hCden : 0 < C - 1 := by linarith
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Real.logb_nonneg (by norm_num : 1 < (2 : ℝ))
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast hM
  have hApos : 0 < A := by
    dsimp [A, B] at hgap ⊢
    by_contra hnot
    have hA' : ((D / 2 - 1 : ℕ) : ℝ) = 0 := by
      have hnonneg : 0 ≤ ((D / 2 - 1 : ℕ) : ℝ) := by positivity
      linarith
    rw [hA'] at hgap
    simp at hgap
    linarith
  have hgap' : B < A * (1 - 1 / (C - 1)) := by
    dsimp [A, B] at *
    exact hgap
  have hden : B < A := by
    have hrecippos : 0 < 1 / (C - 1) := one_div_pos.mpr hCden
    have hreciplt : 1 / (C - 1) < 1 := by
      rw [div_lt_one hCden]
      linarith
    nlinarith
  have hfactor :
      1 + A / (A - B) ≤ C := by
    have hAB : 0 < A - B := sub_pos.mpr hden
    have haux : A / (C - 1) < A - B := by
      have hrewritten : A * (1 - 1 / (C - 1)) =
          A - A / (C - 1) := by ring
      rw [hrewritten] at hgap'
      linarith
    have hmul : A < (C - 1) * (A - B) := by
      nlinarith [((div_lt_iff₀ hCden).mp haux)]
    have hquot : A / (A - B) < C - 1 :=
      (div_lt_iff₀ hAB).2 (by nlinarith)
    linarith
  have hmaxEq : max 2 M = M := Nat.max_eq_right hM
  have hBmax : B = Real.logb 2 (((max 2 M : ℕ) : ℝ) / 2) := by
    simp [B, hmaxEq]
  have hquant := order_le_cubicDeficit_factor_of_girth G hmax M D hGM hg (by
    rw [← hBmax]
    exact hden)
  have hδnonneg : 0 ≤ δ := by
    dsimp [δ]
    have hmaxGraph : ∀ v, G.toSimpleGraph.degree v ≤ 3 := by
      intro v
      rw [← FiniteTwoCore.original_degree_eq_graph_degree G v]
      exact hmax v
    exact_mod_cast FiniteTwoCore.cubicDeficit_nonneg
      G.toSimpleGraph Finset.univ hmaxGraph
  have hquant' : (G.vertexCount : ℝ) ≤ δ * (1 + A / (A - B)) := by
    simpa [A, B, δ, hmaxEq] using hquant
  calc
    (G.vertexCount : ℝ) ≤ δ * (1 + A / (A - B)) := hquant'
    _ ≤ δ * C := mul_le_mul_of_nonneg_left hfactor hδnonneg
    _ = C * δ := by ring
    _ = _ := by rfl

end Erdos1016.Nonbacktracking
