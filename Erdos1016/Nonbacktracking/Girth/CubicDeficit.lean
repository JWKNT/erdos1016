import Erdos1016.Decomposition.TwoCore.PhysicalCore

set_option autoImplicit false

/-!
# The high-girth cubic-deficit estimate

This is the order-versus-cubic-deficit lemma used for small high-girth pieces.
The upper order bound `N` is an explicit parameter, as in the paper.
-/

noncomputable section
namespace Erdos1016.Nonbacktracking

open FiniteTwoCore

local instance girthDeficitDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- A subcubic physical graph of order at most `N` and girth greater than `D`
has order bounded by its cubic deficit times the high-girth amplification
factor. Here the cubic deficit is `3|V| - sum_v degree(v)`, equivalently
`3|V| - 2|E|` for this finite simple graph. This formulation does not assume
connectedness. -/
theorem order_le_cubicDeficit_factor_of_girth
    (G : PhysicalGraph) (hmax : ∀ v, G.degree v ≤ 3)
    (N D : ℕ) (hGN : G.vertexCount ≤ N)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hell : Real.logb 2 (((max 2 N : ℕ) : ℝ) / 2) <
      ((D / 2 - 1 : ℕ) : ℝ)) :
    (G.vertexCount : ℝ) ≤
      (cubicDeficit G.toSimpleGraph Finset.univ : ℝ) *
        (1 + ((D / 2 - 1 : ℕ) : ℝ) /
          (((D / 2 - 1 : ℕ) : ℝ) -
            Real.logb 2 (((max 2 N : ℕ) : ℝ) / 2))) := by
  let C := maximalPhysicalCore G
  let H := inducedPhysical G C
  let uNat : ℕ := D / 2 - 1
  let u : ℝ := (uNat : ℝ)
  let ell : ℝ := Real.logb 2 (((max 2 N : ℕ) : ℝ) / 2)
  let d : ℝ := (cubicDeficit G.toSimpleGraph Finset.univ : ℝ)
  have hmaxGraph : ∀ v, G.toSimpleGraph.degree v ≤ 3 := by
    intro v
    rw [← original_degree_eq_graph_degree G v]
    exact hmax v
  have hdZ : 0 ≤ cubicDeficit G.toSimpleGraph Finset.univ :=
    cubicDeficit_nonneg G.toSimpleGraph Finset.univ hmaxGraph
  have hd : 0 ≤ d := by
    dsimp [d]
    exact_mod_cast hdZ
  have hell' : ell < u := hell
  have hden : 0 < u - ell := sub_pos.mpr hell'
  have hellNonneg : 0 ≤ ell := by
    apply Real.logb_nonneg (by norm_num : 1 < (2 : ℝ))
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hmaxN : 2 ≤ max 2 N := Nat.le_max_left 2 N
    exact_mod_cast hmaxN
  have hfactor : 1 ≤ 1 + u / (u - ell) := by
    have hu : 0 ≤ u := by linarith
    have hquot : 0 ≤ u / (u - ell) := div_nonneg hu hden.le
    linarith
  have horderZ := physicalOrder_le_core_add_cubicDeficit G hmax
  have horder : (G.vertexCount : ℝ) ≤ (C.card : ℝ) + d := by
    dsimp [C, d]
    exact_mod_cast horderZ
  have hcoreSubset : C.card ≤ G.vertexCount := by
    simpa [C, maximalPhysicalCore] using
      Finset.card_le_card (vertices_subset G.toSimpleGraph Finset.univ)
  have hcoreN : (C.card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcoreSubset.trans hGN
  have hcoreNmax : (C.card : ℝ) ≤ ((max 2 N : ℕ) : ℝ) := by
    exact hcoreN.trans (by exact_mod_cast (Nat.le_max_right 2 N))
  by_cases hsmall : (G.vertexCount : ℝ) ≤ d
  · calc
      (G.vertexCount : ℝ) ≤ d := hsmall
      _ ≤ d * (1 + u / (u - ell)) := by
        simpa using (mul_le_mul_of_nonneg_left hfactor hd)
  · have hlarge : d < (G.vertexCount : ℝ) := lt_of_not_ge hsmall
    have horderLower : (G.vertexCount : ℝ) - d ≤ (C.card : ℝ) := by
      linarith
    have hcorePositiveR : 0 < (C.card : ℝ) := by linarith
    have hcorePositive : 0 < C.card := by exact_mod_cast hcorePositiveR
    have hellCore : Real.logb 2 ((C.card : ℝ) / 2) ≤ ell := by
      apply Real.logb_le_logb_of_le (by norm_num : 1 < (2 : ℝ))
      · positivity
      · exact div_le_div_of_nonneg_right hcoreNmax (by norm_num)
    have htZ := maximalPhysicalCore_degreeTwo_le_cubicDeficit G hmax
    have ht : (Nonbacktracking.degreeTwoCount H : ℝ) ≤ d := by
      rw [inducedPhysical_degreeTwoCount_eq]
      dsimp [d]
      exact_mod_cast htZ
    have hnH : 0 < H.vertexCount := by
      rw [inducedPhysical_vertexCount_eq_card]
      exact hcorePositive
    have hgH := maximalPhysicalCore_girthGreater G D hg
    have huPos : 0 < u := lt_of_le_of_lt hellNonneg hell'
    have huNatPos : 0 < uNat := by
      dsimp [u] at huPos
      exact_mod_cast huPos
    have huNatSucc : uNat + 1 = D / 2 := by
      dsimp [uNat]
      exact Nat.sub_add_cancel (by omega)
    have hshort : 2 * (uNat + 1) ≤ D := by
      rw [huNatSucc]
      exact Nat.mul_div_le D 2
    have hentropy := degreeTwo_entropy_bound_of_girth H
      (maximalPhysicalCore_minDegree G)
      (maximalPhysicalCore_degree_le_three G hmax)
      hnH D uNat hgH hshort
    have hentropy' : u * (1 -
        (Nonbacktracking.degreeTwoCount H : ℝ) / (C.card : ℝ)) ≤
        Real.logb 2 ((C.card : ℝ) / 2) := by
      simpa [H, C, u, uNat, inducedPhysical_vertexCount_eq_card] using hentropy
    have hdenCore : 0 < (C.card : ℝ) := hcorePositiveR
    have hdenOriginal : 0 < (G.vertexCount : ℝ) - d := by linarith
    have hratio : (Nonbacktracking.degreeTwoCount H : ℝ) / (C.card : ℝ) ≤
        d / ((G.vertexCount : ℝ) - d) := by
      rw [div_le_div_iff₀ hdenCore hdenOriginal]
      have hmul₁ := mul_le_mul_of_nonneg_right ht (le_of_lt hdenOriginal)
      have hmul₂ := mul_le_mul_of_nonneg_left horderLower hd
      nlinarith
    have hu : 0 ≤ u := by linarith
    have hentropyBound : u * (1 - d / ((G.vertexCount : ℝ) - d)) ≤ ell := by
      calc
        _ ≤ u * (1 -
            (Nonbacktracking.degreeTwoCount H : ℝ) / (C.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hu
        _ ≤ Real.logb 2 ((C.card : ℝ) / 2) := hentropy'
        _ ≤ ell := hellCore
    have hnD : d < (G.vertexCount : ℝ) := hlarge
    have hfinal := order_le_deficit_factor
      (v := (G.vertexCount : ℝ)) (k := d) (u := u) (ell := ell)
      hnD hell' hentropyBound
    simpa [u, ell, d] using hfinal

end Erdos1016.Nonbacktracking
end
