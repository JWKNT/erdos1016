import Erdos1016.ExactMaximumSupport.PoleMarginLayers

set_option autoImplicit false

/-!
# Partial ingredients for the bounded-port girth-five path bound

These are the scalar bridge-factor count and the actual bridgeless rank bound
from a bounded short-cycle transversal. They do not assume or assert a supplied
suppression/block model. The full bounded-port theorem remains to be assembled
from the actual graph reductions.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PoleGirthGap
open scoped BigOperators
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- More than half of the full product permits at most ten factors of size at most 15/16. -/
theorem deficient_factors_le_ten {ι : Type*} [Fintype ι]
    (ρ : ι → ℝ) (bad : Finset ι)
    (hzero : ∀ i, 0 ≤ ρ i) (hone : ∀ i, ρ i ≤ 1)
    (hbad : ∀ i ∈ bad, ρ i ≤ 15/16)
    (hrich : (1/2 : ℝ) < ∏ i, ρ i) : bad.card ≤ 10 := by
  classical
  have hprod : (∏ i, ρ i) ≤ (15/16 : ℝ)^bad.card := by
    calc
      _ ≤ ∏ i, if i ∈ bad then (15/16 : ℝ) else 1 := by
        apply Finset.prod_le_prod
        · intro i _; exact hzero i
        · intro i _
          by_cases hi : i ∈ bad
          · simpa only [if_pos hi] using hbad i hi
          · simpa only [if_neg hi] using hone i
      _ = _ := by simp only [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  by_cases hcard : 11 ≤ bad.card
  · have hpow : (15/16 : ℝ)^bad.card ≤ (15/16 : ℝ)^11 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
    have hsmall : (15/16 : ℝ)^11 < 1/2 := by norm_num
    exact False.elim ((not_lt_of_ge (hprod.trans hpow)) (hsmall.trans hrich))
  · omega

/-- A bounded family of full factors plus the gap bounds the total number of blocks. -/
theorem blocks_card_le {ι : Type*} [Fintype ι]
    (ρ : ι → ℝ) (full : Finset ι) (d : ℕ)
    (hzero : ∀ i, 0 ≤ ρ i) (hone : ∀ i, ρ i ≤ 1)
    (hgap : ∀ i, i ∉ full → ρ i ≤ 15/16)
    (hrich : (1/2 : ℝ) < ∏ i, ρ i) (hfull : full.card ≤ d) :
    Fintype.card ι ≤ d+10 := by
  classical
  let bad := Finset.univ \ full
  have hb : bad.card ≤ 10 := deficient_factors_le_ten ρ bad hzero hone
    (fun i hi => hgap i (Finset.mem_sdiff.mp hi).2) hrich
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ full)
  change bad.card + full.card = Finset.univ.card at hc
  rw [Finset.card_univ] at hc
  omega

/-- In the actual bridgeless pole, a bounded short-cycle transversal bounds the rank. -/
theorem exists_rank_bound_of_short_cycle_transversal (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V), N.IsBridgelessTwoPole s t →
      (1/2+ε)*(2:ℝ)^networkRank N ≤ N.numPaths s t →
      ∀ X : Finset V, X.card ≤ k →
      (∀ z : N.Word, N.IsCycleWord z → size z ≤ 4 →
        ∃ v, 0 < N.deg z v ∧ v ∈ X) →
      networkRank N < 5*C+4*k+5 := by
  obtain ⟨C,hC⟩ := PoleMarginLayers.exists_avoiding_constant ε hε
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hpaths X hX hhit
  by_contra hr
  obtain ⟨z,hz,hsize,havoid⟩ := hC k V E N s t hN hpaths X hX (by omega)
  obtain ⟨v,hv,hmem⟩ := hhit z hz hsize
  exact havoid v hv hmem

end Erdos1016.ExactMaximumSupport.Shortening.PoleGirthGap
