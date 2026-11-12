import Erdos1016.ExactMaximumSupport.Shortening.TreeCapShares

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The physical tree-cap bound with an arbitrary positive error. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.TreeCapMargin
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
open ExactMaximum FourCutArithmeticProof

theorem exists_dyadic_bound (m : ℕ) :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      B≤networkRank N → ∀ a b c d : V,
      2^(m+1)*TreeCapCycleBound.load N a b c d≤
        8*(2^m+1)*2^networkRank N := by
  obtain ⟨B,hB⟩ := ExactMaximum.numCycles_le_of_large_rank_margin m
  refine ⟨B,?_⟩
  intro V E _ _ N hr a b c d
  have hrank := TreeCapCycleBound.rank_bounds N a b c d
  have hc := hB _ _ (TreeCapCycleBound.closed N a b c d) (hr.trans hrank.1)
  have hload := TreeCapCycleBound.load_le_cycles N a b c d
  have hpow : 2^networkRank (TreeCapCycleBound.closed N a b c d)≤8*2^networkRank N := by
    have hp := Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) hrank.2
    simpa only [pow_add,show (2 : ℕ)^3=8 by norm_num,mul_comm] using hp
  exact (Nat.mul_le_mul_left _ hload).trans
    (hc.trans (by nlinarith [Nat.mul_le_mul_left (2^m+1) hpow]))

/-- All three actual normalized cap loads converge uniformly to at most four. -/
theorem exists_bound (η : ℝ) (hη : 0<η) :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      B≤networkRank N → ∀ (p : Fin 4 → V) (α : Fin 3),
      (N.numCycles:ℝ)/(2:ℝ)^networkRank N + pathSum (pathShare N p) +
        forestSum (pairShare N p) - pairShare N p α ≤ 4+η := by
  obtain ⟨m,hm⟩ := exists_nat_gt (4/η)
  have hpowm : (m:ℝ)<(2:ℝ)^m := by exact_mod_cast Nat.lt_two_pow_self (n:=m)
  have hsmall : (4:ℝ)≤η*(2:ℝ)^m := by
    have hm' : (4:ℝ)/η<(2:ℝ)^m := hm.trans hpowm
    have hh := (div_lt_iff₀ hη).mp hm'
    nlinarith
  obtain ⟨B,hB⟩ := exists_dyadic_bound m
  refine ⟨B,?_⟩
  intro V E _ _ N hr p α
  rw [TreeCapShares.normalized_load]
  have hD : (0:ℝ)<(2:ℝ)^networkRank N := by positivity
  apply (div_le_iff₀ hD).mpr
  have hc := hB V E N hr (p (TreeCapShares.capOrder α 0))
    (p (TreeCapShares.capOrder α 1)) (p (TreeCapShares.capOrder α 2))
    (p (TreeCapShares.capOrder α 3))
  have hcR : (2:ℝ)^(m+1)*(TreeCapCycleBound.load N
      (p (TreeCapShares.capOrder α 0)) (p (TreeCapShares.capOrder α 1))
      (p (TreeCapShares.capOrder α 2)) (p (TreeCapShares.capOrder α 3)):ℝ)≤
      8*((2:ℝ)^m+1)*(2:ℝ)^networkRank N := by exact_mod_cast hc
  rw [pow_succ] at hcR
  have hp : (0:ℝ)<(2:ℝ)^m := by positivity
  have hs := mul_le_mul_of_nonneg_right hsmall hD.le
  nlinarith

end Erdos1016.ExactMaximumSupport.Shortening.TreeCapMargin
