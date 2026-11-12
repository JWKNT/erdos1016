import Erdos1016.ExactMaximumSupport.PoleGapReduction
import Erdos1016.ExactMaximumSupport.PoleTerminalDeletion
import Erdos1016.ExactMaximumSupport.PoleAdjacentGap
import Erdos1016.ExactMaximumSupport.PoleSmallRank
import Erdos1016.ExactMaximumSupport.ThirdPortArithmetic

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The gap theorem from the third-port theorem

Rank induction uses the exact terminal-deletion count.
Port suppression, bridge decomposition, rank one, and adjacent ports are discharged.
The third-port theorem remains an explicit structural hypothesis.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleGapInduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- The paper's third-port lemma, permitting isolated vertices in its pole model. -/
def ThirdPortStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), N.IsWeakPole →
    ∀ s t v : V, N.IsPort s → N.IsPort t → N.IsPort v → s ≠ t → s ≠ v → t ≠ v →
    (∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v) → N.IsFullPair s t →
    N.IsFullPair v t ∨ 8 * N.numPaths v t ≤ 7 * 2 ^ networkRank N

/-- The complete rank induction leaves only the actual third-port theorem as a premise. -/
theorem gapStatement_of_thirdPort (h3 : ThirdPortStatement) : ExactMaximum.GapStatement := by
  classical
  have hall : ∀ r : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      N.IsWeakPole → ∀ s t : V, N.IsPort s → N.IsPort t → s ≠ t → networkRank N ≤ r →
      N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro V E _ _ N hN s t hs ht hst hrank
      apply PoleGapReduction.gap_of_rank_bound r ?_ V E N hN s t hs ht hst hrank
      intro V' E' _ _ M a b hM hbound
      by_cases hone : networkRank M = 1
      · exact Or.inl (PoleSmallRank.full_of_rank_one M a b hM hone)
      have hpos := PoleSmallRank.rank_pos M a b hM
      have htwo : 2 ≤ networkRank M := by omega
      by_cases hadj : M.graph.Adj a b
      · right
        have hh := PoleAdjacentGap.adjacent_port_quarter M a b hM hadj htwo
        omega
      obtain ⟨e,f,x,y,T,hxb,hyb,hK,hports,hzero,hr,hpaths⟩ :=
        PoleTerminalDeletion.exists_three_pole_deletion M a b hM hadj
      let K := PoleTerminalDeletion.deleted M a
      have hkx : K.IsPort x := (hports x).mpr (Or.inl rfl)
      have hky : K.IsPort y := (hports y).mpr (Or.inr (Or.inl rfl))
      have hkb : K.IsPort b := (hports b).mpr (Or.inr (Or.inr rfl))
      have hlt : networkRank K < r := by dsimp only [K]; omega
      have hx := ih (networkRank K) hlt _ _ K hK x b hkx hkb hxb le_rfl
      have hy := ih (networkRank K) hlt _ _ K hK y b hky hkb hyb le_rfl
      have hxy : K.numPaths x b = 2^networkRank K →
          K.numPaths y b = 2^networkRank K ∨ 8*K.numPaths y b ≤ 7*2^networkRank K := by
        intro hxfull
        apply h3 _ _ K hK x b y hkx hkb hky hxb T.huw hyb.symm
        · intro z hz
          rcases (hports z).mp hz with hz | hz | hz
          · exact Or.inl hz
          · exact Or.inr (Or.inr hz)
          · exact Or.inr (Or.inl hz)
        · exact hxfull
      have hyx : K.numPaths y b = 2^networkRank K →
          K.numPaths x b = 2^networkRank K ∨ 8*K.numPaths x b ≤ 7*2^networkRank K := by
        intro hyfull
        apply h3 _ _ K hK y b x hky hkb hkx hyb T.huw.symm hxb.symm
        · intro z hz
          rcases (hports z).mp hz with hz | hz | hz
          · exact Or.inr (Or.inr hz)
          · exact Or.inl hz
          · exact Or.inr (Or.inl hz)
        · exact hyfull
      have hh := ThirdPortArithmetic.sum_gap _ _ _ hx hy hxy hyx
      have hp : 2^networkRank M = 2*2^networkRank K := by
        rw [← hr,pow_succ]
        change 2^networkRank K*2 = 2*2^networkRank K
        ring
      rw [hpaths,hp]
      exact hh
  intro V E _ _ N hN s t hs ht hst
  exact hall (networkRank N) V E N hN s t hs ht hst le_rfl

end Erdos1016.ExactMaximumSupport.PoleGapInduction
