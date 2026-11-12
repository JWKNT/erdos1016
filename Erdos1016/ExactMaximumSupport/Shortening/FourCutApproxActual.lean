import Erdos1016.ExactMaximumSupport.Shortening.MarginGadgets
import Erdos1016.ExactMaximumSupport.Shortening.MarginDecay
import Erdos1016.ExactMaximumSupport.Shortening.FourCutApproxState
import Erdos1016.ExactMaximumSupport.GapInput
import Erdos1016.ExactMaximum.FourCutSides

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The approximate compactness state comes from actual physical four-poles. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.FourCutApproxActual
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
open FourCutArithmeticProof FourCutCompactness

/-- Uniform arbitrary-tolerance gadget laws on actual four-pole shares. -/
theorem exists_bound (η : ℝ) (hη : 0<η) :
    ∃A:ℕ,∀(V E:Type) [Fintype V] [Fintype E] (N:Network V E),
      N.IsWeakPole → ∀p:Fin 4→V,Function.Injective p → (∀i,N.IsPort (p i)) →
      A≤networkRank N → ApproxState η (pathShare N p) (pairShare N p) := by
  obtain ⟨K,hK⟩ := MarginFewCycles.exists_bound (η/4) (by positivity)
  obtain ⟨A,hA⟩ := MarginDecay.exists_scale (4*K) η hη
  refine ⟨A,?_⟩
  intro V E _ _ N hN p hp hport hrank
  have hD : (0:ℝ)<2^networkRank N := by positivity
  have hne : ∀{i j:Fin 4},i≠j → p i≠p j := fun h h' => h (hp h')
  have hscale : ((4*K:ℕ):ℝ)≤η^2*(2:ℝ)^networkRank N := hA _ hrank
  have hscale₂ : ((2*K:ℕ):ℝ)≤η^2*(2:ℝ)^networkRank N := by
    have h : (2*K:ℕ)≤4*K := by omega
    exact (by exact_mod_cast h : ((2*K:ℕ):ℝ)≤(4*K:ℕ)).trans hscale
  have hF : MarginGadgets.Bound (η/4) K := hK
  refine ⟨fourState_of_pole gapStatement N hN p hp hport, ?_, ?_, ?_⟩
  · intro i j k hij hik hjk hsum
    have hmany : (1+2*(η/4))*(2:ℝ)^networkRank N≤
        (N.numPaths (p i) (p k):ℝ)+N.numPaths (p j) (p k) := by
      unfold pathShare at hsum
      rw [←add_div,le_div_iff₀ hD] at hsum
      nlinarith
    have hh := MarginGadgets.gadget_third_pair (by positivity) hF N hN
      (hport i) (hport j) (hport k) (hne hij) (hne hik.symm) (hne hjk.symm) hmany
    exact MarginDecay.normalized_le hη.le hh hscale₂
  · intro i j k l hd hsum
    rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
    have hmany : (2+4*(η/4))*(2:ℝ)^networkRank N≤
        (N.numPaths (p i) (p k):ℝ)+N.numPaths (p j) (p k)+
          N.numPaths (p i) (p l)+N.numPaths (p j) (p l) := by
      unfold pathShare at hsum
      rw [←add_div,←add_div,←add_div,le_div_iff₀ hD] at hsum
      nlinarith
    have hh := MarginGadgets.gadget_cross_pairs (by positivity) hF N hN
      (hport i) (hport j) (hport k) (hport l) (hne hij) (hne hkl)
      (hne hik.symm) (hne hjk.symm) (hne hil.symm) (hne hjl.symm) hmany
    rw [numPathPairs_eq_pairCount N p k i j l hik.symm hjk.symm hkl hij hil hjl,
      numPathPairs_eq_pairCount N p k j i l hjk.symm hik.symm hkl hij.symm hjl hil,
      pairingOf_comm k i,
      pairingOf_opposite i l k j hil hik hij hkl.symm hjl.symm hjk.symm] at hh
    have hn := MarginDecay.normalized_le hη.le hh hscale
    simpa only [pairShare,Nat.cast_add,add_div] using hn
  · intro i j k l hd hsum
    rcases hd with ⟨hij,hik,hil,hjk,hjl,hkl⟩
    have hmany : (1+2*(η/4))*(2:ℝ)^networkRank N≤
        (N.numPaths (p i) (p j):ℝ)+N.numPathPairs (p i) (p k) (p l) (p j)+
          N.numPathPairs (p i) (p l) (p k) (p j) := by
      rw [numPathPairs_eq_pairCount N p i k l j hik hil hij hkl hjk.symm hjl.symm,
        numPathPairs_eq_pairCount N p i l k j hil hik hij hkl.symm hjl.symm hjk.symm]
      unfold pathShare pairShare at hsum
      rw [←add_div,←add_div,le_div_iff₀ hD] at hsum
      nlinarith
    have hh := MarginGadgets.gadget_opposite_pair (by positivity) hF N hN
      (hport k) (hport l) (hport i) (hport j) (hne hkl) (hne hij)
      (hne hik) (hne hil) (hne hjk) (hne hjl) hmany
    exact MarginDecay.normalized_le hη.le hh hscale₂

end Erdos1016.ExactMaximumSupport.Shortening.FourCutApproxActual
