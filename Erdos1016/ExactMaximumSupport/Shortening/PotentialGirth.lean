import Erdos1016.ExactMaximumSupport.Shortening.OneMarkSuppression
import Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalPotential

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! The bounded-port theorem from one mark per suppression and an additive bridge potential. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PotentialGirth
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- At fixed margin and fixed port bound, girth-five poles cannot have rich
tested paths at arbitrarily large rank. Bridges and isolated vertices are allowed. -/
theorem exists_bound (m g : ℕ) :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      N.IsWeakPole → Nat.card {v : V // N.IsPort v}≤g+2 → B≤networkRank N →
      (∀z : N.Word,N.IsCycleWord z → 5≤size z) →
      ∀s t : V,N.IsPort s → N.IsPort t → s≠t →
        2^(m+1)*N.numPaths s t < (2^m+2)*2^networkRank N := by
  obtain ⟨C,hC⟩ := PoleTransversalPotential.exists_constant m
  refine ⟨(g+15)*(5*C+4*g+4)+1,?_⟩
  intro V E _ _ N hN hports hr hgirth s t hs ht hst
  apply Nat.lt_of_not_le
  intro hrich
  have hhalf := CyclicShoreMargin.strict_half m _ _ hrich
  obtain ⟨E',iE',M,Y,hM,hMr,hMp,hY,hHit⟩ :=
    OneMarkSuppression.exists_two_pole N g s t hN hs ht hst hports hhalf hgirth
  letI := iE'
  have hrichM : (2^m+2)*2^networkRank M≤2^(m+1)*M.numPaths s t := by
    rw [hMr,hMp]
    exact hrich
  have hb := hC g V E' M s t hM hrichM Y hY hHit
  have hle := Nat.mul_le_mul_right (5*C+4*g+4) (Nat.add_le_add_right hY 15)
  rw [hMr] at hb
  omega

end Erdos1016.ExactMaximumSupport.Shortening.PotentialGirth
