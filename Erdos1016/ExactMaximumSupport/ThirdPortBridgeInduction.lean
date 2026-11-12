import Erdos1016.ExactMaximumSupport.ThirdPortBridges
import Erdos1016.ExactMaximumSupport.PoleGapInduction

set_option autoImplicit false

/-!
# The third-port statement reduces to one bridgeless component

This is an actual-network reduction. The bridge step retains the original
third vertex and multiplies both tested path counts by the same full factor.
Only the bridgeless three-pole statement is left as an explicit premise.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- The remaining third-port input, allowing isolated vertices but no bridges. -/
def BridgelessThirdPortStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
    N.IsWeakPole → N.IsBridgeless →
    ∀ s t v : V, N.IsPort s → N.IsPort t → N.IsPort v → s ≠ t → s ≠ v → t ≠ v →
    (∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v) → N.IsFullPair s t →
    N.IsFullPair v t ∨ 8 * N.numPaths v t ≤ 7 * 2 ^ networkRank N

/-- All bridge positions are discharged, with the original third port retained. -/
theorem thirdPortStatement_of_bridgeless (h : BridgelessThirdPortStatement) :
    PoleGapInduction.ThirdPortStatement := by
  classical
  have key : ∀ r : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      networkRank N = r → N.IsWeakPole →
      ∀ s t v : V, N.IsPort s → N.IsPort t → N.IsPort v → s ≠ t → s ≠ v → t ≠ v →
      (∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v) → N.IsFullPair s t →
      N.IsFullPair v t ∨ 8 * N.numPaths v t ≤ 7 * 2 ^ networkRank N := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro V E _ _ N hr hN s t v hs ht hv hst hsv htv honly hfull
      by_cases hbl : N.IsBridgeless
      · exact h V E N hN hbl s t v hs ht hv hst hsv htv honly hfull
      obtain ⟨e,he⟩ : ∃ e, ∀ z : N.Word, N.IsCycleWord z → z e = 0 := by
        unfold IsBridgeless at hbl
        obtain ⟨e,he⟩ := not_forall.mp hbl
        exact ⟨e,fun z hz => Classical.not_not.mp fun hn => he ⟨z,hz,hn⟩⟩
      rcases ThirdPortBridges.bridge_step_or_half N s t v hN hs ht hv honly hfull he
        with hhalf | ⟨S,x,y,step⟩
      · right
        omega
      have hlt : networkRank (N.sub (N.inside S)) < r := by
        have hsum := step.rank_eq
        have hpos := step.right_rank_pos
        omega
      have hind := ih _ hlt V _ (N.sub (N.inside S)) rfl step.left_pole s x v
        step.left_port_s step.left_port_x step.left_port_v step.sx_ne hsv step.xv_ne
        step.left_only step.left_full
      have hright : (N.sub (N.outside S)).numPaths y t =
          2 ^ networkRank (N.sub (N.outside S)) := step.right_full
      rcases hind with hleft | hleft
      · left
        change N.numPaths v t = 2 ^ networkRank N
        have hleft' : (N.sub (N.inside S)).numPaths v x =
            2 ^ networkRank (N.sub (N.inside S)) := hleft
        rw [step.paths_vt,hleft',hright,step.rank_eq,pow_add]
      · right
        have hh := Nat.mul_le_mul_right (2 ^ networkRank (N.sub (N.outside S))) hleft
        rw [step.paths_vt,hright,step.rank_eq,pow_add]
        simpa only [Nat.mul_assoc] using hh
  intro V E _ _ N hN s t v hs ht hv hst hsv htv honly hfull
  exact key (networkRank N) V E N rfl hN s t v hs ht hv hst hsv htv honly hfull

end Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction
