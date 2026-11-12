import Erdos1016.ExactMaximumSupport.FourPoleCapGeometry
import Erdos1016.ExactMaximumSupport.FullPairCappedLadder

set_option autoImplicit false

/-!
# The concrete capped model of a full-cross four-pole

The positive-degree normalization removes only isolated ambient vertices.
The actual double-cap network is a cap-preserving mixed ladder.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleCaps
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A bridgeless full-cross four-pole has the actual cap-preserving ladder model. -/
theorem exists_capped_ladder (a b c d : V) (hN : N.IsWeakPole) (hbl : N.IsBridgeless)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : N.IsPort a) (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d)
    (honly : ∀v,N.IsPort v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (hfac : N.IsFullPair a c) (hfbc : N.IsFullPair b c)
    (hfad : N.IsFullPair a d) (hfbd : N.IsFullPair b d) :
    ∃ k : ℕ,∃ T : Fin (k+1) → Kind,
      ∃ I : NetworkIso (MixedTiles.capped T) (ThirdPortMarkedCore.positive (capped N a b c d)),
        (I.vertices (Sum.inr false)).val=left ∧
        (I.vertices (Sum.inr true)).val=right ∧ weight T=networkRank N+1 := by
  classical
  have hpole := weak_two_pole N a b c d hN hab hac had hbc hbd hcd ha hb hc hd honly
  have hbridge := capped_bridgeless N a b c d hN hbl hab hac had hbc hbd hcd ha hb hc hd
  obtain ⟨hfull,hr⟩ := full_and_rank N a b c d hfac hfbc hfad hfbd
  obtain ⟨hs,ht,hcore,hfcore,hrcore,_,_⟩ :=
    ThirdPortMarkedCore.connected_full_two_pole (capped N a b c d) left right hpole hbridge hfull
  obtain ⟨k,T,I,hleft,hright,hweight⟩ :=
    FullPairCappedLadder.exists_capped_ladder
      (ThirdPortMarkedCore.positive (capped N a b c d)) hcore hfcore (by omega)
  refine ⟨k,T,I,?_,?_,?_⟩
  · exact congrArg Subtype.val hleft
  · exact congrArg Subtype.val hright
  · omega

end Erdos1016.ExactMaximumSupport.FourPoleCaps
