import Erdos1016.ExactMaximumSupport.FullPairLadderIso
import Erdos1016.ExactMaximumSupport.LadderTileIso
import Erdos1016.ExactMaximumSupport.NetworkIsoComposition
import Erdos1016.ExactMaximumSupport.PoleSmallRank

set_option autoImplicit false

/-!
# Every full bridgeless two-pole is a capped ladder or the rank-one pole

The isomorphism is constructed from the actual paths, matching permutation,
and canonical tile blocks. No graph decomposition is supplied as a premise.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairCappedLadder
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Above rank one, an actual full two-pole is a concrete cap-preserving mixed ladder. -/
theorem exists_capped_ladder {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) (hr : 2 ≤ networkRank N) :
    ∃ k : ℕ, ∃ T : Fin (k+1) → Kind, ∃ R : NetworkIso (capped T) N,
      R.vertices (Sum.inr false)=s ∧ R.vertices (Sum.inr true)=t ∧
      weight T+1=networkRank N := by
  obtain ⟨n,π,I,hπ,hs,ht,hn⟩ := FullPairLadderIso.exists_ladder_iso N hN hfull
  obtain ⟨k,T,J,hW,hleft,hright⟩ := LadderTileIso.exists_capped_iso π hπ (by omega)
  refine ⟨k,T,J.trans I,?_,?_,?_⟩
  · rw [NetworkIso.trans_vertices,hleft,hs]
  · rw [NetworkIso.trans_vertices,hright,ht]
  · omega

/-- Every actual full bridgeless two-pole has rank one or is the concrete capped model. -/
theorem rank_one_or_capped {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) :
    networkRank N=1 ∨
      ∃ k : ℕ, ∃ T : Fin (k+1) → Kind, ∃ R : NetworkIso (capped T) N,
        R.vertices (Sum.inr false)=s ∧ R.vertices (Sum.inr true)=t ∧
        weight T+1=networkRank N := by
  by_cases hr : networkRank N=1
  · exact Or.inl hr
  · right
    have hp := PoleSmallRank.rank_pos N s t hN
    exact exists_capped_ladder N hN hfull (by omega)

end Erdos1016.ExactMaximumSupport.FullPairCappedLadder
