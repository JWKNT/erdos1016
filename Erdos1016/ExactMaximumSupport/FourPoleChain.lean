import Erdos1016.ExactMaximumSupport.FourPoleCappedLadder
import Erdos1016.ExactMaximumSupport.MixedTilesUncap
import Erdos1016.ExactMaximumSupport.FourFullBridge

set_option autoImplicit false

/-! # A full-cross four-pole is a physical tile chain or has a cyclic bridge -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleChain
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The physical chain model includes both unordered port pairs and the exact tile weight. -/
def IsChain (a b c d : V) : Prop :=
  ∃ k : ℕ,∃ T : Fin (k+1) → Kind,∃ J : NetworkIso (chain T) (ThirdPortMarkedCore.positive N),
    (((J.vertices (left T 0 false)).val=a ∧ (J.vertices (left T 0 true)).val=b) ∨
      ((J.vertices (left T 0 false)).val=b ∧ (J.vertices (left T 0 true)).val=a)) ∧
    (((J.vertices (right T (Fin.last k) false)).val=c ∧
      (J.vertices (right T (Fin.last k) true)).val=d) ∨
      ((J.vertices (right T (Fin.last k) false)).val=d ∧
      (J.vertices (right T (Fin.last k) true)).val=c)) ∧ weight T=networkRank N+1

/-- A bridgeless four-pole with all four full cross pairs is an actual physical tile chain. -/
theorem isChain (a b c d : V) (hN : N.IsWeakPole) (hbl : N.IsBridgeless)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : N.IsPort a) (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d)
    (honly : ∀v,N.IsPort v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (hfac : N.IsFullPair a c) (hfbc : N.IsFullPair b c)
    (hfad : N.IsFullPair a d) (hfbd : N.IsFullPair b d) : IsChain N a b c d := by
  classical
  obtain ⟨k,T,I,hl,hr,hweight⟩ := FourPoleCaps.exists_capped_ladder N a b c d hN hbl
    hab hac had hbc hbd hcd ha hb hc hd honly hfac hfbc hfad hfbd
  have ha' : 0<N.deg (fun _ => 1) a := by rw [ha]; decide
  have hb' : 0<N.deg (fun _ => 1) b := by rw [hb]; decide
  have hc' : 0<N.deg (fun _ => 1) c := by rw [hc]; decide
  have hd' : 0<N.deg (fun _ => 1) d := by rw [hd]; decide
  refine ⟨k,T,MixedTilesUncap.uncap T N a b c d I hl hr ha' hb' hc' hd',?_,?_,hweight⟩
  · exact MixedTilesUncap.uncap_left_pair T N a b c d I hl hr ha' hb' hc' hd'
  · exact MixedTilesUncap.uncap_right_pair T N a b c d I hl hr ha' hb' hc' hd'

/-- The complete four-pole alternative retains both actual cycles in the bridge case. -/
theorem chain_or_cyclic_bridge (a b c d : V) (hN : N.IsWeakPole)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (ha : N.IsPort a) (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d)
    (honly : ∀v,N.IsPort v → v=a ∨ v=b ∨ v=c ∨ v=d)
    (hfac : N.IsFullPair a c) (hfbc : N.IsFullPair b c)
    (hfad : N.IsFullPair a d) (hfbd : N.IsFullPair b d) :
    IsChain N a b c d ∨ ∃ (S : V → Prop) (e : E),
      N.IsCyclicCut S ∧ N.cutSize S=1 ∧ S a ∧ S b ∧ ¬S c ∧ ¬S d ∧
      (∀g,N.crosses S g → g=e) := by
  rcases FourFullBridge.bridgeless_or_cyclic_bridge N hN ha hc hfac hfbc hfad with hb' | hcut
  · exact Or.inl (isChain N a b c d hN hb' hab hac had hbc hbd hcd ha hb hc hd honly
      hfac hfbc hfad hfbd)
  · exact Or.inr hcut

end Erdos1016.ExactMaximumSupport.FourPoleChain
