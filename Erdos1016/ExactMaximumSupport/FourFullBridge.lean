import Erdos1016.ExactMaximumSupport.ThirdPortBridges

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The bridge alternative for full cross pairs

Actual full pairs force the two port groups onto opposite bridge shores.
The existing minimum-degree bridge ledger makes both shores cyclic.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourFullBridge
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A physical bridge separates the prescribed port groups and leaves cycles on both shores. -/
theorem bridge_cut {a b c d : V} (hN : N.IsWeakPole)
    (ha : N.IsPort a) (hc : N.IsPort c)
    (hac : N.IsFullPair a c) (hbc : N.IsFullPair b c) (had : N.IsFullPair a d)
    (e : E) (hbr : ∀ z : N.Word,N.IsCycleWord z → z e=0) :
    ∃ S : V → Prop, N.IsCyclicCut S ∧ N.cutSize S=1 ∧
      S a ∧ S b ∧ ¬S c ∧ ¬S d ∧
      (∀ g,N.crosses S g → g=e) := by
  classical
  have hpow : 0<2^networkRank N := Nat.two_pow_pos _
  have hmany : 2^networkRank N<2*N.numPaths a c := by
    rw [show N.numPaths a c=2^networkRank N from hac]
    omega
  obtain ⟨S,x,y,he,hx,hy,hcut,hSa,hSc,_,_,_,_⟩ :=
    ThirdPortBridges.bridge_cut N hN ha hc hmany hbr
  have hcut' : ∀ g,N.crosses (fun v => ¬S v) g → g=e :=
    fun g hg => hcut g ((N.crosses_not_iff S g).mp hg)
  have hSb : S b := by
    by_contra hb
    have hh := N.two_mul_numPaths_le_of_same_side hN.deg_zero_or_two_le
      (fun v => ¬S v) he.symm hy (not_not.mpr hx) hcut' hb hSc
    rw [show N.numPaths b c=2^networkRank N from hbc] at hh
    omega
  have hSd : ¬S d := by
    intro hd
    have hh := N.two_mul_numPaths_le_of_same_side hN.deg_zero_or_two_le
      S he hx hy hcut hSa hd
    rw [show N.numPaths a d=2^networkRank N from had] at hh
    omega
  have hleft := N.rank_side_pos_of_one_crossing hN.deg_zero_or_two_le S he hx hy hcut
  have hright := N.rank_side_pos_of_one_crossing hN.deg_zero_or_two_le
    (fun v => ¬S v) he.symm hy (not_not.mpr hx) hcut'
  have hcyclic : N.IsCyclicCut S :=
    ⟨(N.sub (N.inside S)).numCycles_pos_of_rank_pos hleft,
      (N.sub (N.outside S)).numCycles_pos_of_rank_pos hright⟩
  have hsize : N.cutSize S=1 := Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun f g => Subtype.ext ((hcut f.1 f.2).trans (hcut g.1 g.2).symm)⟩,
      ⟨⟨e,N.crosses_of_joins he hx hy⟩⟩⟩
  exact ⟨S,hcyclic,hsize,hSa,hSb,hSc,hSd,hcut⟩

/-- The original pole is bridgeless, or it has the exact cyclic bridge alternative. -/
theorem bridgeless_or_cyclic_bridge {a b c d : V} (hN : N.IsWeakPole)
    (ha : N.IsPort a) (hc : N.IsPort c)
    (hac : N.IsFullPair a c) (hbc : N.IsFullPair b c) (had : N.IsFullPair a d) :
    N.IsBridgeless ∨ ∃ (S : V → Prop) (e : E),
      N.IsCyclicCut S ∧ N.cutSize S=1 ∧ S a ∧ S b ∧ ¬S c ∧ ¬S d ∧
      (∀ g,N.crosses S g → g=e) := by
  classical
  by_cases h : N.IsBridgeless
  · exact Or.inl h
  · right
    obtain ⟨e,he⟩ := not_forall.mp h
    have hbr : ∀ z : N.Word,N.IsCycleWord z → z e=0 := by
      intro z hz
      by_contra hez
      exact he ⟨z,hz,hez⟩
    obtain ⟨S,hS⟩ := bridge_cut N hN ha hc hac hbc had e hbr
    exact ⟨S,e,hS⟩

end Erdos1016.ExactMaximumSupport.FourFullBridge
