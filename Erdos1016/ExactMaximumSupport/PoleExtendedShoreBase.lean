import Erdos1016.ExactMaximumSupport.PoleExtendedShore
import Erdos1016.ExactMaximumSupport.NetworkInducedCut
import Erdos1016.ExactMaximumSupport.CyclicShoreMargin

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The bridgeless base for marked cyclic shores

The connected theorem applies after deleting only isolated vertices.
Its shore lifts to the original physical network and avoids every marked vertex.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleExtendedShore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance extendedBaseDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The short-cycle shore theorem also holds for weak poles with isolated vertices. -/
theorem weak_bridgeless_constant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t → N.IsBridgeless →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → 5*C+4*k+13≤networkRank N →
      ∃ S : V → Prop,N.IsCyclicCut S ∧ N.cutSize S≤4 ∧
        ∀v,S v → N.deg (fun _ => 1) v=3 ∧ v∉X := by
  have hε : 0<1/(2:ℝ)^m := by positivity
  obtain ⟨C,hC⟩ := PoleCyclicShore.exists_avoiding_constant (1/(2:ℝ)^m) hε
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hbl hrich X hX hrank
  obtain ⟨hs,ht,hpole,_,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
  let P := fun v => 0<N.deg (fun _ => 1) v
  let M := N.induce P
  let Y := X.subtype P
  have hY : Y.card≤k := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans hX
  have hrich' : (1/2+1/(2:ℝ)^m)*(2:ℝ)^networkRank M≤M.numPaths ⟨s,hs⟩ ⟨t,ht⟩ := by
    rw [hp,hr]
    exact CyclicShoreMargin.real_margin m _ _ hrich
  have hrank' : 5*C+4*k+13≤networkRank M := by rw [hr]; exact hrank
  obtain ⟨z,_,_,hcyc,hcut,hdeg⟩ := hC k _ _ M ⟨s,hs⟩ ⟨t,ht⟩ hpole hrich' Y hY hrank'
  let S := fun v => 0<M.deg z v
  have hall : ∀e,N.inside P e := fun e =>
    ⟨N.deg_src_pos (x := fun _ => 1) (e := e) one_ne_zero,
      N.deg_dst_pos (x := fun _ => 1) (e := e) one_ne_zero⟩
  refine ⟨NetworkInducedCut.liftSet P S,NetworkInducedCut.cyclic_lift N P S hcyc,?_,?_⟩
  · rw [NetworkInducedCut.cutSize_lift N P S hall]
    exact hcut
  · intro v hv
    obtain ⟨hvP,hvS⟩ := hv
    have hh := hdeg ⟨v,hvP⟩ hvS
    refine ⟨?_,?_⟩
    · rw [←NetworkInducedCut.deg_lift N P hall ⟨v,hvP⟩]
      exact hh.1
    · intro hmem
      exact hh.2 (Finset.mem_subtype.mpr hmem)

/-- Rank proportional to the marked set suffices in the bridgeless base. -/
theorem bridgeless_constant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t → N.IsBridgeless →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → 1≤networkRank N →
      X.card*(5*C+4*k+13)≤networkRank N →
      ∃ S : V → Prop,ExtendedShore N s t X S := by
  obtain ⟨C,hC⟩ := weak_bridgeless_constant m
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hbl hrich X hX hpos hrank
  by_cases hnone : ∀v,v∈X → N.deg (fun _ => 1) v=0
  · exact ⟨_,whole_positive N hN hpos X hnone⟩
  · have hcard : 1≤X.card := by
      apply Finset.card_pos.mpr
      by_contra hn
      apply hnone
      intro v hv
      exact (hn ⟨v,hv⟩).elim
    have hlarge : 5*C+4*k+13≤networkRank N := by nlinarith
    obtain ⟨S,hcyc,hcut,hdeg⟩ := hC k V E N s t hN hbl hrich X hX hlarge
    have hns : ¬S s := by
      intro hs
      have hd := (hdeg s hs).1
      have hp : N.deg (fun _ => 1) s=2 := hN.port_s
      omega
    have hnt : ¬S t := by
      intro ht
      have hd := (hdeg t ht).1
      have hp : N.deg (fun _ => 1) t=2 := hN.port_t
      omega
    refine ⟨S,⟨?_,fun v hv => (hdeg v hv).2,hcyc.1,?_,Or.inl hcyc.2⟩⟩
    · intro v hv
      rw [(hdeg v hv).1]
      norm_num
    · simpa only [if_neg hns,if_neg hnt,Nat.add_zero] using hcut

end Erdos1016.ExactMaximumSupport.PoleExtendedShore
