import Erdos1016.ExactMaximumSupport.PoleExtendedShoreBase
import Erdos1016.ExactMaximumSupport.PoleExtendedShoreLift
import Erdos1016.ExactMaximumSupport.PoleMarginBridge

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Marked cyclic shores through all bridges

The two bridge-side ranks are positive and add to the original rank.
One side retains enough rank for its own marked vertices.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleExtendedShore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance extendedInductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The extended-shore bound holds for every weak two-pole, including all bridge configurations. -/
theorem extended_constant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → 1≤networkRank N →
      X.card*(5*C+4*k+13)≤networkRank N →
      ∃ S : V → Prop,ExtendedShore N s t X S := by
  obtain ⟨C,hC⟩ := bridgeless_constant m
  refine ⟨C,?_⟩
  intro k
  have key : ∀r : ℕ,∀ (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),networkRank N=r → N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → 1≤networkRank N →
      X.card*(5*C+4*k+13)≤networkRank N →
      ∃ S : V → Prop,ExtendedShore N s t X S := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro V E _ _ N s t hr hN hrich X hX hpos hbudget
      by_cases hbl : N.IsBridgeless
      · exact hC k V E N s t hN hbl hrich X hX hpos hbudget
      obtain ⟨e,he⟩ : ∃e,∀z,N.IsCycleWord z → z e=0 := by
        obtain ⟨e,he⟩ := not_forall.mp hbl
        exact ⟨e,fun z hz => Classical.not_not.mp (fun hn => he ⟨z,hz,hn⟩)⟩
      obtain ⟨S,x,y,sp⟩ := PoleMarginBridge.exists_split N m hN hrich he
      let X₁ := X.filter fun v => 0<(N.sub (N.inside S)).deg (fun _ => 1) v
      let X₂ := X.filter fun v => 0<(N.sub (N.outside S)).deg (fun _ => 1) v
      have hX₁ : X₁.card≤k := (Finset.card_filter_le _ _).trans hX
      have hX₂ : X₂.card≤k := (Finset.card_filter_le _ _).trans hX
      have hin (v : V) (hv : 0<(N.sub (N.inside S)).deg (fun _ => 1) v) : S v := by
        by_contra hn
        rw [N.deg_inside_of_not_mem S hn] at hv
        omega
      have hout (v : V) (hv : 0<(N.sub (N.outside S)).deg (fun _ => 1) v) : ¬S v := by
        intro hn
        rw [N.deg_sub_ones,N.deg_outside_eq_zero S hn] at hv
        omega
      have hdisj : Disjoint X₁ X₂ := by
        apply Finset.disjoint_left.mpr
        intro v hv₁ hv₂
        exact hout v (Finset.mem_filter.mp hv₂).2 (hin v (Finset.mem_filter.mp hv₁).2)
      have hcard : X₁.card+X₂.card≤X.card := by
        rw [←Finset.card_union_of_disjoint hdisj]
        apply Finset.card_le_card
        exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hchoose : X₁.card*(5*C+4*k+13)≤networkRank (N.sub (N.inside S)) ∨
          X₂.card*(5*C+4*k+13)≤networkRank (N.sub (N.outside S)) := by
        have hh := Nat.mul_le_mul_right (5*C+4*k+13) hcard
        rw [Nat.add_mul] at hh
        have hs := sp.rank_eq
        omega
      have hlcyc := (N.sub (N.inside S)).numCycles_pos_of_rank_pos sp.left_rank_pos
      have hrcyc := (N.sub (N.outside S)).numCycles_pos_of_rank_pos sp.right_rank_pos
      rcases hchoose with hl | hright
      · have hlt : networkRank (N.sub (N.inside S))<r := by
          have hsum := sp.rank_eq
          have hpositive := sp.right_rank_pos
          omega
        obtain ⟨U,hU⟩ := ih _ hlt V _ (N.sub (N.inside S)) s x rfl sp.left_pole
          sp.left_rich X₁ hX₁ sp.left_rank_pos hl
        exact ⟨U,lift_left N S U X sp.joins sp.mem_x sp.not_mem_y sp.only_cross
          sp.not_mem_t hrcyc hU⟩
      · have hlt : networkRank (N.sub (N.outside S))<r := by
          have hsum := sp.rank_eq
          have hpositive := sp.left_rank_pos
          omega
        obtain ⟨U,hU⟩ := ih _ hlt V _ (N.sub (N.outside S)) y t rfl sp.right_pole
          sp.right_rich X₂ hX₂ sp.right_rank_pos hright
        have hC' : ∀g,N.crosses (fun v => ¬S v) g → g=e :=
          fun g hg => sp.only_cross g ((N.crosses_not_iff S g).mp hg)
        have hother : 0<(N.sub (N.outside fun v => ¬S v)).numCycles := by
          apply cycle_pos_mono N (N.inside S) (N.outside fun v => ¬S v) _ hlcyc
          intro g hg
          exact ⟨not_not.mpr hg.1,not_not.mpr hg.2⟩
        have hlift := lift_left N (fun v => ¬S v) U X sp.joins.symm sp.not_mem_y
          (not_not.mpr sp.mem_x) hC' (not_not.mpr sp.mem_s) hother
          (ExtendedShore.symm (N.sub (N.outside S)) hU)
        exact ⟨U,ExtendedShore.symm N hlift⟩
  intro V E _ _ N s t hN hrich X hX hpos hbudget
  exact key (networkRank N) V E N s t rfl hN hrich X hX hpos hbudget

/-- With both ports marked, every sufficiently large rich weak two-pole has a cubic cyclic shore. -/
theorem marked_two_pole_constant (m k : ℕ) :
    ∃ B : ℕ,∀ (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → s∈X → t∈X → B≤networkRank N →
      ∃ S : V → Prop,N.IsCyclicCut S ∧ N.cutSize S≤4 ∧
        (∀v,S v → N.deg (fun _ => 1) v=3) ∧ ∀v,S v → v∉X := by
  obtain ⟨C,hC⟩ := extended_constant m
  refine ⟨k*(5*C+4*k+13)+1,?_⟩
  intro V E _ _ N s t hN hrich X hX hs ht hr
  have hb : X.card*(5*C+4*k+13)≤networkRank N := by
    have hh := Nat.mul_le_mul_right (5*C+4*k+13) hX
    omega
  obtain ⟨S,hS⟩ := hC k V E N s t hN hrich X hX (by omega) hb
  have hh := hS.cubic N hN hs ht
  exact ⟨S,hh.1,hh.2.1,hh.2.2,hS.avoid⟩

end Erdos1016.ExactMaximumSupport.PoleExtendedShore
