import Erdos1016.ExactMaximumSupport.Shortening.TransversalTransport
import Erdos1016.ExactMaximumSupport.Shortening.FullPairShortCycle
import Erdos1016.ExactMaximumSupport.Shortening.PoleGirthGap
import Erdos1016.ExactMaximumSupport.PoleMarginBridge
import Erdos1016.ExactMaximumSupport.GapInput

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! # Rank of a rich weak two-pole with a bounded short-cycle transversal

The proof splits actual physical bridges. The additive rank and multiplicative
path ledgers retain a count of nonfull factors, without assuming a block family.
Isolated ambient vertices are handled by the actual positive-support network.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalRank
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ShortCycleTransversal

local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The eleventh deficient factor already loses more than half the capacity. -/
theorem eleven_gap (q : ℕ) (hq : 11≤q) : 2*15^q<16^q := by
  induction q,hq using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ,pow_succ]
    have hp : 0<(16 : ℕ)^n := Nat.pow_pos (by decide)
    nlinarith

/-- The actual path product invariant permits at most ten nonfull factors. -/
theorem factor_count_le_ten (q r P : ℕ) (hrich : 2^r<2*P)
    (hproduct : 16^q*P≤15^q*2^r) : q≤10 := by
  by_contra hq
  have hgap := eleven_gap q (by omega)
  have hP : 0<P := by have := Nat.two_pow_pos r; omega
  have h15 : 0<(15 : ℕ)^q := Nat.pow_pos (by decide)
  have hmul := Nat.mul_lt_mul_of_pos_left hrich h15
  have hlt : 16^q*P<(2*15^q)*P := by nlinarith
  have hh := (Nat.mul_lt_mul_right hP).mp hlt
  omega

variable {V E : Type} [Fintype V] [Fintype E]

/-- A full bridgeless weak pole still has a short cycle after its isolated vertices are removed. -/
theorem not_full_of_empty_hits (N : Network V E) (s t : V)
    (hN : N.IsWeakTwoPole s t) (hbl : N.IsBridgeless) (hX : Hits N ∅) :
    ¬N.IsFullPair s t := by
  intro hfull
  obtain ⟨hs,ht,hpole,_,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
  let Q := fun v => 0<N.deg (fun _ => 1) v
  let M := N.induce Q
  have hfull' : M.IsFullPair ⟨s,hs⟩ ⟨t,ht⟩ := by
    change M.numPaths ⟨s,hs⟩ ⟨t,ht⟩=2^networkRank M
    rw [hp,hr]
    exact hfull
  obtain ⟨z,hz,hsize⟩ := FullPairShortCycle.exists_short_cycle M ⟨s,hs⟩ ⟨t,ht⟩ hpole hfull'
  let R := N.induceEmbed Q
  have hcycle := (R.isCycleWord_push_iff z).mpr hz
  have hsize' : size (R.push z)≤4 := by rw [TransversalTransport.size_push]; exact hsize
  obtain ⟨v,_,hv⟩ := hX (R.push z) hcycle hsize'
  exact Finset.not_mem_empty v hv

/-- Positive-support normalization extends the bridgeless rank bound to weak poles. -/
theorem exists_bridgeless_bound (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t → N.IsBridgeless →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X → networkRank N≤5*C+4*k+4 := by
  have hε : (0 : ℝ)<1/(2:ℝ)^m := by positivity
  obtain ⟨C,hC⟩ := PoleGirthGap.exists_rank_bound_of_short_cycle_transversal _ hε
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hbl hrich X hX hhit
  obtain ⟨hs,ht,hpole,_,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
  let Q := fun v => 0<N.deg (fun _ => 1) v
  let M := N.induce Q
  let Y := X.subtype Q
  have hY : Y.card≤k := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans hX
  have hrich' : (1/2+1/(2:ℝ)^m)*(2:ℝ)^networkRank M≤M.numPaths ⟨s,hs⟩ ⟨t,ht⟩ := by
    rw [hp,hr]
    exact CyclicShoreMargin.real_margin m _ _ hrich
  have hhit' : Hits M Y := by
    convert TransversalTransport.hits_induce N Q X hhit using 1
    ext v
    simp [Y]
  have hh := hC k _ _ M ⟨s,hs⟩ ⟨t,ht⟩ hpole hrich' Y hY hhit'
  rw [hr] at hh
  omega

/-- The induction keeps exact path loss and additive rank simultaneously. -/
theorem exists_invariant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      ∃ q : ℕ,networkRank N≤(X.card+q)*(5*C+4*k+4) ∧
        16^q*N.numPaths s t≤15^q*2^networkRank N := by
  obtain ⟨C,hC⟩ := exists_bridgeless_bound m
  refine ⟨C,?_⟩
  intro k
  have key : ∀r : ℕ,∀ (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),networkRank N=r → N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      ∃ q : ℕ,networkRank N≤(X.card+q)*(5*C+4*k+4) ∧
        16^q*N.numPaths s t≤15^q*2^networkRank N := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro V E _ _ N s t hr hN hrich X hX hhit
      by_cases hbl : N.IsBridgeless
      · have hb := hC k V E N s t hN hbl hrich X hX hhit
        by_cases hmarks : X.Nonempty
        · have hc : 1≤X.card := Finset.card_pos.mpr hmarks
          refine ⟨0,?_,?_⟩
          · simp only [Nat.add_zero]
            nlinarith
          · simpa only [pow_zero,one_mul] using N.numPaths_le_two_pow s t
        · have hempty : X=∅ := Finset.not_nonempty_iff_eq_empty.mp hmarks
          have hn : ¬N.IsFullPair s t := not_full_of_empty_hits N s t hN hbl (hempty ▸ hhit)
          have hg := ExactMaximumSupport.gapStatement V E N hN.pole s t
            hN.port_s hN.port_t hN.ne
          have hgap : 16*N.numPaths s t≤15*2^networkRank N := hg.resolve_left hn
          refine ⟨1,?_,?_⟩
          · simpa only [hempty,Finset.card_empty,zero_add,one_mul] using hb
          · simpa only [pow_one] using hgap
      obtain ⟨e,he⟩ : ∃e,∀z,N.IsCycleWord z → z e=0 := by
        obtain ⟨e,he⟩ := not_forall.mp hbl
        exact ⟨e,fun z hz => Classical.not_not.mp (fun hn => he ⟨z,hz,hn⟩)⟩
      obtain ⟨S,x,y,sp⟩ := PoleMarginBridge.exists_split N m hN hrich he
      let X₁ := X.filter S
      let X₂ := X.filter fun v => ¬S v
      have hX₁ : X₁.card≤k := (Finset.card_filter_le _ _).trans hX
      have hX₂ : X₂.card≤k := (Finset.card_filter_le _ _).trans hX
      have hc : X₁.card+X₂.card=X.card :=
        Finset.filter_card_add_filter_neg_card_eq_card S
      have hlhit : Hits (N.sub (N.inside S)) X₁ := TransversalTransport.hits_inside N S X hhit
      have hrhit : Hits (N.sub (N.outside S)) X₂ := TransversalTransport.hits_outside N S X hhit
      have hlt : networkRank (N.sub (N.inside S))<r := by
        have := sp.rank_eq
        have := sp.right_rank_pos
        omega
      have hrt : networkRank (N.sub (N.outside S))<r := by
        have := sp.rank_eq
        have := sp.left_rank_pos
        omega
      obtain ⟨q₁,hr₁,hp₁⟩ := ih _ hlt V _ (N.sub (N.inside S)) s x rfl
        sp.left_pole sp.left_rich X₁ hX₁ hlhit
      obtain ⟨q₂,hr₂,hp₂⟩ := ih _ hrt V _ (N.sub (N.outside S)) y t rfl
        sp.right_pole sp.right_rich X₂ hX₂ hrhit
      refine ⟨q₁+q₂,?_,?_⟩
      · rw [sp.rank_eq]
        have hh := Nat.add_le_add hr₁ hr₂
        calc
          _ ≤ (X₁.card+q₁)*(5*C+4*k+4)+(X₂.card+q₂)*(5*C+4*k+4) := hh
          _ = (X.card+(q₁+q₂))*(5*C+4*k+4) := by rw [←hc]; ring
      · have hh := Nat.mul_le_mul hp₁ hp₂
        rw [sp.paths_eq,sp.rank_eq,pow_add,pow_add,pow_add]
        nlinarith [hh]
  intro V E _ _ N s t hN hrich X hX hhit
  exact key (networkRank N) V E N s t rfl hN hrich X hX hhit

/-- A uniform actual weak-two-pole rank bound, with arbitrary isolated vertices and bridges. -/
theorem exists_constant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      networkRank N≤(X.card+10)*(5*C+4*k+4) := by
  obtain ⟨C,hC⟩ := exists_invariant m
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hrich X hX hhit
  obtain ⟨q,hr,hp⟩ := hC k V E N s t hN hrich X hX hhit
  have hq := factor_count_le_ten q (networkRank N) (N.numPaths s t)
    (CyclicShoreMargin.strict_half m _ _ hrich) hp
  exact hr.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left hq _))

end Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalRank
