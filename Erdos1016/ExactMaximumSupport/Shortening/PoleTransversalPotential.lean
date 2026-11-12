import Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalRank

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A linear path-weighted potential replaces the count of deficient bridge factors.
The constant fifteen replaces ten. No previous transversal-rank endpoint is used. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalPotential
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ShortCycleTransversal
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The reciprocal-density defect is superadditive under a product. -/
theorem product_budget (p q a b : ℕ) (hp : p≤a) (hq : q≤b) :
    a*q+b*p≤a*b+p*q := by
  have hh : 0≤(a-p)*(b-q) := Nat.zero_le _
  have hp' : a=p+(a-p) := (Nat.add_sub_of_le hp).symm
  have hq' : b=q+(b-q) := (Nat.add_sub_of_le hq).symm
  nlinarith

/-- Add actual bridge ranks and mark counts while multiplying the actual path counts. -/
theorem combine (p q a b r s x y L : ℕ) (hp : p≤a) (hq : q≤b)
    (hr : p*r+15*L*p≤L*(p*x+15*a))
    (hs : q*s+15*L*q≤L*(q*y+15*b)) :
    (p*q)*(r+s)+15*L*(p*q)≤L*((p*q)*(x+y)+15*(a*b)) := by
  have h1 := Nat.mul_le_mul_right q hr
  have h2 := Nat.mul_le_mul_right p hs
  have h3 := Nat.mul_le_mul_left (15*L) (product_budget p q a b hp hq)
  nlinarith [h1,h2,h3]

/-- One actual rank induction suffices; there is no auxiliary factor count. -/
theorem exists_potential (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      N.numPaths s t*networkRank N+15*(5*C+4*k+4)*N.numPaths s t ≤
        (5*C+4*k+4)*(N.numPaths s t*X.card+15*2^networkRank N) := by
  obtain ⟨C,hC⟩ := PoleTransversalRank.exists_bridgeless_bound m
  refine ⟨C,?_⟩
  intro k
  have key : ∀r : ℕ,∀ (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),networkRank N=r → N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      N.numPaths s t*networkRank N+15*(5*C+4*k+4)*N.numPaths s t ≤
        (5*C+4*k+4)*(N.numPaths s t*X.card+15*2^networkRank N) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro V E _ _ N s t hr hN hrich X hX hhit
      by_cases hbl : N.IsBridgeless
      · have hb := hC k V E N s t hN hbl hrich X hX hhit
        have hmul := Nat.mul_le_mul_left (N.numPaths s t) hb
        by_cases hmarks : X.Nonempty
        · have hc : 1≤X.card := Finset.card_pos.mpr hmarks
          have hp := N.numPaths_le_two_pow s t
          have hcharge := Nat.mul_le_mul_left ((5*C+4*k+4)*N.numPaths s t) hc
          have hcap := Nat.mul_le_mul_left (15*(5*C+4*k+4)) hp
          nlinarith [hmul,hcharge,hcap]
        · have hempty : X=∅ := Finset.not_nonempty_iff_eq_empty.mp hmarks
          have hn := PoleTransversalRank.not_full_of_empty_hits N s t hN hbl (hempty ▸ hhit)
          have hg := ExactMaximumSupport.gapStatement V E N hN.pole s t
            hN.port_s hN.port_t hN.ne
          have hgap : 16*N.numPaths s t≤15*2^networkRank N := hg.resolve_left hn
          have hh := Nat.mul_le_mul_left (5*C+4*k+4) hgap
          simp only [hempty,Finset.card_empty,Nat.mul_zero,zero_add]
          nlinarith [hmul,hh]
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
      have hr₁ := ih _ hlt V _ (N.sub (N.inside S)) s x rfl
        sp.left_pole sp.left_rich X₁ hX₁ hlhit
      have hr₂ := ih _ hrt V _ (N.sub (N.outside S)) y t rfl
        sp.right_pole sp.right_rich X₂ hX₂ hrhit
      have hh := combine _ _ _ _ _ _ _ _ _
        ((N.sub (N.inside S)).numPaths_le_two_pow s x)
        ((N.sub (N.outside S)).numPaths_le_two_pow y t) hr₁ hr₂
      rw [sp.paths_eq,sp.rank_eq,pow_add,←hc]
      exact hh
  intro V E _ _ N s t hN hrich X hX hhit
  exact key (networkRank N) V E N s t rfl hN hrich X hX hhit

/-- Strictly more than half the paths bounds the reciprocal-density defect by one. -/
theorem exists_constant (m : ℕ) :
    ∃ C : ℕ,∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),N.IsWeakTwoPole s t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      ∀ X : Finset V,X.card≤k → Hits N X →
      networkRank N≤(X.card+15)*(5*C+4*k+4) := by
  obtain ⟨C,hC⟩ := exists_potential m
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hrich X hX hhit
  have hh := hC k V E N s t hN hrich X hX hhit
  have hhalf := CyclicShoreMargin.strict_half m _ _ hrich
  have hpos : 0<N.numPaths s t := by have := Nat.two_pow_pos (networkRank N); omega
  have hcap := Nat.mul_le_mul_left (15*(5*C+4*k+4)) hhalf.le
  have hm : N.numPaths s t*networkRank N≤N.numPaths s t*((X.card+15)*(5*C+4*k+4)) := by
    nlinarith [hh,hcap]
  exact Nat.le_of_mul_le_mul_left hm hpos

end Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalPotential
