import Erdos1016.ExactMaximumSupport.Shortening.MarginFewCyclesCore
import Erdos1016.ExactMaximumSupport.PoleMarginBridge
import Erdos1016.ExactMaximumSupport.PolePortReduction

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A uniform square-root cycle bound at every fixed positive path margin,
including bridges, extra ports and isolated ambient vertices. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.MarginFewCycles
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
local instance marginDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Quantitative induction through actual bridge shores at a fixed dyadic margin. -/
theorem pole_invariant (m K : ℕ)
    (h : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t → (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      N.numCycles^2≤K*2^networkRank N) (V : Type) [Fintype V] :
    ∀ n : ℕ, ∀ (E : Type) [Fintype E] (N : Network V E) (s t : V), Fintype.card E=n →
      N.IsWeakTwoPole s t → (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      (N.numCycles+2*(K+2))^2≤4*(K+2)^2*2^networkRank N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ N s t hcard hN hrich
    by_cases hbl : N.IsBridgeless
    · obtain ⟨hs,ht,hpole,hc,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
      have hcore := h _ _ _ _ _ hpole (by rw [hr,hp]; exact hrich)
      rw [hc,hr] at hcore
      exact invariant_base N.numCycles_lt_two_pow (fun _ => hcore)
    · obtain ⟨e,he⟩ : ∃e,∀z:N.Word,N.IsCycleWord z → z e=0 := by
        unfold IsBridgeless at hbl
        obtain ⟨e,he⟩ := not_forall.1 hbl
        exact ⟨e,fun z hz => Classical.not_not.1 fun hne => he ⟨z,hz,hne⟩⟩
      obtain ⟨S,x,y,hsplit⟩ := PoleMarginBridge.exists_split N m hN hrich he
      have hce := N.crosses_of_joins hsplit.joins hsplit.mem_x hsplit.not_mem_y
      have hlt₁ : Fintype.card {g:E // N.inside S g}<n := by
        rw [←hcard]
        exact Fintype.card_subtype_lt (N.not_inside_of_crosses hce)
      have hlt₂ : Fintype.card {g:E // N.outside S g}<n := by
        rw [←hcard]
        exact Fintype.card_subtype_lt (N.not_outside_of_crosses hce)
      have h1 := ih _ hlt₁ _ (N.sub (N.inside S)) s x rfl hsplit.left_pole hsplit.left_rich
      have h2 := ih _ hlt₂ _ (N.sub (N.outside S)) y t rfl hsplit.right_pole hsplit.right_rich
      rw [N.numCycles_of_one_crossing S hsplit.only_cross,hsplit.rank_eq,pow_add]
      exact invariant_add (by omega : 0<K+2) h1 h2

/-- Extra-port suppression and bridge splitting preserve the dyadic richness. -/
theorem exists_dyadic_bound (m : ℕ) :
    ∃ K : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      N.IsWeakPole → ∀s t, N.IsPort s → N.IsPort t → s≠t →
      (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      N.numCycles^2≤K*2^networkRank N := by
  obtain ⟨K,hK⟩ := MarginFewCyclesCore.exists_bound (1/(2:ℝ)^m) (by positivity)
  have hbase : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t → (2^m+2)*2^networkRank N≤2^(m+1)*N.numPaths s t →
      N.numCycles^2≤K*2^networkRank N := by
    intro V E _ _ N s t hN hr
    exact hK V E N s t hN (CyclicShoreMargin.real_margin m _ _ hr)
  refine ⟨4*(K+2)^2,?_⟩
  intro V E _ _ N hN s t hs ht hst hrich
  obtain ⟨E',inst,N',hN',hr,hp,hc⟩ := PolePortReduction.exists_two_pole V E N hN s t hs ht hst
    (CyclicShoreMargin.strict_half m _ _ hrich)
  have hi := pole_invariant m K hbase V _ E' N' s t rfl hN' (by rw [hr,hp]; exact hrich)
  rw [hc,hr] at hi
  exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) 2).trans hi

/-- A positive real margin contains a dyadic margin. -/
theorem exists_dyadic_le (ε : ℝ) (hε : 0<ε) : ∃m:ℕ,1/(2:ℝ)^m≤ε := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ε)
  have hmp : (m:ℝ)≤(2:ℝ)^m := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))
  have hmε : 1≤(m:ℝ)*ε := (div_le_iff₀ hε).mp hm.le
  refine ⟨m,(div_le_iff₀ (by positivity : 0<(2:ℝ)^m)).mpr ?_⟩
  nlinarith

/-- Arbitrary-margin Theorem 5.4 for the original physical weak pole. -/
theorem exists_bound (ε : ℝ) (hε : 0<ε) :
    ∃K:ℕ, ∀(V E:Type) [Fintype V] [Fintype E] (N:Network V E),
      N.IsWeakPole → ∀s t,N.IsPort s → N.IsPort t → s≠t →
      (1/2+ε)*(2:ℝ)^networkRank N≤N.numPaths s t →
      N.numCycles^2≤K*2^networkRank N := by
  obtain ⟨m,hm⟩ := exists_dyadic_le ε hε
  obtain ⟨K,hK⟩ := exists_dyadic_bound m
  refine ⟨K,?_⟩
  intro V E _ _ N hN s t hs ht hst hrich
  apply hK V E N hN s t hs ht hst
  have hd : 0<(2:ℝ)^m := by positivity
  have hh : (1/2+1/(2:ℝ)^m)*(2:ℝ)^networkRank N≤N.numPaths s t :=
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)).trans hrich
  have he : (1/2+1/(2:ℝ)^m)=((2:ℝ)^m+2)/((2:ℝ)^m*2) := by
    field_simp
    left
    ring
  rw [he,div_mul_eq_mul_div] at hh
  have hh' := (div_le_iff₀ (by positivity : 0<(2:ℝ)^m*2)).mp hh
  have hfinal : ((2:ℝ)^m+2)*(2:ℝ)^networkRank N≤(2:ℝ)^(m+1)*N.numPaths s t := by
    rw [pow_succ]; nlinarith
  exact_mod_cast hfinal

end Erdos1016.ExactMaximumSupport.Shortening.MarginFewCycles
