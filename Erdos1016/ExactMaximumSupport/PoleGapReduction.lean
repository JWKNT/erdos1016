import Erdos1016.ExactMaximum.FullPairs
import Erdos1016.ExactMaximum.PoleBridges
import Erdos1016.ExactMaximumSupport.PolePortReduction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Reduce the gap theorem to connected bridgeless two-poles

Physical port suppression preserves rank and path count above half capacity.
Across bridges, the path counts multiply and ranks add.
The connected bridgeless gap is still an explicit hypothesis here.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleGapReduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance gapReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The remaining structural gap statement for connected bridgeless two-poles. -/
def BridgelessGapStatement : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
    N.IsBridgelessTwoPole s t →
    N.numPaths s t = 2 ^ networkRank N ∨ 16 * N.numPaths s t ≤ 15 * 2 ^ networkRank N

/-- A multiplicative loss in either factor remains a loss in the product. -/
theorem gap_product (x y X Y : ℕ) (hx : x ≤ X) (hy : y ≤ Y)
    (h1 : x = X ∨ 16*x ≤ 15*X) (h2 : y = Y ∨ 16*y ≤ 15*Y) :
    x*y = X*Y ∨ 16*(x*y) ≤ 15*(X*Y) := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact Or.inl (by rw [h1,h2])
    · right
      calc
        16*(x*y) = x*(16*y) := by ring
        _ ≤ X*(15*Y) := Nat.mul_le_mul hx h2
        _ = 15*(X*Y) := by ring
  · right
    calc
      16*(x*y) = (16*x)*y := by ring
      _ ≤ (15*X)*Y := Nat.mul_le_mul h1 hy
      _ = 15*(X*Y) := by ring

/-- The actual bridge induction preserves the gap for all weak two-poles. -/
theorem gap_of_two_pole_bounded (R : ℕ)
    (h : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t → networkRank N ≤ R →
      N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N)
    (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V)
    (hN : N.IsWeakTwoPole s t) (hrank : networkRank N ≤ R) :
    N.numPaths s t = 2 ^ networkRank N ∨ 16 * N.numPaths s t ≤ 15 * 2 ^ networkRank N := by
  have key : ∀ n : ℕ, ∀ (E : Type) [Fintype E] (N : Network V E) (s t : V),
      Fintype.card E = n → N.IsWeakTwoPole s t → networkRank N ≤ R →
      N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E _ N s t hcard hN hbound
      by_cases hmany : 501*2^networkRank N ≤ 1000*N.numPaths s t
      · by_cases hbl : N.IsBridgeless
        · obtain ⟨hs,ht,hpole,hc,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
          have hh := h _ _ _ _ _ hpole (by rw [hr]; exact hbound)
          rw [hr,hp] at hh
          exact hh
        · obtain ⟨e,he⟩ : ∃ e, ∀ Z : N.Word, N.IsCycleWord Z → Z e = 0 := by
            unfold IsBridgeless at hbl
            obtain ⟨e,he⟩ := not_forall.1 hbl
            exact ⟨e,fun Z hZ => Classical.not_not.1 fun hn => he ⟨Z,hZ,hn⟩⟩
          obtain ⟨S,x,y,hj,hx,hy,hC,hSs,hSt,hT₁,hT₂⟩ :=
            N.exists_bridge_split hN hmany he
          have hce : N.crosses S e := N.crosses_of_joins hj hx hy
          have hrank := N.networkRank_of_one_crossing S hC hce
          have hpaths := N.numPaths_of_one_crossing S hj hx hy hC hSs hSt hT₁.ne hT₂.ne
          have hlt₁ : Fintype.card {g : E // N.inside S g} < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (N.not_inside_of_crosses hce)
          have hlt₂ : Fintype.card {g : E // N.outside S g} < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt (N.not_outside_of_crosses hce)
          have h1 := ih _ hlt₁ _ (N.sub (N.inside S)) s x rfl hT₁ (by omega)
          have h2 := ih _ hlt₂ _ (N.sub (N.outside S)) y t rfl hT₂ (by omega)
          have hh := gap_product _ _ _ _ ((N.sub (N.inside S)).numPaths_le_two_pow s x)
            ((N.sub (N.outside S)).numPaths_le_two_pow y t) h1 h2
          rw [hrank,pow_add,hpaths]
          exact hh
      · right
        omega
  exact key _ E N s t rfl hN hrank

/-- The actual bridge induction preserves an unrestricted bridgeless gap. -/
theorem gap_of_two_pole (h : BridgelessGapStatement)
    (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V)
    (hN : N.IsWeakTwoPole s t) :
    N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N :=
  gap_of_two_pole_bounded (networkRank N) (fun V E _ _ N s t hN _ => h V E N s t hN)
    V E N s t hN le_rfl

/-- A bounded-rank bridgeless gap extends to all weak poles of that rank bound. -/
theorem gap_of_rank_bound (R : ℕ)
    (h : ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t → networkRank N ≤ R →
      N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N)
    (V E : Type) [Fintype V] [Fintype E] (N : Network V E) (hN : N.IsWeakPole)
    (s t : V) (hs : N.IsPort s) (ht : N.IsPort t) (hst : s ≠ t)
    (hrank : networkRank N ≤ R) :
    N.numPaths s t = 2 ^ networkRank N ∨ 16*N.numPaths s t ≤ 15*2^networkRank N := by
  by_cases hmany : 2 ^ networkRank N < 2*N.numPaths s t
  · obtain ⟨E',inst,N',hN',hr,hp,hc⟩ :=
      PolePortReduction.exists_two_pole V E N hN s t hs ht hst hmany
    have hh := gap_of_two_pole_bounded R h V E' N' s t hN' (by rw [hr]; exact hrank)
    rw [hr,hp] at hh
    exact hh
  · right
    omega

/-- The complete gap theorem follows once its connected bridgeless case is proved. -/
theorem gapStatement_of_bridgeless (h : BridgelessGapStatement) : ExactMaximum.GapStatement := by
  intro V E _ _ N hN s t hs ht hst
  by_cases hmany : 2 ^ networkRank N < 2 * N.numPaths s t
  · obtain ⟨E',inst,N',hN',hr,hp,hc⟩ :=
      PolePortReduction.exists_two_pole V E N hN s t hs ht hst hmany
    have hh := gap_of_two_pole h V E' N' s t hN'
    rw [hr,hp] at hh
    exact hh
  · right
    omega

end Erdos1016.ExactMaximumSupport.PoleGapReduction
