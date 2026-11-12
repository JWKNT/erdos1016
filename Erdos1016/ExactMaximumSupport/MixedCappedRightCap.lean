import Erdos1016.ExactMaximumSupport.MixedCappedCapCounts
import Erdos1016.ExactMaximumSupport.PoleAdjacentGap
import Erdos1016.ExactMaximum.PoleSides

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # The marked right-cap labels have a quarter loss -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedRightCap
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- A marked label incident to the target has a quarter loss when it lies on a cycle. -/
theorem marked_target_quarter (N : Network V E) {e : E} {a t : V}
    (he : N.Joins e a t) {z : N.Word} (hz : N.IsCycleWord z) (hze : z e≠0)
    (hr : 2≤networkRank N) :
    4*MarkedPathCount.count N e t≤3*2^networkRank N := by
  have hh := PoleAdjacentGap.two_mul_avoiding_paths_le N he hz hze
  have hc : MarkedPathCount.count N e t=
      Nat.card {P : N.Word // N.IsPathWord a t P ∧ P e=0}+1 := by
    rw [MarkedPathCount.count_of_joins N he,MarkedPathCount.branch,MarkedPathCount.branch,
      if_neg he.ne,if_pos rfl,N.numPaths_sub]
    apply congrArg (fun q => q+1)
    exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
      and_congr Iff.rfl (NetworkCutDeletedPaths.within_delete_iff N P e))
  have hp : 4≤2^networkRank N := by
    calc 4=2^2 := by norm_num
         _≤2^networkRank N := Nat.pow_le_pow_right (by decide) hr
  rw [hc]
  omega

variable {k : ℕ}

/-- The original physical chain inside its two-cap network. -/
def chainEmbed (T : Fin (k+1) → Kind) : Network.Embed (chain T) (capped T) where
  φ := Sum.inl
  ψ := Sum.inl
  φ_inj := Sum.inl_injective
  ψ_inj := Sum.inl_injective
  src _ := rfl
  dst _ := rfl

/-- Both right-cap labels lie on an actual cycle made from a chain path. -/
theorem right_cap_on_cycle (T : Fin (k+1) → Kind) (b : Bool) :
    ∃ z : (capped T).Word,(capped T).IsCycleWord z ∧
      z (Sum.inr (Sum.inr b))≠0 := by
  have hne : right T (Fin.last k) b≠right T (Fin.last k) (!b) := by
    intro h
    have he : b=(!b) := (T (Fin.last k)).right_injective (by
      simpa only [right,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h)
    cases b <;> simp at he
  obtain ⟨P,hP,_⟩ := (chain T).exists_isPathWord_of_reachable (fun _ => True) hne
    ((chain T).reachable_sub_of_forall (fun _ => True.intro)
      ((chain_connected T).preconnected _ _))
  let Q : (capped T).Word := (chainEmbed T).push P
  have hQ : (capped T).IsPathWord (Sum.inl (right T (Fin.last k) b))
      (Sum.inl (right T (Fin.last k) (!b))) Q :=
    ((chainEmbed T).isPathWord_push_iff _ _ P).mpr hP
  have hw : Within Q ((capped T).outside (fun v => v=Sum.inr true)) := by
    intro e he
    obtain ⟨g,rfl⟩ := (chainEmbed T).within_push P e he
    constructor <;> simp [chainEmbed,capped,cappedSrc,cappedDst]
  have hzero : (capped T).deg Q (Sum.inr true)=0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact (capped T).not_mem_of_within_outside hw hp rfl
  have hf : (capped T).Joins (Sum.inr (Sum.inr (!b)))
      (Sum.inl (right T (Fin.last k) (!b))) (Sum.inr true) := Or.inl ⟨rfl,rfl⟩
  have he : (capped T).Joins (Sum.inr (Sum.inr b))
      (Sum.inl (right T (Fin.last k) b)) (Sum.inr true) := Or.inl ⟨rfl,rfl⟩
  have hqe : Q (Sum.inr (Sum.inr b))=0 :=
    (capped T).eq_zero_of_deg_eq_zero hzero he.at_right
  have havoid : (Q+unitWord (Sum.inr (Sum.inr (!b))) : (capped T).Word) (Sum.inr (Sum.inr b))=0 := by
    cases b <;> simp [Pi.add_apply,hqe,unitWord_apply]
  refine ⟨Q+unitWord (Sum.inr (Sum.inr (!b)))+unitWord (Sum.inr (Sum.inr b)),
    (hQ.add_pendant hf hzero).add_closing he havoid,?_⟩
  rw [Pi.add_apply,havoid,unitWord_apply,if_pos rfl,zero_add]
  exact one_ne_zero

/-- Restoring a right-cap label loses at least one quarter of the full capacity. -/
theorem right_cap_quarter (T : Fin (k+1) → Kind) (b : Bool) :
    4*MarkedPathCount.count (capped T) (Sum.inr (Sum.inr b)) (Sum.inr true)≤
      3*2^(weight T+1) := by
  obtain ⟨z,hz,he⟩ := right_cap_on_cycle T b
  have hw : 1≤weight T := by
    calc 1≤(T 0).weight := Kind.weight_pos _
         _≤∑ i : Fin (k+1),(T i).weight :=
           Finset.single_le_sum (fun i _ => Nat.zero_le ((T i).weight)) (Finset.mem_univ (0 : Fin (k+1)))
  have h := marked_target_quarter (capped T)
    (show (capped T).Joins (Sum.inr (Sum.inr b))
      (Sum.inl (right T (Fin.last k) b)) (Sum.inr true) from Or.inl ⟨rfl,rfl⟩)
    hz he (by rw [capped_rank]; omega)
  simpa only [capped_rank] using h

end Erdos1016.ExactMaximumSupport.MixedCappedRightCap
