import Erdos1016.ExactMaximumSupport.PoleCyclicShore
import Erdos1016.ExactMaximum.PoleBridges

set_option autoImplicit false

/-!
# Cyclic shores with a boundary budget at the two ports

The extended budget permits a shore to pass through a bridge endpoint.
When both terminal ports are marked, it becomes an ordinary cubic cyclic shore.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleExtendedShore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance extendedShoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A shore retains its inside cycle and accounts for exposed terminal ports. -/
structure ExtendedShore (s t : V) (X : Finset V) (S : V → Prop) : Prop where
  positive : ∀ v,S v → 0<N.deg (fun _ => 1) v
  avoid : ∀ v,S v → v∉X
  inside_cycle : 0<(N.sub (N.inside S)).numCycles
  budget : N.cutSize S+(if S s then 1 else 0)+(if S t then 1 else 0)≤4
  outside_cycle_or_port : 0<(N.sub (N.outside S)).numCycles ∨ S s ∨ S t

omit [Fintype V] in
/-- Avoiding both ports converts the extended budget into a cubic cyclic shore. -/
theorem ExtendedShore.cubic {s t : V} {X : Finset V} {S : V → Prop}
    (h : ExtendedShore N s t X S) (hN : N.IsWeakTwoPole s t)
    (hs : s∈X) (ht : t∈X) :
    N.IsCyclicCut S ∧ N.cutSize S≤4 ∧ ∀v,S v → N.deg (fun _ => 1) v=3 := by
  have hns : ¬S s := fun hS => h.avoid s hS hs
  have hnt : ¬S t := fun hS => h.avoid t hS ht
  refine ⟨⟨h.inside_cycle,?_⟩,?_,?_⟩
  · exact h.outside_cycle_or_port.resolve_right (not_or.mpr ⟨hns,hnt⟩)
  · simpa only [if_neg hns,if_neg hnt,Nat.add_zero] using h.budget
  · intro v hv
    have hp := h.positive v hv
    rcases hN.deg_other (fun he => hns (he ▸ hv)) (fun he => hnt (he ▸ hv)) with hz | hz
    · omega
    · exact hz

/-- The whole positive component is an extended shore when it contains no marked vertex. -/
theorem whole_positive {s t : V} (hN : N.IsWeakTwoPole s t)
    (hr : 0<networkRank N) (X : Finset V)
    (hX : ∀v,v∈X → N.deg (fun _ => 1) v=0) :
    ExtendedShore N s t X (fun v => 0<N.deg (fun _ => 1) v) := by
  let S := fun v => 0<N.deg (fun _ => 1) v
  have hall : ∀e,N.inside S e := fun e =>
    ⟨N.deg_src_pos (x := fun _ => 1) (e := e) one_ne_zero,
      N.deg_dst_pos (x := fun _ => 1) (e := e) one_ne_zero⟩
  have hcut : N.cutSize S=0 := by
    apply Nat.card_eq_zero.mpr
    left
    refine ⟨?_⟩
    rintro ⟨e,he⟩
    exact he ⟨fun _ => (hall e).2,fun _ => (hall e).1⟩
  have hs : S s := by change 0<N.deg (fun _ => 1) s; rw [hN.port_s]; omega
  have ht : S t := by change 0<N.deg (fun _ => 1) t; rw [hN.port_t]; omega
  refine ⟨fun _ hv => hv,?_,?_,?_,Or.inr (Or.inl hs)⟩
  · intro v hv hmem
    have hz := hX v hmem
    change 0<N.deg (fun _ => 1) v at hv
    omega
  · rw [N.numCycles_sub_of_forall _ hall]
    exact N.numCycles_pos_of_rank_pos hr
  · rw [hcut,if_pos hs,if_pos ht]
    norm_num

end Erdos1016.ExactMaximumSupport.PoleExtendedShore
