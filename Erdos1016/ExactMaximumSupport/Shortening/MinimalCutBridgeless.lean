import Erdos1016.ExactMaximum.PoleSides
import Erdos1016.ExactMaximum.PoleLayers
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A minimum cyclic cut has bridgeless shores

If a shore has minimum positive degree two, each side of an internal bridge
contains a cycle. Their ambient cut sizes add to the original cut size plus two.
Thus a minimum cyclic cut of size at least three cannot have such a bridge.
No full-pair or ladder classification is used.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.Shortening.MinimalCutBridgeless
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- The two parts of a shore count each internal crossing label twice. -/
theorem cut_partition (S T : V → Prop) :
    N.cutSize (fun v => S v ∧ T v) + N.cutSize (fun v => S v ∧ ¬T v) =
      N.cutSize S + 2 * (N.sub (N.inside S)).cutSize T := by
  classical
  have hsub : (N.sub (N.inside S)).cutSize T =
      Nat.card {e : E // N.inside S e ∧ N.crosses T e} := by
    apply Nat.card_congr
    exact
      { toFun := fun e => ⟨e.val.val, e.val.property, e.property⟩
        invFun := fun e => ⟨⟨e.val,e.property.1⟩,e.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hsub]
  simp only [Network.cutSize, natCard_subtype_eq_card_filter, Finset.card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hs : S (N.src e) <;> by_cases ht : S (N.dst e) <;>
    by_cases hu : T (N.src e) <;> by_cases hv : T (N.dst e) <;>
    simp [Network.crosses,Network.inside,hs,ht,hu,hv]

omit [Fintype E] in
/-- A nested cycle remains a cycle in every containing edge restriction. -/
theorem cycle_pos_of_nested (p : E → Prop) (q : {e // p e} → Prop) (r : E → Prop)
    [Fintype {e // p e}] [Fintype {e : {e // p e} // q e}] [Fintype {e // r e}]
    (hqr : ∀e,q e → r e.val) (hcyc : 0<((N.sub p).sub q).numCycles) :
    0<(N.sub r).numCycles := by
  classical
  let R : Network.Embed ((N.sub p).sub q) (N.sub r) :=
    { φ := id
      ψ := fun e => ⟨e.val.val,hqr e.val e.property⟩
      φ_inj := Function.injective_id
      ψ_inj := by
        intro e f h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun e : {e // r e} => e.val) h
      src := fun _ => rfl
      dst := fun _ => rfl }
  obtain ⟨⟨z,hz⟩⟩ := Finite.card_pos_iff.mp hcyc
  haveI : Nonempty {x : (N.sub r).Word // (N.sub r).IsCycleWord x} :=
    ⟨⟨R.push z,(R.isCycleWord_push_iff z).mpr hz⟩⟩
  exact Nat.card_pos

/-- Both cycles of an internal cyclic cut survive in its ambient intersection cut. -/
theorem cyclic_intersection (S T : V → Prop)
    (hT : (N.sub (N.inside S)).IsCyclicCut T) :
    N.IsCyclicCut (fun v => S v ∧ T v) := by
  classical
  constructor
  · exact cycle_pos_of_nested N (N.inside S) ((N.sub (N.inside S)).inside T)
      (N.inside (fun v => S v ∧ T v))
      (fun e he => ⟨⟨e.property.1,he.1⟩,⟨e.property.2,he.2⟩⟩) hT.1
  · exact cycle_pos_of_nested N (N.inside S) ((N.sub (N.inside S)).outside T)
      (N.outside (fun v => S v ∧ T v))
      (fun _ he => ⟨fun h => he.1 h.2,fun h => he.2 h.2⟩) hT.2

/-- A bridge in a network of minimum positive degree two gives a cyclic cut of size one. -/
theorem cyclic_cut_of_bridge
    (hdeg : ∀v,N.deg (fun _ => 1) v=0 ∨ 2≤N.deg (fun _ => 1) v)
    (e : E) (hbr : ∀z : N.Word,N.IsCycleWord z → z e=0) :
    ∃T : V → Prop,N.IsCyclicCut T ∧ N.cutSize T=1 := by
  classical
  let T := N.sideOf e (N.src e)
  have he : N.Joins e (N.src e) (N.dst e) := Or.inl ⟨rfl,rfl⟩
  have hx : T (N.src e) := N.sideOf_self e (N.src e)
  have hy : ¬T (N.dst e) := N.not_reachable_of_bridge hbr he
  have hC : ∀g,N.crosses T g → g=e := fun _ hg => N.eq_of_crosses_sideOf e _ hg
  have hC' : ∀g,N.crosses (fun v => ¬T v) g → g=e :=
    fun g hg => hC g ((N.crosses_not_iff T g).mp hg)
  have hl := N.rank_side_pos_of_one_crossing hdeg T he hx hy hC
  have hr := N.rank_side_pos_of_one_crossing hdeg (fun v => ¬T v)
    he.symm hy (not_not.mpr hx) hC'
  have hcyc : N.IsCyclicCut T :=
    ⟨(N.sub (N.inside T)).numCycles_pos_of_rank_pos hl,
      (N.sub (N.outside T)).numCycles_pos_of_rank_pos hr⟩
  have hsize : N.cutSize T=1 := Nat.card_eq_one_iff_unique.mpr
    ⟨⟨fun f g => Subtype.ext ((hC f.1 f.2).trans (hC g.1 g.2).symm)⟩,
      ⟨⟨e,N.crosses_of_joins he hx hy⟩⟩⟩
  exact ⟨T,hcyc,hsize⟩

/-- A minimum cyclic cut of size at least three has a bridgeless minimum-degree-two shore. -/
theorem side_bridgeless_of_cut_le (S : V → Prop) (d : ℕ) (hd : 3≤d)
    (hsize : N.cutSize S≤d)
    (hmin : ∀T,N.IsCyclicCut T → d≤N.cutSize T)
    (hdeg : ∀v,(N.sub (N.inside S)).deg (fun _ => 1) v=0 ∨
      2≤(N.sub (N.inside S)).deg (fun _ => 1) v) :
    (N.sub (N.inside S)).IsBridgeless := by
  classical
  intro e
  by_contra he
  have hbr : ∀z : (N.sub (N.inside S)).Word,
      (N.sub (N.inside S)).IsCycleWord z → z e=0 := by
    intro z hz
    by_contra hne
    exact he ⟨z,hz,hne⟩
  obtain ⟨T,hcyc,hcut⟩ := cyclic_cut_of_bridge (N.sub (N.inside S)) hdeg e hbr
  have hcyc' : (N.sub (N.inside S)).IsCyclicCut (fun v => ¬T v) := by
    constructor
    · simpa only [Network.inside,Network.outside] using hcyc.2
    · have hp : (N.sub (N.inside S)).outside (fun v => ¬T v) =
          (N.sub (N.inside S)).inside T := by
        funext e
        simp [Network.outside,Network.inside]
      rw [hp]
      exact hcyc.1
  have hleft := hmin _ (cyclic_intersection N S T hcyc)
  have hright := hmin _ (cyclic_intersection N S (fun v => ¬T v) hcyc')
  change d≤N.cutSize (fun v => S v ∧ ¬T v) at hright
  have hcount := cut_partition N S T
  rw [hcut] at hcount
  omega

/-- The minimum-cut formulation applies without port data or path-count hypotheses. -/
theorem side_bridgeless (S : V → Prop) (d : ℕ) (hd : 3≤d)
    (hsize : N.cutSize S=d)
    (hmin : ∀T,N.IsCyclicCut T → d≤N.cutSize T)
    (hdeg : ∀v,(N.sub (N.inside S)).deg (fun _ => 1) v=0 ∨
      2≤(N.sub (N.inside S)).deg (fun _ => 1) v) :
    (N.sub (N.inside S)).IsBridgeless :=
  side_bridgeless_of_cut_le N S d hd hsize.le hmin hdeg

/-- In the four-cut application, the existing weak-pole hypothesis suffices. -/
theorem four_cut_shore_bridgeless (S : V → Prop)
    (hsize : N.cutSize S≤4)
    (hmin : ∀T,N.IsCyclicCut T → 4≤N.cutSize T)
    (hpole : (N.sub (N.inside S)).IsWeakPole) :
    (N.sub (N.inside S)).IsBridgeless :=
  side_bridgeless_of_cut_le N S 4 (by decide) hsize hmin hpole.deg_zero_or_two_le

end Erdos1016.ExactMaximumSupport.Shortening.MinimalCutBridgeless
