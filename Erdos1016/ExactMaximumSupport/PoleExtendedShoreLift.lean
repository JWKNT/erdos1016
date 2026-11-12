import Erdos1016.ExactMaximumSupport.PoleExtendedShore
import Erdos1016.ExactMaximumSupport.FourPoleBridgeLift

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Lift an extended shore across one physical bridge

The bridge consumes the budget already assigned to its endpoint.
Both cycle claims and every marked vertex remain explicit.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleExtendedShore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance extendedLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- Reversing the two designated ports preserves the extended boundary budget. -/
theorem ExtendedShore.symm {s t : V} {X : Finset V} {U : V → Prop}
    (h : ExtendedShore N s t X U) : ExtendedShore N t s X U := by
  refine ⟨h.positive,h.avoid,h.inside_cycle,?_,?_⟩
  · have hh := h.budget
    omega
  · rcases h.outside_cycle_or_port with hc | hs | ht
    · exact Or.inl hc
    · exact Or.inr (Or.inr hs)
    · exact Or.inr (Or.inl ht)

/-- A containing physical edge restriction retains an actual cycle. -/
theorem cycle_pos_mono (p q : E → Prop) (hpq : ∀e,p e → q e)
    (hp : 0<(N.sub p).numCycles) : 0<(N.sub q).numCycles := by
  let R : Network.Embed (N.sub p) (N.sub q) :=
    { φ := id
      ψ := fun e => ⟨e.val,hpq e.val e.property⟩
      φ_inj := Function.injective_id
      ψ_inj := fun e f h => Subtype.ext (congrArg (fun z : {e // q e} => z.val) h)
      src := fun _ => rfl
      dst := fun _ => rfl }
  obtain ⟨⟨z,hz⟩⟩ := Finite.card_pos_iff.mp hp
  haveI : Nonempty {z : (N.sub q).Word // (N.sub q).IsCycleWord z} :=
    ⟨⟨R.push z,(R.isCycleWord_push_iff z).mpr hz⟩⟩
  exact Nat.card_pos

omit [Fintype V] in
/-- Lifting a shore contained in one bridge side adds at most the bridge endpoint indicator. -/
theorem cutSize_lift_bridge (S U : V → Prop) {e : E} {x y : V}
    (he : N.Joins e x y) (_hx : S x) (hy : ¬S y)
    (hC : ∀g,N.crosses S g → g=e) (hU : ∀v,U v → S v) :
    N.cutSize U≤(N.sub (N.inside S)).cutSize U+(if U x then 1 else 0) := by
  have hlabels (g : E) (hg : N.crosses U g) (hgi : ¬N.inside S g) : g=e ∧ U x := by
    have hcross : N.crosses S g := by
      change ¬(S (N.src g) ↔ S (N.dst g))
      change ¬(S (N.src g) ∧ S (N.dst g)) at hgi
      change ¬(U (N.src g) ↔ U (N.dst g)) at hg
      have hsrc := hU (N.src g)
      have hdst := hU (N.dst g)
      tauto
    have hge := hC g hcross
    refine ⟨hge,?_⟩
    rw [hge] at hg
    have hUy : ¬U y := fun h => hy (hU y h)
    rcases he with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · change ¬(U (N.src e) ↔ U (N.dst e)) at hg
      simpa only [hs,ht,hUy,iff_false,not_not] using hg
    · change ¬(U (N.src e) ↔ U (N.dst e)) at hg
      simpa only [hs,ht,hUy,false_iff,not_not] using hg
  let F : {g : E // N.crosses U g} →
      {g : {g : E // N.inside S g} // (N.sub (N.inside S)).crosses U g} ⊕ {b : Unit // U x} :=
    fun g => if hi : N.inside S g.val then Sum.inl ⟨⟨g.val,hi⟩,g.property⟩
      else Sum.inr ⟨(),(hlabels g.val g.property hi).2⟩
  have hinj : Function.Injective F := by
    intro g h hF
    by_cases hg : N.inside S g.val
    · by_cases hh : N.inside S h.val
      · simp only [F,dif_pos hg,dif_pos hh,Sum.inl.injEq] at hF
        exact Subtype.ext (congrArg (fun z => z.val.val) hF)
      · simp only [F,dif_pos hg,dif_neg hh,Sum.inl_ne_inr] at hF
    · by_cases hh : N.inside S h.val
      · simp only [F,dif_neg hg,dif_pos hh,Sum.inr_ne_inl] at hF
      · exact Subtype.ext ((hlabels g.val g.property hg).1.trans
          (hlabels h.val h.property hh).1.symm)
  have hcard := Nat.card_le_card_of_injective F hinj
  rw [Nat.card_sum] at hcard
  have hunit : Nat.card {b : Unit // U x}=(if U x then 1 else 0) := by
    by_cases h : U x <;> simp [h]
  rw [hunit] at hcard
  exact hcard

/-- An extended shore of the first bridge side lifts with its original marker avoidance. -/
theorem lift_left {s t x y : V} {e : E} (S U : V → Prop) (X : Finset V)
    (he : N.Joins e x y) (hx : S x) (hy : ¬S y)
    (hC : ∀g,N.crosses S g → g=e) (ht : ¬S t)
    (houtside : 0<(N.sub (N.outside S)).numCycles)
    (h : ExtendedShore (N.sub (N.inside S)) s x
      (X.filter fun v => 0<(N.sub (N.inside S)).deg (fun _ => 1) v) U) :
    ExtendedShore N s t X U := by
  have hU : ∀v,U v → S v := by
    intro v hv
    have hp := h.positive v hv
    by_contra hn
    rw [N.deg_inside_of_not_mem S hn] at hp
    omega
  have hUt : ¬U t := fun h => ht (hU t h)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro v hv
    have hp := h.positive v hv
    have hd := N.deg_inside_of_one_crossing S he hx hy hC (hU v hv)
    omega
  · intro v hv hmem
    exact h.avoid v hv (Finset.mem_filter.mpr ⟨hmem,h.positive v hv⟩)
  · exact FourPoleBridgeLift.cycle_pos_of_nested N (N.inside S)
      ((N.sub (N.inside S)).inside U) (N.inside U) (fun _ hu => hu) h.inside_cycle
  · have hcut := cutSize_lift_bridge N S U he hx hy hC hU
    have hb := h.budget
    rw [if_neg hUt]
    omega
  · left
    apply cycle_pos_mono N (N.outside S) (N.outside U) _ houtside
    intro g hg
    exact ⟨fun hv => hg.1 (hU _ hv),fun hv => hg.2 (hU _ hv)⟩

end Erdos1016.ExactMaximumSupport.PoleExtendedShore
