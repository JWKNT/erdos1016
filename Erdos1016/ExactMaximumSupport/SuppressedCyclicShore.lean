import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.NetSmallCut

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A cyclic shore survives tracked degree-two suppression

The shore is the same predicate on the original vertex type.  Avoiding the two
thread ends and its middle vertex preserves both cyclic sides, the exact physical
cut size, and all degrees on the shore.  Parallel edge labels are retained.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.SuppressedCyclicShore
open BoundaryTrace BoundaryTrace.Network
local instance suppressedShoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]
variable {N : Network V E} {e f : E} {u v w : V} (T : N.Thread e f u v w)

/-- A supported word grows inside the same vertex predicate whenever its new
edge can be expanded through the old middle vertex. -/
theorem within_grow_inside (Q : V → Prop) (hthrough : Q u → Q w → Q v)
    (y : (N.suppress e f u w T.huw).Word)
    (hy : Within y ((N.suppress e f u w T.huw).inside Q)) :
    Within (grow e f T.hef y) (N.inside Q) := by
  intro g hg
  have heQ (he : y ⟨e,T.hef⟩ ≠ 0) : Q u ∧ Q w := by
    have hh := hy ⟨e,T.hef⟩ he
    simpa only [Network.inside, N.suppress_src_of_eq (e := e) (f := f) T.huw ⟨e,T.hef⟩ rfl,
      N.suppress_dst_of_eq (e := e) (f := f) T.huw ⟨e,T.hef⟩ rfl] using hh
  by_cases hgf : g=f
  · subst g
    rw [grow_apply_f] at hg
    obtain ⟨hu,hw⟩ := heQ hg
    rcases T.hf with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ hthrough hu hw,h2 ▸ hw⟩
    · exact ⟨h1 ▸ hw,h2 ▸ hthrough hu hw⟩
  · rw [grow_apply_of_ne T.hef y hgf] at hg
    by_cases hge : g=e
    · subst g
      obtain ⟨hu,hw⟩ := heQ hg
      rcases T.he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact ⟨h1 ▸ hu,h2 ▸ hthrough hu hw⟩
      · exact ⟨h1 ▸ hthrough hu hw,h2 ▸ hu⟩
    · have hh := hy ⟨g,hgf⟩ hg
      simpa only [Network.inside,N.suppress_src_of_ne (e := e) (f := f) T.huw ⟨g,hgf⟩ hge,
        N.suppress_dst_of_ne (e := e) (f := f) T.huw ⟨g,hgf⟩ hge] using hh

/-- An actual internal cycle grows through the suppression, with all original
labels and the same containing vertex predicate. -/
theorem cycle_pos_inside (Q : V → Prop) (hthrough : Q u → Q w → Q v)
    (hcyc : 0<((N.suppress e f u w T.huw).sub
      ((N.suppress e f u w T.huw).inside Q)).numCycles) :
    0<(N.sub (N.inside Q)).numCycles := by
  rw [Network.numCycles_sub] at hcyc ⊢
  obtain ⟨⟨y,hy,hwithin⟩⟩ := Finite.card_pos_iff.mp hcyc
  haveI : Nonempty {z : N.Word // N.IsCycleWord z ∧ Within z (N.inside Q)} :=
    ⟨⟨grow e f T.hef y,(T.isCycleWord_grow_iff y).mpr hy,
      within_grow_inside T Q hthrough y hwithin⟩⟩
  exact Nat.card_pos

/-- Both cyclic sides lift to the same original vertex shore. -/
theorem cyclic_lift (S : V → Prop) (hu : ¬S u) (hv : ¬S v)
    (hS : (N.suppress e f u w T.huw).IsCyclicCut S) : N.IsCyclicCut S := by
  exact ⟨cycle_pos_inside T S (fun hs _ => (hu hs).elim) hS.1,
    cycle_pos_inside T (fun x => ¬S x) (fun _ _ => hv) hS.2⟩

omit [Fintype V] [Fintype E] in
/-- A surviving physical label crosses exactly the same shore when the thread
is wholly outside it. -/
theorem crosses_iff (S : V → Prop) (hu : ¬S u) (hv : ¬S v) (hw : ¬S w)
    (g : {g : E // g≠f}) :
    (N.suppress e f u w T.huw).crosses S g ↔ N.crosses S g.val := by
  by_cases hge : g.val=e
  · have heout : N.outside S e := by
      rcases T.he with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact ⟨h1 ▸ hu,h2 ▸ hv⟩
      · exact ⟨h1 ▸ hv,h2 ▸ hu⟩
    have hmout : (N.suppress e f u w T.huw).outside S g := by
      simpa only [Network.outside,N.suppress_src_of_eq T.huw _ hge,
        N.suppress_dst_of_eq T.huw _ hge] using And.intro hu hw
    exact iff_of_false ((N.suppress e f u w T.huw).not_crosses_of_outside hmout)
      (hge ▸ N.not_crosses_of_outside heout)
  · simp only [Network.crosses,N.suppress_src_of_ne T.huw _ hge,
      N.suppress_dst_of_ne T.huw _ hge]

/-- Suppression outside a shore preserves the exact number of crossing labels. -/
theorem cutSize_eq (S : V → Prop) (hu : ¬S u) (hv : ¬S v) (hw : ¬S w) :
    (N.suppress e f u w T.huw).cutSize S=N.cutSize S := by
  have hfout : N.outside S f := by
    rcases T.hf with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ hv,h2 ▸ hw⟩
    · exact ⟨h1 ▸ hw,h2 ▸ hv⟩
  have hne : ∀g,N.crosses S g → g≠f := by
    intro g hg hgf
    exact N.not_crosses_of_outside hfout (hgf ▸ hg)
  apply Nat.card_congr
  exact
    { toFun := fun g => ⟨g.val.val,(crosses_iff T S hu hv hw g.val).mp g.property⟩
      invFun := fun g => ⟨⟨g.val,hne g.val g.property⟩,
        (crosses_iff T S hu hv hw _).mpr g.property⟩
      left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; rfl }

omit [Fintype V] in
/-- The unchanged actual shore is cubic in the original network. -/
theorem cubic_lift (S : V → Prop) (hv : ¬S v)
    (hdeg : ∀x,S x → (N.suppress e f u w T.huw).deg (fun _ => 1) x=3) :
    ∀x,S x → N.deg (fun _ => 1) x=3 := by
  intro x hx
  have hneq : x≠v := fun h => hv (h ▸ hx)
  rw [←T.deg_suppress hneq]
  exact hdeg x hx

/-- One tracked suppression step, retaining the literal original shore. -/
theorem lift (S : V → Prop) (hu : ¬S u) (hv : ¬S v) (hw : ¬S w)
    (hS : (N.suppress e f u w T.huw).IsCyclicCut S)
    (hdeg : ∀x,S x → (N.suppress e f u w T.huw).deg (fun _ => 1) x=3) :
    N.IsCyclicCut S ∧ N.cutSize S=(N.suppress e f u w T.huw).cutSize S ∧
      ∀x,S x → N.deg (fun _ => 1) x=3 :=
  ⟨cyclic_lift T S hu hv hS,(cutSize_eq T S hu hv hw).symm,cubic_lift T S hv hdeg⟩

end Erdos1016.ExactMaximumSupport.SuppressedCyclicShore
