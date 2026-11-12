import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A marked local label before a two-label interface

This exact identity uses the actual deleted-label shore counts. The suffix
count is an explicit parameter, to be supplied by the concrete suffix theorem.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MarkedTileCount
open BoundaryTrace BoundaryTrace.Network BoundaryDecay NetworkTwoCutPaths
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Deleting the marked physical label keeps every other label and all vertices. -/
abbrev deleted (N : Network V E) (e : E) := N.sub (fun q => q≠e)

/-- The two marked endpoints contribute the two symmetric shore products. -/
theorem count_eq (N : Network V E) (S : V → Prop) {e f g : E} {a b x u y v t : V}
    (he : N.Joins e a b) (ha : S a) (hb : S b) (hx : S x) (hu : S u)
    (hf : N.Joins f x y) (hy : ¬S y) (hg : N.Joins g u v) (hv : ¬S v)
    (hfg : f≠g) (hcover : ∀ q,N.crosses S q → q=f ∨ q=g) (ht : ¬S t)
    (B : ℕ)
    (hB₀ : (if y=t then 1 else
      ((deleted N e).sub ((deleted N e).outside S)).numPaths y t)=B)
    (hB₁ : (if v=t then 1 else
      ((deleted N e).sub ((deleted N e).outside S)).numPaths v t)=B) :
    MarkedPathCount.count N e t=
      ((if a=x then 1 else ((deleted N e).sub ((deleted N e).inside S)).numPaths a x)+
        (if a=u then 1 else ((deleted N e).sub ((deleted N e).inside S)).numPaths a u)+
        (if b=x then 1 else ((deleted N e).sub ((deleted N e).inside S)).numPaths b x)+
        (if b=u then 1 else ((deleted N e).sub ((deleted N e).inside S)).numPaths b u))*B := by
  have hei : N.inside S e := by
    rcases he with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · exact ⟨hs ▸ ha,hd ▸ hb⟩
    · exact ⟨hs ▸ hb,hd ▸ ha⟩
  have hfne : f≠e := fun h =>
    N.not_crosses_of_inside hei (h ▸ N.crosses_of_joins hf hx hy)
  have hgne : g≠e := fun h =>
    N.not_crosses_of_inside hei (h ▸ N.crosses_of_joins hg hu hv)
  let f' : {q : E // q≠e} := ⟨f,hfne⟩
  let g' : {q : E // q≠e} := ⟨g,hgne⟩
  have hf' : (deleted N e).Joins f' x y := hf
  have hg' : (deleted N e).Joins g' u v := hg
  have hfg' : f'≠g' := fun h => hfg (congrArg Subtype.val h)
  have hcover' (q : {q : E // q≠e}) (hq : (deleted N e).crosses S q) : q=f' ∨ q=g' := by
    rcases hcover q.val hq with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hxcount := numPaths_of_two_crossing (deleted N e) S hfg'
    hf' hx hy hg' hu hv hcover' ha ht
  have hucount := numPaths_of_two_crossing (deleted N e) S hfg'
    hf' hx hy hg' hu hv hcover' hb ht
  rw [hB₀,hB₁] at hxcount hucount
  have hxt : a≠t := fun h => ht (h ▸ ha)
  have hut : b≠t := fun h => ht (h ▸ hb)
  have hcount : MarkedPathCount.count N e t=
      (deleted N e).numPaths a t+(deleted N e).numPaths b t := by
    rw [MarkedPathCount.count_of_joins N he,MarkedPathCount.branch,MarkedPathCount.branch,
      if_neg hxt,if_neg hut]
  rw [hcount,hxcount,hucount]
  ring

end Erdos1016.ExactMaximumSupport.MarkedTileCount
