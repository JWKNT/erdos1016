import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A marked rung immediately before a two-label interface

This exact identity uses the actual deleted-label shore counts. The suffix
count is an explicit parameter, to be supplied by the concrete suffix theorem.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MarkedRungCount
open BoundaryTrace BoundaryTrace.Network BoundaryDecay NetworkTwoCutPaths
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Deleting the marked physical label keeps every other label and all vertices. -/
abbrev deleted (N : Network V E) (e : E) := N.sub (fun q => q≠e)

/-- The two marked endpoints contribute the two symmetric shore products. -/
theorem count_eq (N : Network V E) (S : V → Prop) {e f g : E} {x u y v t : V}
    (he : N.Joins e x u) (hx : S x) (hu : S u)
    (hf : N.Joins f x y) (hy : ¬S y) (hg : N.Joins g u v) (hv : ¬S v)
    (hfg : f≠g) (hcover : ∀ q,N.crosses S q → q=f ∨ q=g) (ht : ¬S t)
    (B : ℕ)
    (hB₀ : (if y=t then 1 else
      ((deleted N e).sub ((deleted N e).outside S)).numPaths y t)=B)
    (hB₁ : (if v=t then 1 else
      ((deleted N e).sub ((deleted N e).outside S)).numPaths v t)=B) :
    MarkedPathCount.count N e t=
      2*(1+((deleted N e).sub ((deleted N e).inside S)).numPaths x u)*B := by
  have hei : N.inside S e := by
    rcases he with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · exact ⟨hs ▸ hx,hd ▸ hu⟩
    · exact ⟨hs ▸ hu,hd ▸ hx⟩
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
    hf' hx hy hg' hu hv hcover' hx ht
  have hucount := numPaths_of_two_crossing (deleted N e) S hfg'
    hf' hx hy hg' hu hv hcover' hu ht
  rw [if_pos rfl,if_neg he.ne,hB₀,hB₁,one_mul] at hxcount
  rw [if_neg he.ne.symm,if_pos rfl,hB₀,hB₁,one_mul,
    ExactMaximum.numPaths_symm ((deleted N e).sub ((deleted N e).inside S)) u x] at hucount
  have hxt : x≠t := fun h => ht (h ▸ hx)
  have hut : u≠t := fun h => ht (h ▸ hu)
  have hcount : MarkedPathCount.count N e t=
      (deleted N e).numPaths x t+(deleted N e).numPaths u t := by
    rw [MarkedPathCount.count_of_joins N he,MarkedPathCount.branch,MarkedPathCount.branch,
      if_neg hxt,if_neg hut]
  rw [hcount,hxcount,hucount]
  ring

end Erdos1016.ExactMaximumSupport.MarkedRungCount
