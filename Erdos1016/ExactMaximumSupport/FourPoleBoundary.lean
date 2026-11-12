import Erdos1016.ExactMaximum.FourCutStructure
import Erdos1016.ExactMaximum.PoleSides

set_option autoImplicit false

/-! # The exact ports of a cubic side with distinct boundary endpoints -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourPoleBoundary
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance boundaryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
variable (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
include hcover hjoins hx hy

omit [Fintype V] [Fintype E] hx in
/-- A crossing label at a vertex in the side identifies one of the prescribed ports. -/
theorem incidence {v : V} (hv : S v) {g : E} (hg : N.crosses S g)
    (hat : N.src g=v ∨ N.dst g=v) : ∃i,g=e i ∧ v=x i := by
  obtain ⟨i,rfl⟩ := hcover g hg
  refine ⟨i,rfl,?_⟩
  rcases hjoins i with ⟨hs,hd⟩ | ⟨hs,hd⟩
  · rcases hat with hat | hat
    · exact hat.symm.trans hs
    · exact (hy i ((hat.symm.trans hd) ▸ hv)).elim
  · rcases hat with hat | hat
    · exact (hy i ((hat.symm.trans hs) ▸ hv)).elim
    · exact hat.symm.trans hd

omit [Fintype V] [Fintype E] hx in
/-- Injective boundary endpoints preclude two crossing labels at one side vertex. -/
theorem no_double_end (hinj : Function.Injective x) : N.NoDoubleEnd S := by
  intro f g v w₁ w₂ hfg hf hg hv hw₁ hw₂
  obtain ⟨i,hi,hvi⟩ := incidence N S e x y hcover hjoins hy hv
    (N.crosses_of_joins hf hv hw₁) hf.at_left
  obtain ⟨j,hj,hvj⟩ := incidence N S e x y hcover hjoins hy hv
    (N.crosses_of_joins hg hv hw₂) hg.at_left
  have hij : i=j := hinj (hvi.symm.trans hvj)
  exact hfg (hi.trans ((congrArg e hij).trans hj.symm))

omit [Fintype V] in
/-- Every listed boundary endpoint is a port of the induced side. -/
theorem isPort (hcubic : N.IsCubic) (hinj : Function.Injective x) (i : Fin 4) :
    (N.sub (N.inside S)).IsPort (x i) :=
  N.isPort_inside_of hcubic S (no_double_end N S e x y hcover hjoins hy hinj)
    (hjoins i) (hx i) (hy i)

omit [Fintype V] hx in
/-- A side port must be the inside endpoint of one of its boundary labels. -/
theorem only (hcubic : N.IsCubic) (v : V) (hv : (N.sub (N.inside S)).IsPort v) :
    ∃i,v=x i := by
  have hSv : S v := by
    by_contra h
    have hz := N.deg_inside_of_not_mem S h
    change (N.sub (N.inside S)).deg (fun _ => 1) v=2 at hv
    omega
  have hdegree := N.deg_inside_add hcubic S hSv
  have hpos : 0<N.deg (restrict (fun _ => 1) (N.crosses S)) v := by
    change (N.sub (N.inside S)).deg (fun _ => 1) v=2 at hv
    omega
  obtain ⟨g,hg,hat⟩ := N.exists_edge_of_deg_pos hpos
  have hcross := ((restrict_ne_zero_iff (fun _ => 1) (N.crosses S) g).mp hg).1
  obtain ⟨i,_,hi⟩ := incidence N S e x y hcover hjoins hy hSv hcross hat
  exact ⟨i,hi⟩

omit [Fintype V] in
/-- The side has exactly its four prescribed ports. -/
theorem isPort_iff (hcubic : N.IsCubic) (hinj : Function.Injective x) (v : V) :
    (N.sub (N.inside S)).IsPort v ↔ ∃i,v=x i := by
  constructor
  · exact only N S e x y hcover hjoins hy hcubic v
  · rintro ⟨i,rfl⟩
    exact isPort N S e x y hcover hjoins hx hy hcubic hinj i

end Erdos1016.ExactMaximumSupport.FourPoleBoundary
