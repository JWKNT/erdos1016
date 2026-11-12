import Erdos1016.ExactMaximumSupport.FourPoleBoundary
import Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore

set_option autoImplicit false

/-!
# Original vertices and physical labels at a four-cut

The two positive-degree sides partition the original vertices. Their physical
labels, together with the four cut labels, partition the original labels.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutPartition
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance partitionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
/-- With at most one outgoing label, a cubic side has positive degree at every vertex of the side. -/
theorem positive_iff (hcubic : N.IsCubic) (S : V → Prop) (hno : N.NoDoubleEnd S) (v : V) :
    0<(N.sub (N.inside S)).deg (fun _ => 1) v ↔ S v := by
  constructor
  · intro hp
    by_contra hn
    have hz := N.deg_inside_of_not_mem S hn
    omega
  · intro hv
    have hsum := N.deg_inside_add hcubic S hv
    have hsmall := N.crossDeg_le_one_of S hno hv
    omega

/-- The positive vertices of the first physical side. -/
abbrev LeftVertex (S : V → Prop) := {v : V // 0<(N.sub (N.inside S)).deg (fun _ => 1) v}
/-- The positive vertices of the second physical side. -/
abbrev RightVertex (S : V → Prop) := {v : V // 0<(N.sub (N.outside S)).deg (fun _ => 1) v}

omit [Fintype V] in
/-- Positive sides with the actual membership laws partition the original vertex type. -/
def vertices (S : V → Prop)
    (hl : ∀v,0<(N.sub (N.inside S)).deg (fun _ => 1) v ↔ S v)
    (hr : ∀v,0<(N.sub (N.outside S)).deg (fun _ => 1) v ↔ ¬S v) :
    (LeftVertex N S ⊕ RightVertex N S) ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if h : S v then Sum.inl ⟨v,(hl v).mpr h⟩ else Sum.inr ⟨v,(hr v).mpr h⟩
  left_inv := by
    rintro (v | v)
    · simp only [Sum.elim_inl,dif_pos ((hl v.val).mp v.property)]
    · simp only [Sum.elim_inr,dif_neg ((hr v.val).mp v.property)]
  right_inv := by intro v; by_cases h : S v <;> simp [h]

omit [Fintype V] in
@[simp] theorem vertices_left (S : V → Prop) (hl hr) (v : LeftVertex N S) :
    vertices N S hl hr (Sum.inl v)=v.val := rfl

omit [Fintype V] in
@[simp] theorem vertices_right (S : V → Prop) (hl hr) (v : RightVertex N S) :
    vertices N S hl hr (Sum.inr v)=v.val := rfl

omit [Fintype V] in
/-- Removing isolated vertices retains exactly every physical label. -/
def positiveEdges : {e : E // N.inside (fun v => 0<N.deg (fun _ => 1) v) e} ≃ E where
  toFun := Subtype.val
  invFun := ThirdPortMarkedCore.positiveEdge N
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
variable (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i)) (hinj : Function.Injective x)
include hcover hjoins hx hy hinj

omit [Fintype V] [Fintype E] hcover in
/-- Distinct first-side endpoints force distinct crossing labels. -/
theorem cut_labels_injective : Function.Injective e := by
  intro i j hij
  have hh := hjoins j
  rw [←hij] at hh
  have hxi : x i=x j := by
    rcases hjoins i with ⟨hi₁,hi₂⟩ | ⟨hi₁,hi₂⟩
    · rcases hh with ⟨hj₁,hj₂⟩ | ⟨hj₁,hj₂⟩
      · exact hi₁.symm.trans hj₁
      · exact (hy j ((hi₁.symm.trans hj₁) ▸ hx i)).elim
    · rcases hh with ⟨hj₁,hj₂⟩ | ⟨hj₁,hj₂⟩
      · exact (hy j ((hi₂.symm.trans hj₂) ▸ hx i)).elim
      · exact hi₂.symm.trans hj₂
  exact hinj hxi

/-- The direct physical label map from the two sides and four interfaces. -/
def edgeMap : ({g : E // N.inside S g} ⊕ {g : E // N.outside S g}) ⊕ Fin 4 → E
  | Sum.inl (Sum.inl g) => g.val
  | Sum.inl (Sum.inr g) => g.val
  | Sum.inr i => e i

omit [Fintype V] [Fintype E] in
/-- Every label occurs in exactly one of the physical side/interface classes. -/
theorem edgeMap_bijective : Function.Bijective (edgeMap N S e) := by
  have hcross i := N.crosses_of_joins (hjoins i) (hx i) (hy i)
  constructor
  · rintro ((g | g) | i) ((h | h) | j) he
    all_goals dsimp only [edgeMap] at he
    · exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext he)
    · exact ((N.not_outside_of_inside g.property) (he.symm ▸ h.property)).elim
    · exact ((N.not_inside_of_crosses (hcross j)) (he ▸ g.property)).elim
    · exact ((N.not_outside_of_inside h.property) (he ▸ g.property)).elim
    · exact congrArg (Sum.inl ∘ Sum.inr) (Subtype.ext he)
    · exact ((N.not_outside_of_crosses (hcross j)) (he ▸ g.property)).elim
    · exact ((N.not_inside_of_crosses (hcross i)) (he.symm ▸ h.property)).elim
    · exact ((N.not_outside_of_crosses (hcross i)) (he.symm ▸ h.property)).elim
    · exact congrArg Sum.inr (cut_labels_injective N S e x y hjoins hx hy hinj he)
  · intro g
    by_cases hi : N.inside S g
    · exact ⟨Sum.inl (Sum.inl ⟨g,hi⟩),rfl⟩
    by_cases ho : N.outside S g
    · exact ⟨Sum.inl (Sum.inr ⟨g,ho⟩),rfl⟩
    have hc : N.crosses S g := by
      change ¬(S (N.src g) ↔ S (N.dst g))
      change ¬(S (N.src g) ∧ S (N.dst g)) at hi
      change ¬(¬S (N.src g) ∧ ¬S (N.dst g)) at ho
      tauto
    obtain ⟨i,rfl⟩ := hcover g hc
    exact ⟨Sum.inr i,rfl⟩

/-- The physical side/interface partition as an exact label equivalence. -/
def edges : (({g : E // N.inside S g} ⊕ {g : E // N.outside S g}) ⊕ Fin 4) ≃ E :=
  Equiv.ofBijective (edgeMap N S e) (edgeMap_bijective N S e x y hcover hjoins hx hy hinj)

end Erdos1016.ExactMaximumSupport.FourCutPartition
