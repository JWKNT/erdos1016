import Erdos1016.ExactMaximumSupport.FourCutPartition
import Erdos1016.ExactMaximumSupport.MixedChainGlueModel
import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false

/-! # Assemble the original physical network from its two actual chain sides -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FourCutGluedIso
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
local instance gluedDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable (S : V → Prop) (e : Fin 4 → E) (x y : Fin 4 → V)
variable (hcubic : N.IsCubic) (hcover : ∀g,N.crosses S g → ∃i,g=e i)
    (hjoins : ∀i,N.Joins (e i) (x i) (y i))
    (hx : ∀i,S (x i)) (hy : ∀i,¬S (y i))
    (hxinj : Function.Injective x) (hyinj : Function.Injective y)
variable {k l : ℕ} (T : Fin (k+1) → Kind) (U : Fin (l+1) → Kind)
variable (J : NetworkIso (chain T) (ThirdPortMarkedCore.positive (N.sub (N.inside S))))
    (K : NetworkIso (chain U) (ThirdPortMarkedCore.positive (N.sub (N.outside S))))

include hcubic hcover hjoins hy hxinj in
omit [Fintype V] in
/-- Every original side vertex has positive degree in that side. -/
theorem inside_positive (v : V) :
    0<(N.sub (N.inside S)).deg (fun _ => 1) v ↔ S v :=
  FourCutPartition.positive_iff N hcubic S
    (FourPoleBoundary.no_double_end N S e x y hcover hjoins hy hxinj) v

include hcubic hcover hjoins hx hyinj in
omit [Fintype V] in
/-- The complementary side has the complementary positive-vertex set. -/
theorem outside_positive (v : V) :
    0<(N.sub (N.outside S)).deg (fun _ => 1) v ↔ ¬S v :=
  FourCutPartition.positive_iff N hcubic (fun v => ¬S v)
    (FourPoleBoundary.no_double_end N (fun v => ¬S v) e y x
      (fun g hg => hcover g ((N.crosses_not_iff S g).mp hg))
      (fun i => (hjoins i).symm) (fun i => not_not.mpr (hx i)) hyinj) v

/-- The actual two chain vertex maps cover every original vertex exactly once. -/
def vertices : (Vertex T ⊕ Vertex U) ≃ V :=
  (Equiv.sumCongr J.vertices K.vertices).trans
    (FourCutPartition.vertices N S
      (inside_positive N S e x y hcubic hcover hjoins hy hxinj)
      (outside_positive N S e x y hcubic hcover hjoins hx hyinj))

/-- The side-label maps and four cut labels retain every original physical label exactly once. -/
def edges (ρ : (Bool ⊕ Bool) ≃ Fin 4) : GluedEdge T U ≃ E :=
  (Equiv.sumCongr
    (Equiv.sumCongr (J.edges.trans (FourCutPartition.positiveEdges (N.sub (N.inside S))))
      (K.edges.trans (FourCutPartition.positiveEdges (N.sub (N.outside S))))) ρ).trans
    (FourCutPartition.edges N S e x y hcover hjoins hx hy hxinj)

/-- Given the exact four endpoint identifications, the glued physical model is the original network. -/
def iso (twist : Equiv.Perm Bool) (ρ : (Bool ⊕ Bool) ≃ Fin 4)
    (hclosing : ∀b,N.Joins (e (ρ (Sum.inl b)))
      (K.vertices (right U (Fin.last l) b)).val (J.vertices (left T 0 (twist b))).val)
    (hcentral : ∀b,N.Joins (e (ρ (Sum.inr b)))
      (J.vertices (right T (Fin.last k) b)).val (K.vertices (left U 0 b)).val) :
    NetworkIso (glued T U twist) N where
  vertices := vertices N S e x y hcubic hcover hjoins hx hy hxinj hyinj T U J K
  edges := edges N S e x y hcover hjoins hx hy hxinj T U J K ρ
  joins g := by
    rcases g with (g | g) | (b | b)
    · change N.Joins (J.edges g).val.val
        (J.vertices ((chain T).src g)).val (J.vertices ((chain T).dst g)).val
      rcases J.joins g with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
      · exact Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
    · change N.Joins (K.edges g).val.val
        (K.vertices ((chain U).src g)).val (K.vertices ((chain U).dst g)).val
      rcases K.joins g with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
      · exact Or.inr ⟨congrArg Subtype.val hs,congrArg Subtype.val ht⟩
    · exact hclosing b
    · exact hcentral b

end Erdos1016.ExactMaximumSupport.FourCutGluedIso
