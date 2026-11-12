import Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore

set_option autoImplicit false

/-!
# Removing isolated vertices commutes with restricting physical labels

If a vertex set contains every edge endpoint, its induced network retains
all paths after any further restriction of physical labels.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkPositiveSubnetwork
open BoundaryTrace BoundaryTrace.Network
local instance (priority := 2000) positiveSubnetworkDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The canonical embedding retains the original vertex and physical label. -/
def restrictedEmbed (S : V → Prop) (p : E → Prop) :
    Network.Embed ((N.induce S).sub fun g => p g.1) (N.sub p) where
  φ := Subtype.val
  ψ := fun g => ⟨g.1.1,g.2⟩
  φ_inj := Subtype.val_injective
  ψ_inj := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g : {g : E // p g} => g.1) h
  src _ := rfl
  dst _ := rfl

omit [Fintype V] [Fintype E] in
/-- Every retained label is in the embedding when its endpoints belong to the vertex set. -/
theorem restricted_image (S : V → Prop) (p : E → Prop)
    (hS : ∀ e,N.inside S e) (g : {e : E // p e}) :
    (restrictedEmbed N S p).image g := by
  exact ⟨⟨⟨g.1,hS g.1⟩,g.2⟩,rfl⟩

/-- An induced vertex set containing all endpoints preserves every restricted path count. -/
theorem numPaths_induce_sub (S : V → Prop) (p : E → Prop)
    (hS : ∀ e,N.inside S e) (s t : {v : V // S v}) :
    ((N.induce S).sub fun g => p g.1).numPaths s t = (N.sub p).numPaths s.1 t.1 := by
  rw [(restrictedEmbed N S p).numPaths_eq s t]
  unfold Network.numPaths
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun y =>
    ⟨fun h => h.1,fun h => ⟨h,fun g _ => restricted_image N S p hS g⟩⟩

/-- Removing original isolated vertices preserves arbitrary physical edge restrictions. -/
theorem numPaths_positive_sub (p : E → Prop)
    (s t : {v : V // 0 < N.deg (fun _ => 1) v}) :
    ((ThirdPortMarkedCore.positive N).sub fun g => p g.1).numPaths s t =
      (N.sub p).numPaths s.1 t.1 := by
  apply numPaths_induce_sub N _ p _ s t
  intro e
  exact ⟨N.deg_src_pos (show (fun _ : E => (1 : Bit)) e≠0 from one_ne_zero),
    N.deg_dst_pos (show (fun _ : E => (1 : Bit)) e≠0 from one_ne_zero)⟩

/-- A marked-edge deletion is preserved by the positive-degree normalization. -/
theorem numPaths_positive_deleteEdge (e : E)
    (s t : {v : V // 0 < N.deg (fun _ => 1) v}) :
    ((ThirdPortMarkedCore.positive N).sub fun g => g.1≠e).numPaths s t =
      (N.sub fun g => g≠e).numPaths s.1 t.1 :=
  numPaths_positive_sub N (fun g => g≠e) s t

end Erdos1016.ExactMaximumSupport.NetworkPositiveSubnetwork
