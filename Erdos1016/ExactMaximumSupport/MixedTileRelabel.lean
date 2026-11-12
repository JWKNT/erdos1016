import Erdos1016.ExactMaximumSupport.MixedTiles
import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false

/-!
# Relabel both rails of a physical tile chain

A single Bool permutation acts at every tile and interface.
The resulting map preserves every physical label and both port pairs.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

namespace Kind

/-- Apply the same rail permutation on both sides of a tile. -/
def railVertices (t : Kind) (p : Equiv.Perm Bool) : t.Vertex ≃ t.Vertex :=
  match t with
  | rung => p
  | square => Equiv.prodCongr (Equiv.refl Bool) p

/-- Relabel the physical tile edges under a rail permutation. -/
def railEdges (t : Kind) (p : Equiv.Perm Bool) : t.Edge ≃ t.Edge :=
  match t with
  | rung => Equiv.refl Unit
  | square => Equiv.prodCongr p p

@[simp] theorem railVertices_left (t : Kind) (p : Equiv.Perm Bool) (b : Bool) :
    t.railVertices p (t.left b)=t.left (p b) := by cases t <;> rfl

@[simp] theorem railVertices_right (t : Kind) (p : Equiv.Perm Bool) (b : Bool) :
    t.railVertices p (t.right b)=t.right (p b) := by cases t <;> rfl

/-- The local relabeling preserves the unordered ends of each physical label. -/
theorem railEdges_joins (t : Kind) (p : Equiv.Perm Bool) (e : t.Edge) :
    t.network.Joins (t.railEdges p e)
      (t.railVertices p (t.src e)) (t.railVertices p (t.dst e)) := by
  cases t with
  | square => exact Or.inl ⟨rfl,rfl⟩
  | rung =>
      have hne : p false≠p true := fun h => Bool.false_ne_true (p.injective h)
      cases h₀ : p false <;> cases h₁ : p true <;>
        simp_all [Network.Joins,network,src,dst,railVertices,railEdges]

end Kind

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The same rail permutation gives an exact physical chain isomorphism. -/
def railIso (p : Equiv.Perm Bool) : NetworkIso (chain T) (chain T) where
  vertices := Equiv.sigmaCongrRight fun i => (T i).railVertices p
  edges := Equiv.sumCongr (Equiv.sigmaCongrRight fun i => (T i).railEdges p)
    (Equiv.prodCongr (Equiv.refl (Fin k)) p)
  joins e := by
    rcases e with ⟨i,e⟩ | ⟨i,b⟩
    · rcases (T i).railEdges_joins p e with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ⟨congrArg (Sigma.mk i) hs,congrArg (Sigma.mk i) ht⟩
      · exact Or.inr ⟨congrArg (Sigma.mk i) hs,congrArg (Sigma.mk i) ht⟩
    · left
      constructor <;> simp [chain,chainSrc,chainDst,right,left,Equiv.sigmaCongrRight,
        Kind.railVertices_right,Kind.railVertices_left]

@[simp] theorem railIso_left (p : Equiv.Perm Bool) (i : Fin (k+1)) (b : Bool) :
    (railIso T p).vertices (left T i b)=left T i (p b) := by
  simp [railIso,left,Equiv.sigmaCongrRight]

@[simp] theorem railIso_right (p : Equiv.Perm Bool) (i : Fin (k+1)) (b : Bool) :
    (railIso T p).vertices (right T i b)=right T i (p b) := by
  simp [railIso,right,Equiv.sigmaCongrRight]

end Erdos1016.ExactMaximumSupport.MixedTiles
