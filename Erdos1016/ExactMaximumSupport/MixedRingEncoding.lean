import Erdos1016.ExactMaximumSupport.MixedTileStates
import Erdos1016.ExactMaximumSupport.MixedTilesRank
import Mathlib.Tactic.Convert

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Physical word encoding for mixed rings

The interface labels and one local choice per square determine an even word.
This statement is proved from the actual labelled incidence boundary.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The part of a ring word on the physical labels of one tile. -/
def ringTileWord (z : RingEdge T → Bit) (i : Fin (k+1)) : (T i).network.Word :=
  fun e => z (Sum.inl (inner T i e))

private theorem sum_at_tile (f : (i : Fin (k+1)) → (T i).Edge → Bit)
    (ends : (i : Fin (k+1)) → (T i).Edge → (T i).Vertex)
    (i : Fin (k+1)) (v : (T i).Vertex) :
    (∑ e : InnerEdge T, if (⟨e.1,ends e.1 e.2⟩ : Vertex T)=⟨i,v⟩ then f e.1 e.2 else 0) =
      ∑ e : (T i).Edge, if ends i e=v then f i e else 0 := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro e _
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro e _
    apply if_neg
    intro h
    exact hji (congrArg Sigma.fst h)
  · simp

/-- A word with zero interface labels has the same boundary as its local tile word. -/
theorem boundary_at_tile_of_zero_interfaces (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word)
    (hlink : ∀ i b, z (Sum.inl (link T i b))=0)
    (hclose : ∀ b, z (Sum.inr b)=0) (i : Fin (k+1)) (v : (T i).Vertex) :
    (ring T hk twist).boundary z ⟨i,v⟩=(T i).network.boundary (ringTileWord T z i) v := by
  classical
  rw [Network.boundary_apply,Network.boundary_apply]
  simp only [ring,ringSrc,ringDst,chain,chainSrc,chainDst,
    Fintype.sum_sum_type,Fintype.sum_prod_type]
  have hlink' (j : Fin k) (b : Bool) : z (Sum.inl (Sum.inr (j,b)))=0 := hlink j b
  simp only [hlink',hclose,ite_self,Finset.sum_const_zero,add_zero]
  have hs := sum_at_tile T (fun i e => z (Sum.inl (Sum.inl ⟨i,e⟩)))
      (fun i => (T i).src) i v
  have hd := sum_at_tile T (fun i e => z (Sum.inl (Sum.inl ⟨i,e⟩)))
      (fun i => (T i).dst) i v
  simp only [Sigma.eta] at hs hd
  simp only [Kind.network,ringTileWord,inner]
  convert congrArg₂ (·+·) hs hd using 2 <;>
    apply Finset.sum_congr rfl <;> intro e _ <;> split_ifs <;> rfl

/-- Equal interfaces give equal local boundaries for two even physical words. -/
theorem tile_boundary_eq_of_interfaces (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (x y : (ring T hk twist).Word)
    (hx : (ring T hk twist).boundary x=0) (hy : (ring T hk twist).boundary y=0)
    (hlink : ∀ i b,x (Sum.inl (link T i b))=y (Sum.inl (link T i b)))
    (hclose : ∀ b,x (Sum.inr b)=y (Sum.inr b)) (i : Fin (k+1)) :
    (T i).network.boundary (ringTileWord T x i)=
      (T i).network.boundary (ringTileWord T y i) := by
  have hzero : (ring T hk twist).boundary (x-y)=0 := by simp only [map_sub,hx,hy,sub_self]
  funext v
  have hh := boundary_at_tile_of_zero_interfaces T hk twist (x-y)
    (fun j b => by change x _-y _=0; rw [hlink]; exact sub_self _)
    (fun b => by change x _-y _=0; rw [hclose]; exact sub_self _) i v
  have he : ringTileWord T (x-y) i=ringTileWord T x i-ringTileWord T y i := rfl
  rw [hzero,Pi.zero_apply,he,map_sub,Pi.sub_apply] at hh
  exact sub_eq_zero.mp hh.symm

/-- Interfaces and local corner choices determine every label of an even ring word. -/
theorem even_word_eq_of_encoding (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (x y : (ring T hk twist).Word)
    (hx : (ring T hk twist).boundary x=0) (hy : (ring T hk twist).boundary y=0)
    (hlink : ∀ i b,x (Sum.inl (link T i b))=y (Sum.inl (link T i b)))
    (hclose : ∀ b,x (Sum.inr b)=y (Sum.inr b))
    (hchoice : ∀ i,stateChoice (T i) (ringTileWord T x i)=
      stateChoice (T i) (ringTileWord T y i)) : x=y := by
  have ht (i : Fin (k+1)) := word_eq_of_boundary_choice (T i)
    (tile_boundary_eq_of_interfaces T hk twist x y hx hy hlink hclose i) (hchoice i)
  funext e
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
  · exact congrFun (ht i) e
  · exact hlink i b
  · exact hclose b

end Erdos1016.ExactMaximumSupport.MixedTiles
