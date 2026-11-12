import Erdos1016.ExactMaximumSupport.MixedRingLinearization
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Local states when every ring interface is used

The interface-only word has boundary zero at a rung and one at every square vertex.
Subtracting it from an actual even word gives the local matching constraints.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

namespace Kind
/-- The boundary supplied by the two full port pairs of a tile. -/
def fullParity : Kind → Bit
  | rung => 0
  | square => 1

theorem port_parity (t : Kind) (v : t.Vertex) :
    (∑ b : Bool,if t.right b=v then (1 : Bit) else 0)+
      (∑ b : Bool,if t.left b=v then (1 : Bit) else 0)=fullParity t := by
  cases t
  · cases v <;> simp [right,left,fullParity]
  · rcases v with ⟨a,b⟩
    cases a <;> cases b <;> simp [right,left,fullParity]

theorem neg_fullParity (t : Kind) : -fullParity t=fullParity t := by
  cases t <;> decide
end Kind

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Select all interface labels and none of the local tile labels. -/
def interfaceWord : RingEdge T → Bit
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr _ => 1

private theorem port_sum (port : (j : Fin (k+1)) → Bool → (T j).Vertex)
    (i : Fin (k+1)) (v : (T i).Vertex) :
    (∑ j : Fin (k+1),∑ b : Bool,
      if (⟨j,port j b⟩ : Vertex T)=⟨i,v⟩ then (1 : Bit) else 0)=
      ∑ b : Bool,if port i b=v then (1 : Bit) else 0 := by
  classical
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro b _
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro b _
    apply if_neg
    intro h
    exact hji (congrArg Sigma.fst h)
  · simp

/-- The physical interface-only boundary has the expected local parity at every vertex. -/
theorem interfaceWord_boundary (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (i : Fin (k+1)) (v : (T i).Vertex) :
    (ring T hk twist).boundary (interfaceWord T) ⟨i,v⟩=Kind.fullParity (T i) := by
  classical
  let R (j : Fin (k+1)) : Bit := ∑ b : Bool,if right T j b=⟨i,v⟩ then 1 else 0
  let L (j : Fin (k+1)) : Bit := ∑ b : Bool,if left T j b=⟨i,v⟩ then 1 else 0
  have htw : (∑ b : Bool,if left T 0 (twist b)=⟨i,v⟩ then (1 : Bit) else 0)=L 0 :=
    Equiv.sum_comp (twist : Bool ≃ Bool) (fun b => if left T 0 b=⟨i,v⟩ then (1 : Bit) else 0)
  have hb : (ring T hk twist).boundary (interfaceWord T) ⟨i,v⟩=
      ((∑ j : Fin k,R j.castSucc)+R (Fin.last k))+((∑ j : Fin k,L j.succ)+L 0) := by
    rw [Network.boundary_apply]
    simp only [ring,ringSrc,ringDst,chain,chainSrc,chainDst,interfaceWord,
      Fintype.sum_sum_type,Fintype.sum_prod_type,ite_self,Finset.sum_const_zero,zero_add]
    rw [htw]
  rw [hb,←Fin.sum_univ_castSucc]
  rw [add_comm (∑ j : Fin k,L j.succ) (L 0),←Fin.sum_univ_succ]
  have hR := port_sum T (fun j => (T j).right) i v
  have hL := port_sum T (fun j => (T j).left) i v
  change (∑ j,R j)+(∑ j,L j)=Kind.fullParity (T i)
  rw [show (∑ j,R j)=∑ b : Bool,if (T i).right b=v then (1 : Bit) else 0 from hR,
    show (∑ j,L j)=∑ b : Bool,if (T i).left b=v then (1 : Bit) else 0 from hL]
  exact Kind.port_parity (T i) v

/-- An actual even word using all interfaces has the corresponding local tile boundary. -/
theorem full_ring_tile_boundary (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).boundary z=0)
    (hfull : ∀ q b,z (interfaceEdge T q b)=1) (i : Fin (k+1)) :
    (T i).network.boundary (ringTileWord T z i)=fun _ => Kind.fullParity (T i) := by
  have hlink (q : Fin k) (b : Bool) : z (Sum.inl (link T q b))=1 := by
    simpa only [interfaceEdge_castSucc] using hfull q.castSucc b
  have hclose (b : Bool) : z (Sum.inr b)=1 := by
    simpa only [interfaceEdge_last] using hfull (Fin.last k) b
  have hlocal : ringTileWord T (z-interfaceWord T) i=ringTileWord T z i := by
    funext e
    simp only [ringTileWord,Pi.sub_apply,inner,interfaceWord,sub_zero]
  funext v
  have hh := boundary_at_tile_of_zero_interfaces T hk twist (z-interfaceWord T)
    (fun q b => by change z (Sum.inl (link T q b))-1=0; rw [hlink]; exact sub_self _)
    (fun b => by change z (Sum.inr b)-1=0; rw [hclose]; exact sub_self _) i v
  rw [map_sub,hz,Pi.sub_apply,Pi.zero_apply,zero_sub,interfaceWord_boundary,
    Kind.neg_fullParity,hlocal] at hh
  exact hh.symm

end Erdos1016.ExactMaximumSupport.MixedTiles
