import Erdos1016.ExactMaximumSupport.MixedRingOdd
import Erdos1016.ExactMaximum.NetCut

set_option autoImplicit false

/-!
# The common interface parity of a mixed ring

The prefix of the tile sequence has exactly two interfaces in its physical cut.
The actual boundary identity therefore forces common interface parity.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- All interfaces contain an even number of selected physical labels. -/
def HasEvenInterfaces (z : RingEdge T → Bit) : Prop :=
  (∀ i : Fin k, z (Sum.inl (link T i false))+z (Sum.inl (link T i true))=0) ∧
  z (Sum.inr false)+z (Sum.inr true)=0

/-- The two selected labels at any interface have the closing interface's parity. -/
theorem interface_parity (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).boundary z=0) (j : Fin k) :
    z (Sum.inl (link T j false))+z (Sum.inl (link T j true))=
      z (Sum.inr false)+z (Sum.inr true) := by
  classical
  let S : Vertex T → Prop := fun v => v.1.val≤j.val
  have hi (i : Fin (k+1)) (e : (T i).Edge) :
      ¬(ring T hk twist).crosses S (Sum.inl (inner T i e)) := by
    change ¬¬(i.val≤j.val ↔ i.val≤j.val)
    simp
  have hl (i : Fin k) (b : Bool) :
      (ring T hk twist).crosses S (Sum.inl (link T i b)) ↔ i=j := by
    change ¬(i.val≤j.val ↔ i.val+1≤j.val) ↔ i=j
    rw [Fin.ext_iff]
    omega
  have hc (b : Bool) : (ring T hk twist).crosses S (Sum.inr b) := by
    change ¬(k≤j.val ↔ 0≤j.val)
    have := j.isLt
    omega
  have hh := (ring T hk twist).cut_parity S z
  rw [hz] at hh
  simp only [Pi.zero_apply,ite_self,Finset.sum_const_zero] at hh
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_prod_type] at hh
  have hi' (i : Fin (k+1)) (e : (T i).Edge) :
      ¬(ring T hk twist).crosses S (Sum.inl (Sum.inl ⟨i,e⟩)) := hi i e
  have hl' (i : Fin k) (b : Bool) :
      (ring T hk twist).crosses S (Sum.inl (Sum.inr (i,b))) ↔ i=j := hl i b
  simp only [hi',if_false,Finset.sum_const_zero,hl',hc,if_true,zero_add] at hh
  have hs : (∑ i : Fin k, ∑ b : Bool, if i=j then z (Sum.inl (Sum.inr (i,b))) else 0)=
      ∑ b : Bool,z (Sum.inl (Sum.inr (j,b))) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  rw [hs] at hh
  have hsum : (z (Sum.inl (link T j false))+z (Sum.inl (link T j true)))+
      (z (Sum.inr false)+z (Sum.inr true))=0 := by
    simpa [link,add_comm,add_left_comm,add_assoc] using hh.symm
  exact bit_eq_of_add_eq_zero hsum

/-- Every actual even word is in one of the two common-parity sectors. -/
theorem even_or_odd_interfaces (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).boundary z=0) :
    HasEvenInterfaces T z ∨ HasOddInterfaces T z := by
  rcases bit_cases (z (Sum.inr false)+z (Sum.inr true)) with h | h
  · exact Or.inl ⟨fun j => (interface_parity T hk twist z hz j).trans h,h⟩
  · exact Or.inr ⟨fun j => (interface_parity T hk twist z hz j).trans h,h⟩

end Erdos1016.ExactMaximumSupport.MixedTiles
