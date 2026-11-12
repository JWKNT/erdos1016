import Erdos1016.ExactMaximumSupport.NetworkPathOrder

set_option autoImplicit false

/-!
# Ordered coordinates for the inner vertices of an actual path

Removing the two endpoint positions gives exactly the selected-degree-two vertices.
The equivalence supplies the ordered rail coordinates for the matching permutation.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order
open BoundaryTrace BoundaryTrace.Network
variable {V E : Type*} [Fintype V] [Fintype E] {N : Network V E}
variable {s t : V} {P : N.Word} (O : NetworkPathOrder.Order N s t P)

/-- The inner positions in their actual path order. -/
def innerVertex (i : Fin O.innerCount) : V := O.vertex i.succ.castSucc

omit [Fintype V] [Fintype E] in
theorem innerVertex_ne_left (i : Fin O.innerCount) : O.innerVertex i ≠ s := by
  intro h
  have hh := O.vertex_injective (h.trans O.first.symm)
  have hv := congrArg Fin.val hh
  change i.val+1 = 0 at hv
  omega

omit [Fintype V] [Fintype E] in
theorem innerVertex_ne_right (i : Fin O.innerCount) : O.innerVertex i ≠ t := by
  intro h
  have hh := O.vertex_injective (h.trans O.last.symm)
  have hv := congrArg Fin.val hh
  change i.val+1 = O.innerCount+1 at hv
  have hi := i.isLt
  omega

omit [Fintype V] [Fintype E] in
theorem innerVertex_injective : Function.Injective O.innerVertex := by
  intro i j h
  have hh := O.vertex_injective h
  have hv := congrArg Fin.val hh
  apply Fin.ext
  change i.val+1 = j.val+1 at hv
  omega

omit [Fintype V] in
/-- Every inner ordered vertex has degree exactly two in the selected word. -/
theorem innerVertex_degree (hP : N.IsPathWord s t P) (i : Fin O.innerCount) :
    N.deg P (O.innerVertex i) = 2 := by
  have hp := O.vertex_pos i.succ.castSucc
  rcases hP.2.2.2.1 (O.innerVertex i) (O.innerVertex_ne_left i) (O.innerVertex_ne_right i) with h | h
  · change 0 < N.deg P (O.innerVertex i) at hp
    omega
  · exact h

omit [Fintype V] in
/-- The inner ordered vertices exhaust the actual degree-two support. -/
theorem exists_innerVertex (hP : N.IsPathWord s t P) (v : V) (hv : N.deg P v = 2) :
    ∃ i : Fin O.innerCount, O.innerVertex i = v := by
  have hvs : v ≠ s := by intro h; subst v; have := hP.2.1; omega
  have hvt : v ≠ t := by intro h; subst v; have := hP.2.2.1; omega
  obtain ⟨j,hj⟩ := (O.vertex_support v).mp (by omega)
  have hj0 : j.val ≠ 0 := by
    intro h
    have he : j = 0 := Fin.ext h
    rw [he,O.first] at hj
    exact hvs hj.symm
  have hjlast : j.val ≠ O.innerCount+1 := by
    intro h
    have he : j = Fin.last (O.innerCount+1) := Fin.ext h
    rw [he,O.last] at hj
    exact hvt hj.symm
  have hjlt := j.isLt
  let i : Fin O.innerCount := ⟨j.val-1,by omega⟩
  have hi : i.succ.castSucc = j := by
    apply Fin.ext
    change (j.val-1)+1 = j.val
    omega
  exact ⟨i,by unfold innerVertex; rw [hi]; exact hj⟩

/-- An order-preserving physical identification of inner positions with the path's inner vertices. -/
def innerEquiv (hP : N.IsPathWord s t P) :
    Fin O.innerCount ≃ {v : V // N.deg P v = 2} :=
  Equiv.ofBijective (fun i => ⟨O.innerVertex i,O.innerVertex_degree hP i⟩) (by
    constructor
    · intro i j h
      exact O.innerVertex_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨i,hi⟩ := O.exists_innerVertex hP v.1 v.2
      exact ⟨i,Subtype.ext hi⟩)

@[simp] theorem innerEquiv_apply (hP : N.IsPathWord s t P) (i : Fin O.innerCount) :
    (O.innerEquiv hP i).1 = O.innerVertex i := rfl

/-- The actual number of inner vertices is the length parameter of the order. -/
theorem inner_card (hP : N.IsPathWord s t P) :
    Nat.card {v : V // N.deg P v = 2} = O.innerCount := by
  rw [← Nat.card_congr (O.innerEquiv hP)]
  simp

end Erdos1016.ExactMaximumSupport.NetworkPathOrder.Order
