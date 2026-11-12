import Erdos1016.ExactMaximumSupport.MixedRingTransport
import Erdos1016.ExactMaximumSupport.MixedRingSectors

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Halving the all-interface sector

The nonidentity two-rail transport determines one missing square matching.
The resulting physical cycle encoding omits one square bit.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- All local choices except one determine an all-interface cycle. -/
theorem full_cycle_eq_of_other_choices (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    {x y : (ring T hk twist).Word}
    (hx : (ring T hk twist).IsCycleWord x) (hy : (ring T hk twist).IsCycleWord y)
    (hxf : HasFullInterfaces T x) (hyf : HasFullInterfaces T y) (i : Fin (k+1))
    (hother : ∀ j,j≠i → stateChoice (T j) (ringTileWord T x j)=
      stateChoice (T j) (ringTileWord T y j)) : x=y := by
  have hbx (j : Fin (k+1)) := full_ring_tile_boundary T hk twist x hx.boundary_eq_zero hxf j
  have hby (j : Fin (k+1)) := full_ring_tile_boundary T hk twist y hy.boundary_eq_zero hyf j
  have hwords (j : Fin (k+1)) (hji : j≠i) : ringTileWord T x j=ringTileWord T y j :=
    word_eq_of_boundary_choice (T j) ((hbx j).trans (hby j).symm) (hother j hji)
  have hprod : railPrefix (tileRail T x) (k+1)=railPrefix (tileRail T y) (k+1) := by
    apply mul_left_cancel (a := twist)
    exact bool_perm_eq_of_ne_one _ _
      (full_cycle_transport_ne_one T hk twist x hx hxf)
      (full_cycle_transport_ne_one T hk twist y hy hyf)
  have hi : tileRail T x i.val=tileRail T y i.val :=
    railPrefix_cancel_one (tileRail T x) (tileRail T y) (k+1) i.val i.isLt
      (fun j hj hji => by
        let q : Fin (k+1) := ⟨j,hj⟩
        have hq : q≠i := fun h => hji (congrArg Fin.val h)
        change tileRail T x q.val=tileRail T y q.val
        rw [tileRail_at,tileRail_at,hwords q hq]) hprod
  rw [tileRail_at,tileRail_at] at hi
  have hwi := Kind.full_word_eq_of_railPermutation (T i) (hbx i) (hby i) hi
  apply even_word_eq_of_encoding T hk twist x y hx.boundary_eq_zero hy.boundary_eq_zero
  · intro j b
    have hxx := hxf j.castSucc b
    have hyy := hyf j.castSucc b
    simpa only [interfaceEdge_castSucc] using hxx.trans hyy.symm
  · intro b
    have hxx := hxf (Fin.last k) b
    have hyy := hyf (Fin.last k) b
    simpa only [interfaceEdge_last] using hxx.trans hyy.symm
  · intro j
    by_cases hji : j=i
    · subst j
      rw [hwi]
    · exact hother j hji

/-- Omitting a specified square bit halves the actual all-interface cycle count. -/
theorem full_interface_cycles_card_le_half_at (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (i : Fin (k+1)) (hi : T i=Kind.square) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z} ≤ 2^(squares T-1) := by
  classical
  let I := Finset.univ.erase i
  let C := {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z}
  let f : C → ((j : I) → StateChoice (T j)) :=
    fun z j => stateChoice (T j) (ringTileWord T z.1 j)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply full_cycle_eq_of_other_choices T hk twist x.2.1 y.2.1 x.2.2 y.2.2 i
    intro j hji
    exact congrFun h ⟨j,Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩⟩
  have hb := Nat.card_le_card_of_injective f hf
  rw [localChoice_card] at hb
  have hfilter : I.filter (fun j => T j=Kind.square)=
      (Finset.univ.filter fun j => T j=Kind.square).erase i := by
    ext j
    simp only [I,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and]
    tauto
  have hmem : i∈(Finset.univ.filter fun j => T j=Kind.square) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  rw [hfilter,Finset.card_erase_of_mem hmem] at hb
  exact hb

/-- Every mixed ring with a square has at most half of its full-interface local choices as cycles. -/
theorem full_interface_cycles_card_le_half (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (ha : 1≤squares T) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z} ≤ 2^(squares T-1) := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<(Finset.univ.filter fun j => T j=Kind.square).card from ha)
  exact full_interface_cycles_card_le_half_at T hk twist i (Finset.mem_filter.mp hi).2

end Erdos1016.ExactMaximumSupport.MixedTiles
