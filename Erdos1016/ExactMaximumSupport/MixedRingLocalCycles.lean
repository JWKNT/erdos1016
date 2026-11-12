import Erdos1016.ExactMaximumSupport.MixedRingEncoding
import Erdos1016.ExactMaximum.NetEmbed

set_option autoImplicit false

/-!
# Cycles that use no interface of a physical mixed ring

A nonzero local even word is impossible in a rung and unique in a square.
Cycle minimality then locates every interface-free cycle in one square tile.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

/-- A nonzero even tile word can occur only in a square. -/
theorem nonzero_even_tile_is_square (t : Kind) (z : t.network.Word)
    (hz : t.network.boundary z=0) (hne : z≠0) : t=Kind.square := by
  cases t
  · exfalso
    apply hne
    exact rung_word_eq_of_boundary (by simpa using hz)
  · rfl

/-- Each tile has at most one nonzero even physical word. -/
theorem nonzero_even_tile_unique (t : Kind) {x y : t.network.Word}
    (hx : t.network.boundary x=0) (hy : t.network.boundary y=0)
    (hxn : x≠0) (hyn : y≠0) : x=y := by
  have ht := nonzero_even_tile_is_square t x hx hxn
  subst t
  have hcorner (z : Kind.square.network.Word) (hz : Kind.square.network.boundary z=0)
      (hn : z≠0) : z (false,false)=1 := by
    rcases bit_cases (z (false,false)) with h | h
    · exact False.elim (hn (square_word_eq_of_boundary_corner (by simpa using hz) h))
    · exact h
  exact square_word_eq_of_boundary_corner (hx.trans hy.symm)
    ((hcorner x hx hxn).trans (hcorner y hy hyn).symm)

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- No ordinary or closing interface label is selected. -/
def HasZeroInterfaces (z : RingEdge T → Bit) : Prop :=
  (∀ i b, z (Sum.inl (link T i b))=0) ∧ ∀ b,z (Sum.inr b)=0

/-- The actual physical embedding of one tile in its ring. -/
def ringTileEmbed (hk : 1 ≤ k) (twist : Equiv.Perm Bool) (i : Fin (k+1)) :
    Network.Embed (T i).network (ring T hk twist) where
  φ := fun v => ⟨i,v⟩
  ψ := fun e => Sum.inl (inner T i e)
  φ_inj := by intro u v h; simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  ψ_inj := by
    intro e f h
    have hh := Sum.inl.inj (Sum.inl.inj h)
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
  src := fun _ => rfl
  dst := fun _ => rfl

/-- An interface-free even ring word restricts to an even word on every tile. -/
theorem local_boundary_zero (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).boundary z=0)
    (hzero : HasZeroInterfaces T z) (i : Fin (k+1)) :
    (T i).network.boundary (ringTileWord T z i)=0 := by
  funext v
  have h := boundary_at_tile_of_zero_interfaces T hk twist z hzero.1 hzero.2 i v
  rw [hz,Pi.zero_apply] at h
  exact h.symm

/-- A nonzero interface-free word has a nonzero local tile restriction. -/
theorem exists_nonzero_tile (z : RingEdge T → Bit) (hne : z≠0)
    (hzero : HasZeroInterfaces T z) : ∃ i,ringTileWord T z i≠0 := by
  by_contra h
  push_neg at h
  apply hne
  funext e
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | b
  · exact congrFun (h i) e
  · exact hzero.1 i b
  · exact hzero.2 b

/-- A nonzero local piece of an interface-free cycle is the whole physical cycle. -/
theorem cycle_eq_tile_push (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z)
    (hzero : HasZeroInterfaces T z) (i : Fin (k+1))
    (hne : ringTileWord T z i≠0) :
    z=(ringTileEmbed T hk twist i).push (ringTileWord T z i) := by
  let R := ringTileEmbed T hk twist i
  have hs : (ring T hk twist).IsSubword (R.push (ringTileWord T z i)) z := by
    intro e he
    obtain ⟨f,rfl⟩ := R.within_push (ringTileWord T z i) e he
    rw [R.push_apply] at he
    exact he
  have hb : (ring T hk twist).boundary (R.push (ringTileWord T z i))=0 :=
    (R.boundary_push_eq_zero_iff _).2
      (local_boundary_zero T hk twist z hz.boundary_eq_zero hzero i)
  have hn : R.push (ringTileWord T z i)≠0 := by
    intro h
    apply hne
    apply R.push_injective
    simpa only [R.push_zero] using h
  exact (hz.eq_of_even_subword hs hb hn).symm

/-- Two interface-free cycles using the same tile are equal. -/
theorem zero_interface_cycles_unique_at_tile (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    {x y : (ring T hk twist).Word}
    (hx : (ring T hk twist).IsCycleWord x) (hy : (ring T hk twist).IsCycleWord y)
    (hxz : HasZeroInterfaces T x) (hyz : HasZeroInterfaces T y)
    (i : Fin (k+1)) (hxn : ringTileWord T x i≠0) (hyn : ringTileWord T y i≠0) : x=y := by
  have ht := nonzero_even_tile_unique (T i)
    (local_boundary_zero T hk twist x hx.boundary_eq_zero hxz i)
    (local_boundary_zero T hk twist y hy.boundary_eq_zero hyz i) hxn hyn
  rw [cycle_eq_tile_push T hk twist x hx hxz i hxn,
    cycle_eq_tile_push T hk twist y hy hyz i hyn,ht]

/-- There are at most as many interface-free cycles as square tiles. -/
theorem zero_interface_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasZeroInterfaces T z} ≤ squares T := by
  classical
  let C := {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasZeroInterfaces T z}
  have hex (z : C) : ∃ i,ringTileWord T z.1 i≠0 :=
    exists_nonzero_tile T z.1 z.2.1.1 z.2.2
  let idx (z : C) := Classical.choose (hex z)
  have hn (z : C) : ringTileWord T z.1 (idx z)≠0 := Classical.choose_spec (hex z)
  let f : C → {i : Fin (k+1) // T i=Kind.square} := fun z => ⟨idx z,
    nonzero_even_tile_is_square (T (idx z)) _
      (local_boundary_zero T hk twist z.1 z.2.1.boundary_eq_zero z.2.2 (idx z)) (hn z)⟩
  have hf : Function.Injective f := by
    intro x y h
    have hi : idx x=idx y := congrArg Subtype.val h
    apply Subtype.ext
    exact zero_interface_cycles_unique_at_tile T hk twist x.2.1 y.2.1 x.2.2 y.2.2
      (idx x) (hn x) (by rw [hi]; exact hn y)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [C,Nat.card_eq_fintype_card,Fintype.card_subtype,squares] using hh

end Erdos1016.ExactMaximumSupport.MixedTiles
