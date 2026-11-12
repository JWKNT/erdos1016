import Erdos1016.ExactMaximumSupport.MixedTiles

set_option autoImplicit false

/-!
# Exact local parity states of the physical tiles

A rung word is determined by its boundary.
A square word is determined by its boundary and one physical corner label.
These statements apply to every edge word, before any cycle encoding is assumed.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

/-- Either endpoint of a rung sees its single physical label. -/
theorem rung_boundary (z : Kind.rung.network.Word) (b : Bool) :
    Kind.rung.network.boundary z b=z () := by
  cases b <;>
    simp [Network.boundary_apply,Kind.network,Kind.src,Kind.dst]

/-- A square boundary at its left vertex is the sum of its two row labels. -/
theorem square_boundary_left (z : Kind.square.network.Word) (b : Bool) :
    Kind.square.network.boundary z (false,b)=z (b,false)+z (b,true) := by
  cases b <;>
    simp [Network.boundary_apply,Kind.network,Kind.src,Kind.dst,Fintype.sum_prod_type,add_comm]

/-- A square boundary at its right vertex is the sum of its two column labels. -/
theorem square_boundary_right (z : Kind.square.network.Word) (b : Bool) :
    Kind.square.network.boundary z (true,b)=z (false,b)+z (true,b) := by
  cases b <;>
    simp [Network.boundary_apply,Kind.network,Kind.src,Kind.dst,Fintype.sum_prod_type,add_comm]

/-- The physical rung word is uniquely determined by its boundary. -/
theorem rung_word_eq_of_boundary {x y : Kind.rung.network.Word}
    (h : Kind.rung.network.boundary x=Kind.rung.network.boundary y) : x=y := by
  have hh := congrFun h false
  rw [rung_boundary,rung_boundary] at hh
  funext e
  cases e
  exact hh

/-- One corner label resolves the two possible square boundary states. -/
theorem square_word_eq_of_boundary_corner {x y : Kind.square.network.Word}
    (h : Kind.square.network.boundary x=Kind.square.network.boundary y)
    (h00 : x (false,false)=y (false,false)) : x=y := by
  have h01 := congrFun h (false,false)
  have h10 := congrFun h (true,false)
  have h11 := congrFun h (false,true)
  rw [square_boundary_left,square_boundary_left,h00] at h01
  rw [square_boundary_right,square_boundary_right,h00] at h10
  have h01' : x (false,true)=y (false,true) := add_left_cancel h01
  have h10' : x (true,false)=y (true,false) := add_left_cancel h10
  rw [square_boundary_left,square_boundary_left,h10'] at h11
  have h11' : x (true,true)=y (true,true) := add_left_cancel h11
  funext e
  rcases e with ⟨a,b⟩
  cases a <;> cases b
  · exact h00
  · exact h01'
  · exact h10'
  · exact h11'

/-- A rung needs no extra bit; a square needs one corner bit. -/
abbrev StateChoice : Kind → Type
  | Kind.rung => Unit
  | Kind.square => Bit

instance (t : Kind) : Fintype (StateChoice t) := by cases t <;> infer_instance

/-- Read the extra local information from an actual physical edge word. -/
def stateChoice : (t : Kind) → t.network.Word → StateChoice t
  | Kind.rung, _ => ()
  | Kind.square, z => z (false,false)

/-- Boundary and the stated local choice determine every physical label. -/
theorem word_eq_of_boundary_choice (t : Kind) {x y : t.network.Word}
    (h : t.network.boundary x=t.network.boundary y)
    (hc : stateChoice t x=stateChoice t y) : x=y := by
  cases t
  · exact rung_word_eq_of_boundary h
  · exact square_word_eq_of_boundary_corner h hc

/-- The local choice count is exactly the paper's factor one or two. -/
theorem stateChoice_card (t : Kind) : Nat.card (StateChoice t)=2^(t.weight-1) := by
  cases t <;> simp [StateChoice,Kind.weight,Bit]

/-- Any fixed physical boundary has at most one rung state or two square states. -/
theorem boundary_fiber_card_le (t : Kind) (b : t.network.Demand) :
    Nat.card {z : t.network.Word // t.network.boundary z=b} ≤ 2^(t.weight-1) := by
  let f : {z : t.network.Word // t.network.boundary z=b} → StateChoice t :=
    fun z => stateChoice t z.1
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (word_eq_of_boundary_choice t (x.2.trans y.2.symm) h)
  have hh := Nat.card_le_card_of_injective f hi
  simpa only [stateChoice_card] using hh

end Erdos1016.ExactMaximumSupport.MixedTiles
