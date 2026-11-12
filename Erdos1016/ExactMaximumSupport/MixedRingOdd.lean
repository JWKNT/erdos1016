import Erdos1016.ExactMaximumSupport.MixedRingEncoding

set_option autoImplicit false

/-!
# The odd interface sector of a physical mixed ring

An odd interface uses exactly one of its two physical labels.
The interface choices and local square bits give an actual injective encoding.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Each interface has odd selected parity. -/
def HasOddInterfaces (z : RingEdge T → Bit) : Prop :=
  (∀ i : Fin k, z (Sum.inl (link T i false))+z (Sum.inl (link T i true))=1) ∧
  z (Sum.inr false)+z (Sum.inr true)=1

/-- One bit per interface and one bit per square. -/
abbrev OddEncoding := (Fin k → Bit) × Bit × ((i : Fin (k+1)) → StateChoice (T i))

/-- The code is read directly from physical edge labels. -/
def oddEncoding (z : RingEdge T → Bit) : OddEncoding T :=
  (fun i => z (Sum.inl (link T i false)), z (Sum.inr false),
    fun i => stateChoice (T i) (ringTileWord T z i))

/-- The encoding identifies any two even words in the odd interface sector. -/
theorem oddEncoding_injective_on (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    {x y : (ring T hk twist).Word}
    (hx : (ring T hk twist).boundary x=0) (hy : (ring T hk twist).boundary y=0)
    (hxo : HasOddInterfaces T x) (hyo : HasOddInterfaces T y)
    (h : oddEncoding T x=oddEncoding T y) : x=y := by
  have hi : ∀ i, x (Sum.inl (link T i false))=y (Sum.inl (link T i false)) :=
    fun i => congrFun (congrArg Prod.fst h) i
  have hc : x (Sum.inr false)=y (Sum.inr false) := congrArg (fun z => z.2.1) h
  have ht : ∀ i, stateChoice (T i) (ringTileWord T x i)=
      stateChoice (T i) (ringTileWord T y i) :=
    fun i => congrFun (congrArg (fun z => z.2.2) h) i
  apply even_word_eq_of_encoding T hk twist x y hx hy _ _ ht
  · intro i b
    cases b
    · exact hi i
    · have hh := (hxo.1 i).trans (hyo.1 i).symm
      rw [hi i] at hh
      exact add_left_cancel hh
  · intro b
    cases b
    · exact hc
    · have hh := hxo.2.trans hyo.2.symm
      rw [hc] at hh
      exact add_left_cancel hh

/-- Tile weights count the interface bits and the extra square bits. -/
theorem weight_eq_interfaces_add_choices :
    weight T=(k+1)+∑ i : Fin (k+1), ((T i).weight-1) := by
  have h (i : Fin (k+1)) : (T i).weight=1+((T i).weight-1) := by
    have := Kind.weight_pos (T i)
    omega
  unfold weight
  calc
    ∑ i : Fin (k+1), (T i).weight = ∑ i : Fin (k+1), (1+((T i).weight-1)) :=
      Finset.sum_congr rfl (fun i _ => h i)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The exact finite code space has the odd-sector leading size. -/
theorem oddEncoding_card : Nat.card (OddEncoding T)=2^(weight T) := by
  classical
  rw [Nat.card_prod,Nat.card_fun,Nat.card_prod,Nat.card_pi]
  have hb : Nat.card Bit=2 := by simp [Bit]
  have hf : Nat.card (Fin k)=k := by simp [Nat.card_eq_fintype_card]
  rw [hb,hf]
  simp_rw [stateChoice_card]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [weight_eq_interfaces_add_choices T]
  simp only [pow_add,pow_one]
  ring

/-- All actual even words in the odd sector satisfy the leading-term bound. -/
theorem odd_even_words_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧ HasOddInterfaces T z} ≤ 2^(weight T) := by
  let f : {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧ HasOddInterfaces T z} → OddEncoding T :=
    fun z => oddEncoding T z.1
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (oddEncoding_injective_on T hk twist x.2.1 y.2.1 x.2.2 y.2.2 h)
  simpa only [oddEncoding_card] using Nat.card_le_card_of_injective f hf

/-- In particular, the actual odd-sector cycles contribute at most `2^weight`. -/
theorem odd_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasOddInterfaces T z} ≤ 2^(weight T) := by
  let f : {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasOddInterfaces T z} →
      {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧ HasOddInterfaces T z} :=
    fun z => ⟨z.1,z.2.1.boundary_eq_zero,z.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh
  exact (Nat.card_le_card_of_injective f hf).trans
    (odd_even_words_card_le T hk twist)

end Erdos1016.ExactMaximumSupport.MixedTiles
