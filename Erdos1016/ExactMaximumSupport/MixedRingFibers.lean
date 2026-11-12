import Erdos1016.ExactMaximumSupport.MixedRingEncoding

set_option autoImplicit false

/-!
# Fixed-interface fibers supported on specified tiles

The actual even-word encoding restricts to the tiles on which a word is allowed.
Every permitted square contributes one bit; permitted rungs contribute no bit.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Physical local words vanish outside the specified tile set. -/
def WithinTiles (I : Finset (Fin (k+1))) (z : RingEdge T → Bit) : Prop :=
  ∀ i, i∉I → ringTileWord T z i=0

/-- Only square tiles require an independent local parity choice. -/
theorem sum_local_choices (I : Finset (Fin (k+1))) :
    (∑ i ∈ I, ((T i).weight-1))=(I.filter fun i => T i=Kind.square).card := by
  classical
  have h (i : Fin (k+1)) : (T i).weight-1=if T i=Kind.square then 1 else 0 := by
    cases ht : T i <;> simp [Kind.weight]
  simp_rw [h]
  rw [Finset.card_filter]

/-- The restricted local code has one bit per permitted square. -/
theorem localChoice_card (I : Finset (Fin (k+1))) :
    Nat.card ((i : I) → StateChoice (T i))=2^((I.filter fun i => T i=Kind.square).card) := by
  classical
  rw [Nat.card_pi]
  simp_rw [stateChoice_card]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  calc
    (∑ i : I, ((T i).weight-1)) = ∑ i ∈ I, ((T i).weight-1) :=
      Finset.sum_coe_sort I (fun i => (T i).weight-1)
    _ = _ := sum_local_choices T I

/-- Prescribed interfaces and prescribed active tiles give the exact local fiber bound. -/
theorem fixed_interface_fiber_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (I : Finset (Fin (k+1))) (links : Fin k → Bool → Bit) (closing : Bool → Bit) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧
      (∀ i b,z (Sum.inl (link T i b))=links i b) ∧
      (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z} ≤
      2^((I.filter fun i => T i=Kind.square).card) := by
  classical
  let C := {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧
      (∀ i b,z (Sum.inl (link T i b))=links i b) ∧
      (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z}
  let f : C → ((i : I) → StateChoice (T i)) :=
    fun z i => stateChoice (T i) (ringTileWord T z.1 i)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply even_word_eq_of_encoding T hk twist x.1 y.1 x.2.1 y.2.1
    · intro i b
      exact (x.2.2.1 i b).trans (y.2.2.1 i b).symm
    · intro b
      exact (x.2.2.2.1 b).trans (y.2.2.2.1 b).symm
    · intro i
      by_cases hi : i∈I
      · exact congrFun h ⟨i,hi⟩
      · rw [x.2.2.2.2 i hi,y.2.2.2.2 i hi]
  simpa only [localChoice_card] using Nat.card_le_card_of_injective f hf

/-- The same fiber bound applies to actual cycles. -/
theorem fixed_interface_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (I : Finset (Fin (k+1))) (links : Fin k → Bool → Bit) (closing : Bool → Bit) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧
      (∀ i b,z (Sum.inl (link T i b))=links i b) ∧
      (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z} ≤
      2^((I.filter fun i => T i=Kind.square).card) := by
  let f : {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧
      (∀ i b,z (Sum.inl (link T i b))=links i b) ∧
      (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z} →
      {z : (ring T hk twist).Word //
      (ring T hk twist).boundary z=0 ∧
      (∀ i b,z (Sum.inl (link T i b))=links i b) ∧
      (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z} :=
    fun z => ⟨z.1,z.2.1.boundary_eq_zero,z.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh
  exact (Nat.card_le_card_of_injective f hf).trans
    (fixed_interface_fiber_card_le T hk twist I links closing)

end Erdos1016.ExactMaximumSupport.MixedTiles
