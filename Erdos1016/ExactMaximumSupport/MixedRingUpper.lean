import Erdos1016.ExactMaximumSupport.MixedRingHalving
import Erdos1016.ExactMaximumSupport.RingOmega
import Erdos1016.ExactMaximumSupport.RingUpperArithmetic
import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The physical mixed-ring upper bound

All four cycle sectors are counted from the labelled Network model.
The cyclic endpoint sum and fixed-weight arithmetic then give the Horak--Kim bound.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- The paper's doubled integer excess bounds the actual mixed-ring cycle count. -/
theorem ring_doubled_cycle_bound (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (ha : 1≤squares T) :
    2*((ring T hk twist).numCycles : ℤ) ≤ (2 : ℤ)^(weight T+1)+
      RingUpperArithmetic.doubledExcess (squares T) (rungs T) := by
  classical
  let A := Finset.univ.filter fun q => T q=Kind.square
  have hledger := numCycles_le_sector_ledger T hk twist
  have hhalf := full_interface_cycles_card_le_half T hk twist ha
  have hnat : (ring T hk twist).numCycles ≤
      2^(weight T)+squares T+2^(squares T-1)+RingOmega.partialSum A := by
    dsimp only [A]
    omega
  have hc : ((ring T hk twist).numCycles : ℤ) ≤
      (2 : ℤ)^(weight T)+(squares T : ℤ)+2^(squares T-1)+(RingOmega.partialSum A : ℤ) := by
    exact_mod_cast hnat
  have hsum := squares_add_rungs T
  have hsub : k+1-squares T=rungs T := by omega
  have hB := RingOmega.partialSum_bound A
  change 2*(RingOmega.partialSum A : ℤ) ≤
    (2 : ℤ)^(squares T)*(4*(squares T : ℤ)+8*((k+1-squares T : ℕ) : ℤ)+
      ((k+1-squares T : ℕ) : ℤ)*(((k+1-squares T : ℕ) : ℤ)-1))-
      8*(squares T : ℤ)-8*((k+1-squares T : ℕ) : ℤ)+
      ((k+1-squares T : ℕ) : ℤ)*(((k+1-squares T : ℕ) : ℤ)-1) at hB
  rw [hsub] at hB
  have hp : (2 : ℤ)^(squares T)=2*2^(squares T-1) := by
    have he : squares T=squares T-1+1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]
    ring
  unfold RingUpperArithmetic.doubledExcess
  rw [pow_succ]
  nlinarith

/-- A ring without squares satisfies the paper's simpler quadratic excess bound. -/
theorem ring_no_square_cycle_bound (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (ha : squares T=0) :
    (ring T hk twist).numCycles≤2^(weight T)+(weight T)^2 := by
  classical
  let A := Finset.univ.filter fun q => T q=Kind.square
  have hA : A=∅ := Finset.card_eq_zero.mp ha
  have hB : RingOmega.partialSum A=(k+1)*k := by
    rw [hA,RingOmega.partialSum_empty]
    simp
  have hledger := numCycles_le_sector_ledger T hk twist
  have hfull := full_interface_cycles_card_le T hk twist
  have hsum := squares_add_rungs T
  have hweight := weight_eq T
  have hW : weight T=k+1 := by omega
  change (ring T hk twist).numCycles≤2^(weight T)+squares T+
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z}+RingOmega.partialSum A at hledger
  rw [ha,pow_zero] at hfull
  rw [ha,add_zero,hB,hW] at hledger
  rw [hW]
  nlinarith

/-- Every physical mixed ring of weight at least seven obeys the exact Horak--Kim upper bound. -/
theorem ring_numCycles_le_horakKim (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (hW : 7≤weight T) :
    (ring T hk twist).numCycles≤ExactMaximum.horakKim (weight T+1) := by
  by_cases ha : squares T=0
  · exact le_of_lt (RingUpperArithmetic.singleton_cycle_bound _ _ hW
      (ring_no_square_cycle_bound T hk twist ha))
  · have hp : 1≤squares T := Nat.one_le_iff_ne_zero.mpr ha
    have hc := ring_doubled_cycle_bound T hk twist hp
    have hw := weight_eq T
    rw [hw] at hc hW ⊢
    exact RingUpperArithmetic.cycle_bound_of_doubled _ _ _ hp hW hc

/-- The same actual cycle bound is stated in terms of the physical cycle rank. -/
theorem ring_numCycles_le_horakKim_rank (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (hW : 7≤weight T) :
    (ring T hk twist).numCycles≤ExactMaximum.horakKim (networkRank (ring T hk twist)) := by
  rw [ring_rank]
  exact ring_numCycles_le_horakKim T hk twist hW

end Erdos1016.ExactMaximumSupport.MixedTiles
