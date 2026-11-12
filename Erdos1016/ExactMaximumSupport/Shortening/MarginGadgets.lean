import Erdos1016.ExactMaximumSupport.Shortening.MarginFewCycles
import Erdos1016.ExactMaximum.Gadgets

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Actual pole gadgets at any positive margin, retaining their physical path/cycle injections. -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.MarginGadgets
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ExactMaximum
local instance gadgetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The uniform actual weak-pole bound at a specified real margin. -/
def Bound (ε : ℝ) (K : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
    N.IsWeakPole → ∀s t,N.IsPort s → N.IsPort t → s≠t →
    (1/2+ε)*(2:ℝ)^networkRank N≤N.numPaths s t →
    N.numCycles^2≤K*2^networkRank N

/-- The third-pair gadget, without a fixed numerical tolerance. -/
theorem gadget_third_pair {ε : ℝ} (hε : 0 ≤ ε) {K : ℕ} (hF : Bound ε K) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.IsWeakPole) {a b c : V} (ha : N.IsPort a) (hb : N.IsPort b)
    (hc : N.IsPort c) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hmany : (1+2*ε) * (2:ℝ)^networkRank N ≤ (N.numPaths a c : ℝ) + N.numPaths b c) :
    N.numPaths a b ^ 2 ≤ 2 * K * 2 ^ networkRank N := by
  have hpole := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank := N.networkRank_addVertex_le a b
  have hpaths := N.numPaths_add_le_numPaths_addVertex a b c
  have hcyc := N.numPaths_le_numCycles_addVertex a b
  have hpow : 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) :=
    Nat.pow_le_pow_right (by norm_num) hrank
  have hF' := hF (Option V) (E ⊕ Bool) (N.addVertex a b) hpole none (some c)
    (N.isPort_addVertex_none a b) (N.isPort_addVertex_some a b hca hcb hc)
    (fun k => Option.noConfusion k) (by
      have hpowR : (2:ℝ)^networkRank (N.addVertex a b) ≤ 2*(2:ℝ)^networkRank N := by
        rw [pow_succ] at hpow
        exact_mod_cast (show 2^networkRank (N.addVertex a b)≤2*2^networkRank N by omega)
      have hpR := hpaths
      have hpR' : (N.numPaths a c : ℝ) + N.numPaths b c ≤ ((N.addVertex a b).numPaths none (some c) : ℝ) := by
        exact_mod_cast hpR
      calc
        (1/2+ε)*(2:ℝ)^networkRank (N.addVertex a b)
          ≤ (1/2+ε)*(2*(2:ℝ)^networkRank N) :=
            mul_le_mul_of_nonneg_left hpowR (by positivity)
        _ ≤ _ := by nlinarith)
  calc N.numPaths a b ^ 2 ≤ (N.addVertex a b).numCycles ^ 2 := Nat.pow_le_pow_left hcyc 2
    _ ≤ K * 2 ^ networkRank (N.addVertex a b) := hF'
    _ ≤ K * 2 ^ (networkRank N + 1) := Nat.mul_le_mul_left K hpow
    _ = 2 * K * 2 ^ networkRank N := by
        rw [pow_succ]
        ring

/-- The opposite-pair gadget at the specified real margin. -/
theorem gadget_opposite_pair {ε : ℝ} (hε : 0 ≤ ε) {K : ℕ} (hF : Bound ε K) {V E : Type} [Fintype V]
    [Fintype E] (N : Network V E) (hN : N.IsWeakPole) {a b c d : V} (ha : N.IsPort a)
    (hb : N.IsPort b) (hc : N.IsPort c) (hd : N.IsPort d) (hab : a ≠ b) (hcd : c ≠ d)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hmany : (1+2*ε) * (2:ℝ)^networkRank N ≤
      (N.numPaths c d : ℝ) + N.numPathPairs c a b d + N.numPathPairs c b a d) :
    N.numPaths a b ^ 2 ≤ 2 * K * 2 ^ networkRank N := by
  have hpole := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank := N.networkRank_addVertex_le a b
  have hpaths := N.numPaths_pairs_le_numPaths_addVertex a b c d
  have hcyc := N.numPaths_le_numCycles_addVertex a b
  have hpow : 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) :=
    Nat.pow_le_pow_right (by norm_num) hrank
  have hF' := hF (Option V) (E ⊕ Bool) (N.addVertex a b) hpole (some c) (some d)
    (N.isPort_addVertex_some a b hca hcb hc) (N.isPort_addVertex_some a b hda hdb hd)
    (fun k => hcd (Option.some.inj k)) (by
      have hpowR : (2:ℝ)^networkRank (N.addVertex a b) ≤ 2*(2:ℝ)^networkRank N := by
        rw [pow_succ] at hpow
        exact_mod_cast (show 2^networkRank (N.addVertex a b)≤2*2^networkRank N by omega)
      have hpR := hpaths
      have hpR' : (N.numPaths c d : ℝ) + N.numPathPairs c a b d + N.numPathPairs c b a d ≤ ((N.addVertex a b).numPaths (some c) (some d) : ℝ) := by
        exact_mod_cast hpR
      calc
        (1/2+ε)*(2:ℝ)^networkRank (N.addVertex a b)
          ≤ (1/2+ε)*(2*(2:ℝ)^networkRank N) :=
            mul_le_mul_of_nonneg_left hpowR (by positivity)
        _ ≤ _ := by nlinarith)
  calc N.numPaths a b ^ 2 ≤ (N.addVertex a b).numCycles ^ 2 := Nat.pow_le_pow_left hcyc 2
    _ ≤ K * 2 ^ networkRank (N.addVertex a b) := hF'
    _ ≤ K * 2 ^ (networkRank N + 1) := Nat.mul_le_mul_left K hpow
    _ = 2 * K * 2 ^ networkRank N := by
        rw [pow_succ]
        ring

/-- The two-new-vertices gadget bounds the sum of the two crossing forest sectors. -/
theorem gadget_cross_pairs {ε : ℝ} (hε : 0 ≤ ε) {K : ℕ} (hF : Bound ε K) {V E : Type} [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.IsWeakPole) {a b c d : V} (ha : N.IsPort a) (hb : N.IsPort b)
    (hc : N.IsPort c) (hd : N.IsPort d) (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a)
    (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (hmany : (2+4*ε) * (2:ℝ)^networkRank N ≤
      (N.numPaths a c : ℝ) + N.numPaths b c + (N.numPaths a d : ℝ) + N.numPaths b d) :
    (N.numPathPairs c a b d + N.numPathPairs c b a d) ^ 2 ≤ 4 * K * 2 ^ networkRank N := by
  -- the first new vertex, at `a` and `b`
  have hpole₁ := N.isWeakPole_addVertex a b hN hab ha hb
  have hrank₁ := N.networkRank_addVertex_le a b
  have hc₁ := N.isPort_addVertex_some a b hca hcb hc
  have hd₁ := N.isPort_addVertex_some a b hda hdb hd
  have hz₁ := N.isPort_addVertex_none a b
  have hcd₁ : (some c : Option V) ≠ some d := fun k => hcd (Option.some.inj k)
  -- the second new vertex, at `c` and `d`
  have hpole₂ := (N.addVertex a b).isWeakPole_addVertex (some c) (some d) hpole₁ hcd₁ hc₁ hd₁
  have hrank₂ := (N.addVertex a b).networkRank_addVertex_le (some c) (some d)
  have hw₂ := (N.addVertex a b).isPort_addVertex_none (some c) (some d)
  have hz₂ := (N.addVertex a b).isPort_addVertex_some (some c) (some d)
    (fun k : (none : Option V) = some c => Option.noConfusion k)
    (fun k : (none : Option V) = some d => Option.noConfusion k) hz₁
  -- the paths between the two new vertices
  have hp₂ := (N.addVertex a b).numPaths_add_le_numPaths_addVertex (some c) (some d) none
  rw [numPaths_symm (N.addVertex a b) (some c) none,
    numPaths_symm (N.addVertex a b) (some d) none] at hp₂
  have hpc := N.numPaths_add_le_numPaths_addVertex a b c
  have hpd := N.numPaths_add_le_numPaths_addVertex a b d
  -- the cycles through the two new vertices
  have hcyc₂ := (N.addVertex a b).numPaths_le_numCycles_addVertex (some c) (some d)
  have hpairs := N.numPaths_pairs_le_numPaths_addVertex a b c d
  have hpow : 2 ^ networkRank ((N.addVertex a b).addVertex (some c) (some d)) ≤
      2 ^ (networkRank N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF' := hF (Option (Option V)) ((E ⊕ Bool) ⊕ Bool)
    ((N.addVertex a b).addVertex (some c) (some d)) hpole₂ none (some none) hw₂ hz₂
    (fun k => Option.noConfusion k) (by
      have hpowR : (2:ℝ)^networkRank ((N.addVertex a b).addVertex (some c) (some d))
          ≤ 4*(2:ℝ)^networkRank N := by
        rw [pow_succ,pow_succ] at hpow
        exact_mod_cast (show 2^networkRank ((N.addVertex a b).addVertex (some c) (some d))≤4*2^networkRank N by omega)
      have hpR : (N.numPaths a c : ℝ)+N.numPaths b c+N.numPaths a d+N.numPaths b d ≤
          ((N.addVertex a b).addVertex (some c) (some d)).numPaths none (some none) := by
        exact_mod_cast (show N.numPaths a c+N.numPaths b c+N.numPaths a d+N.numPaths b d ≤
          ((N.addVertex a b).addVertex (some c) (some d)).numPaths none (some none) by omega)
      calc
        (1/2+ε)*(2:ℝ)^networkRank ((N.addVertex a b).addVertex (some c) (some d))
          ≤ (1/2+ε)*(4*(2:ℝ)^networkRank N) :=
            mul_le_mul_of_nonneg_left hpowR (by positivity)
        _ ≤ _ := by nlinarith)
  calc (N.numPathPairs c a b d + N.numPathPairs c b a d) ^ 2
      ≤ ((N.addVertex a b).addVertex (some c) (some d)).numCycles ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
    _ ≤ K * 2 ^ networkRank ((N.addVertex a b).addVertex (some c) (some d)) := hF'
    _ ≤ K * 2 ^ (networkRank N + 2) := Nat.mul_le_mul_left K hpow
    _ = 4 * K * 2 ^ networkRank N := by
        rw [pow_succ, pow_succ]
        ring

end Erdos1016.ExactMaximumSupport.Shortening.MarginGadgets
