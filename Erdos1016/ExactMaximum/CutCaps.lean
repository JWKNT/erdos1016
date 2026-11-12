import Erdos1016.ExactMaximum.CycleBoundMargin
import Erdos1016.ExactMaximum.NetAddVertex
import Erdos1016.ExactMaximumSupport.Shortening.TreeCapCycleBound

set_option autoImplicit false

/-!
# Caps: a network that is closed by new vertices

The paper "The maximum number of cycles in a graph of large rank" closes a side of a cut by a
small tree, a *cap*, and applies Corollary 3.11 to the result. The cycles of the result are the
cycles of the side and the paths of the side between two ends of the cap. So the cycles and these
paths together are at most a little more than half of the largest possible number.

This file proves the cap for two and for three vertices of a network `N` of large rank `b`:

* `CapTwoWith`: `c(N) + P_ab(N) ≤ (1 + 1/4096) 2^b`. The cap is one new vertex that is joined to
  `a` and `b`. This is a new edge between `a` and `b` with a vertex in its middle.
* `CapThreeWith`: `c(N) + P_ab(N) + P_ac(N) + P_bc(N) ≤ (2 + 1/2048) 2^b`. The cap is a new
  vertex that is joined to `a` and `b`, and a second new vertex that is joined to the first one
  and to `c`. This is a new vertex joined to `a`, `b` and `c`, with a vertex in the middle of
  its edge to `c`.
* `capStatement`: both hold for all networks of large rank.

The cap for four vertices is `ExactMaximumSupport.Shortening.TreeCapCycleBound.exists_thousandth_bound`
(by Astra). The lemma `cycles_add_paths_le` of that file gives the cycles of a network with one
new vertex.
-/

noncomputable section

namespace Erdos1016.ExactMaximum

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance cutCapsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The cap for two vertices, for networks of rank at least `B`: the cycles and the paths from
`a` to `b` are together at most `(1 + 1/4096) 2^b`. -/
def CapTwoWith (B : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B ≤ networkRank N → ∀ a b : V,
    4096 * (N.numCycles + N.numPaths a b) ≤ 4097 * 2 ^ networkRank N

/-- The cap for three vertices, for networks of rank at least `B`: the cycles and the paths
between two of `a`, `b`, `c` are together at most `(2 + 1/2048) 2^b`. -/
def CapThreeWith (B : ℕ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E), B ≤ networkRank N → ∀ a b c : V,
    2048 * (N.numCycles + N.numPaths a b + N.numPaths a c + N.numPaths b c) ≤
      4097 * 2 ^ networkRank N

/-- **The caps for two and for three vertices.** -/
def CapStatement : Prop := ∃ B : ℕ, CapTwoWith B ∧ CapThreeWith B

/-- **The caps for two and for three vertices hold**, by Corollary 3.11 with the margin
`2^(-13)` for the network with the new vertices. -/
theorem capStatement : CapStatement := by
  obtain ⟨B, hB⟩ := numCycles_le_of_large_rank_margin 12
  have e1 : (2 : ℕ) ^ (12 + 1) = 8192 := by norm_num
  have e2 : (2 : ℕ) ^ 12 + 1 = 4097 := by norm_num
  refine ⟨B, ?_, ?_⟩
  · -- one new vertex, joined to `a` and `b`
    intro V E _ _ N hr a b
    have h1 := ExactMaximumSupport.Shortening.TreeCapCycleBound.cycles_add_paths_le N a b
    have r1 := ExactMaximumSupport.Shortening.TreeCapCycleBound.rank_le_addVertex N a b
    have u1 := N.networkRank_addVertex_le a b
    have hc := hB _ _ (N.addVertex a b) (le_trans hr r1)
    rw [e1, e2] at hc
    have hpow : 2 ^ networkRank (N.addVertex a b) ≤ 2 * 2 ^ networkRank N := by
      calc 2 ^ networkRank (N.addVertex a b) ≤ 2 ^ (networkRank N + 1) :=
            Nat.pow_le_pow_right (by norm_num) u1
        _ = 2 * 2 ^ networkRank N := by rw [pow_succ, Nat.mul_comm]
    have h4 : 8192 * (N.numCycles + N.numPaths a b) ≤ 4097 * (2 * 2 ^ networkRank N) :=
      le_trans (Nat.mul_le_mul_left _ h1) (le_trans hc (Nat.mul_le_mul_left _ hpow))
    generalize 2 ^ networkRank N = T at h4 ⊢
    omega
  · -- a new vertex joined to `a` and `b`, and a second one joined to the first and to `c`
    intro V E _ _ N hr a b c
    have h1 := ExactMaximumSupport.Shortening.TreeCapCycleBound.cycles_add_paths_le N a b
    have h2 := N.numPaths_add_le_numPaths_addVertex a b c
    have h3 := ExactMaximumSupport.Shortening.TreeCapCycleBound.cycles_add_paths_le
      (N.addVertex a b) none (some c)
    have r1 := ExactMaximumSupport.Shortening.TreeCapCycleBound.rank_le_addVertex N a b
    have r2 := ExactMaximumSupport.Shortening.TreeCapCycleBound.rank_le_addVertex
      (N.addVertex a b) none (some c)
    have u1 := N.networkRank_addVertex_le a b
    have u2 := (N.addVertex a b).networkRank_addVertex_le none (some c)
    have hc := hB _ _ ((N.addVertex a b).addVertex none (some c)) (le_trans hr (le_trans r1 r2))
    rw [e1, e2] at hc
    have hpow : 2 ^ networkRank ((N.addVertex a b).addVertex none (some c)) ≤
        4 * 2 ^ networkRank N := by
      calc 2 ^ networkRank ((N.addVertex a b).addVertex none (some c))
          ≤ 2 ^ (networkRank N + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 * 2 ^ networkRank N := by rw [pow_add, Nat.mul_comm]; norm_num
    have hload : N.numCycles + N.numPaths a b + N.numPaths a c + N.numPaths b c ≤
        ((N.addVertex a b).addVertex none (some c)).numCycles := by omega
    have h4 : 8192 * (N.numCycles + N.numPaths a b + N.numPaths a c + N.numPaths b c) ≤
        4097 * (4 * 2 ^ networkRank N) :=
      le_trans (Nat.mul_le_mul_left _ hload) (le_trans hc (Nat.mul_le_mul_left _ hpow))
    generalize 2 ^ networkRank N = T at h4 ⊢
    omega

end Erdos1016.ExactMaximum
