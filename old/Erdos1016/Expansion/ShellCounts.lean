import Mathlib

set_option autoImplicit false

namespace Erdos1016.Proof.ShellCounts

/-- Abstract BFS shell sizes for a union of balls rooted at a finite set of
vertices. The first shell is the root set; the next shell has at most three
neighbors per root; each subsequent shell has at most two children per vertex
because each vertex has a parent in the previous shell. -/
theorem shell_card_le
    (shell : ℕ → ℕ) (rootCount : ℕ)
    (hzero : shell 0 ≤ rootCount)
    (hone : shell 1 ≤ 3 * rootCount)
    (hstep : ∀ k, 1 ≤ k → shell (k + 1) ≤ 2 * shell k) :
    ∀ k, 1 ≤ k → shell k ≤ 3 * rootCount * 2 ^ (k - 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using hone
      · have hkpos : 1 ≤ k := by omega
        have hs := hstep k hkpos
        have ih' := ih hkpos
        have hp : 2 * (3 * rootCount * 2 ^ (k - 1)) =
            3 * rootCount * 2 ^ k := by
          have he : k = (k - 1) + 1 := (Nat.sub_add_cancel hkpos).symm
          rw [he]
          have hsub : ((k - 1) + 1) - 1 = k - 1 := by omega
          rw [hsub, pow_succ]
          ring
        calc
          shell (k + 1) ≤ 2 * shell k := hs
          _ ≤ 2 * (3 * rootCount * 2 ^ (k - 1)) := Nat.mul_le_mul_left 2 ih'
          _ = 3 * rootCount * 2 ^ k := hp

/-- Summing the BFS shells gives the usual subcubic closed-ball estimate.
This is the arithmetic part of the graph argument; a graph-specific proof
must supply `hone` and `hstep` for its actual distance shells. -/
theorem sum_shell_card_le
    (shell : ℕ → ℕ) (rootCount q : ℕ)
    (hzero : shell 0 ≤ rootCount)
    (hone : shell 1 ≤ 3 * rootCount)
    (hstep : ∀ k, 1 ≤ k → shell (k + 1) ≤ 2 * shell k) :
    (∑ k ∈ Finset.range (q + 1), shell k) ≤ 3 * rootCount * 2 ^ q := by
  have hshell := shell_card_le shell rootCount hzero hone hstep
  induction q with
  | zero =>
      simp
      omega
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have hlast : shell (q + 1) ≤ 3 * rootCount * 2 ^ q := by
        apply hshell
        omega
      rw [pow_succ]
      calc
        (∑ k ∈ Finset.range (q + 1), shell k) + shell (q + 1) ≤
            3 * rootCount * 2 ^ q + 3 * rootCount * 2 ^ q := Nat.add_le_add ih hlast
        _ = 3 * rootCount * (2 ^ q * 2) := by ring

end Erdos1016.Proof.ShellCounts
