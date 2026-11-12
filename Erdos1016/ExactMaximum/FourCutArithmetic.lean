import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

/-!
# The arithmetic of a cyclic cut of size four: a statement

The proof of Theorem 6.8 of the paper "The maximum number of cycles in a graph of large rank"
has two parts. The first part is about graphs: the two sides `X`, `Y` of a cyclic cut of size
four are poles with four ports, and their numbers of paths and of pairs of disjoint paths satisfy
the inequalities of Lemma 5.7, Theorem 5.10 and Lemma 6.7. The second part is arithmetic: Lemmas
6.5 and 6.6 and the four cases of the proof. This file states the second part as one statement
about real numbers. It proves nothing.

The ports of a side are numbered `0, 1, 2, 3`, and the cut edge at the port `i` of `X` ends in
the port `i` of `Y`. For a side of rank `h`:

* `a i j` is the number of paths between the ports `i` and `j`, divided by `2^h`;
* `u α` is the number of pairs of disjoint paths for the pairing `α`, divided by `2^h`, where the
  pairings are `0 = 01|23`, `1 = 02|13`, `2 = 03|12` (`pairingOf`).

`FourState` has the facts that hold for every side, and `LargeState` adds the facts that hold for
a side of large rank, with `κ = 1/1000`. In `FourCutArithmeticStatement`, `x`, `p`, `cX`, `dX`
belong to the smaller side `X` and `a`, `u`, `cY`, `dY` to the larger side `Y`: `dX` and `dY` are
`2^h` and `2^k`, and `cX`, `cY` are the numbers of cycles of the sides divided by `dX`, `dY`.
The number of cycles of the graph, divided by `2^(h+k)`, is then
`cX / dY + cY / dX + pairSum x a + pairingSum p u`, and `2^(r-1) = 4 · 2^(h+k)`.
-/

noncomputable section

namespace Erdos1016.ExactMaximum

/-- The pairing of the ports `0, 1, 2, 3` that contains the pair `i, j`: `0` for `01|23`, `1` for
`02|13`, and `2` for `03|12`. -/
def pairingOf (i j : Fin 4) : Fin 3 :=
  if i.val + j.val = 1 ∨ i.val + j.val = 5 then 0
  else if i.val + j.val = 2 ∨ i.val + j.val = 4 then 1 else 2

/-- The numbers of a pole with four ports. -/
structure FourState (a : Fin 4 → Fin 4 → ℝ) (u : Fin 3 → ℝ) : Prop where
  symm : ∀ i j, a i j = a j i
  nonneg : ∀ i j, 0 ≤ a i j
  le_one : ∀ i j, a i j ≤ 1
  u_nonneg : ∀ α, 0 ≤ u α
  /-- The pairs of disjoint paths are joins of the four ports. -/
  u_sum : u 0 + u 1 + u 2 ≤ 1
  /-- Theorem 5.10. -/
  gap : ∀ i j, i ≠ j → a i j = 1 ∨ a i j ≤ 15 / 16
  /-- Lemma 6.7. -/
  star : ∀ i, (∀ j, j ≠ i → a i j = 1) → ∀ α, u α ≤ 1 / 2

/-- The numbers of a pole with four ports and large rank: Lemma 5.7 (b), (c), (d) with
`κ = 1/1000`. -/
structure LargeState (a : Fin 4 → Fin 4 → ℝ) (u : Fin 3 → ℝ) : Prop extends FourState a u where
  t1 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 1002 / 1000 ≤ a i k + a j k → a i j ≤ 1 / 1000
  t2 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    2004 / 1000 ≤ a i k + a i l + a j k + a j l →
    u (pairingOf i k) + u (pairingOf i l) ≤ 1 / 1000
  t3 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    1002 / 1000 ≤ a i j + u (pairingOf i k) + u (pairingOf i l) → a k l ≤ 1 / 1000

/-- The cycles through two cut edges: the sum of the products for the six pairs of ports. -/
def pairSum (x a : Fin 4 → Fin 4 → ℝ) : ℝ :=
  x 0 1 * a 0 1 + x 0 2 * a 0 2 + x 0 3 * a 0 3 + x 1 2 * a 1 2 + x 1 3 * a 1 3 + x 2 3 * a 2 3

/-- The cycles through four cut edges: the sum of the products for the ordered pairs of
different pairings. -/
def pairingSum (p u : Fin 3 → ℝ) : ℝ :=
  p 0 * (u 1 + u 2) + p 1 * (u 0 + u 2) + p 2 * (u 0 + u 1)

/-- **The arithmetic of Theorem 6.8 of the paper** (Lemmas 6.5 and 6.6 and the cases 1 to 4).
Let `x`, `p` be the numbers of the side `X` and `a`, `u` the numbers of the side `Y` of large
rank. Then the graph has fewer than `2^(r-1)` cycles, or for some partition of the ports into
two pairs the four pairs between them are full in both sides. Not proved in this file. -/
def FourCutArithmeticStatement : Prop :=
  ∀ (x a : Fin 4 → Fin 4 → ℝ) (p u : Fin 3 → ℝ) (cX cY dX dY : ℝ),
    FourState x p → LargeState a u → 2 ≤ dX → 1000 ≤ dY →
    (dX < 4 → ∀ α, p α ≤ 1 / 2) → 0 ≤ cX → cX < 1 → 0 ≤ cY → cY ≤ 9 / 16 →
    ((∃ i j, i ≠ j ∧ 501 / 1000 ≤ a i j) → cY ≤ 1 / 1000) →
    cX / dY + cY / dX + (pairSum x a + pairingSum p u) < 4 ∨
      ∃ i j k l : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
        x i k = 1 ∧ x i l = 1 ∧ x j k = 1 ∧ x j l = 1 ∧
        a i k = 1 ∧ a i l = 1 ∧ a j k = 1 ∧ a j l = 1

end Erdos1016.ExactMaximum
