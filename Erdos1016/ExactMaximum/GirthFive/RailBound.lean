import Mathlib.Tactic

set_option autoImplicit false

/-!
# The rail lemma: an arithmetic fact

Let `A` be a shortest path between two vertices of a graph of girth at least five, and let
`v_0, ..., v_6` be a path that avoids `A` such that `v_k` has a neighbour on `A` at the position
`p k`. Then for `k < l`:

* `p k ≠ p l` (the positions are different);
* `|p k - p l| ≤ (l - k) + 2`, because `A` is a shortest path;
* `|p k - p l| + (l - k) + 2 ≥ 5`, because the cycle through the two neighbours has at least
  five edges. For `l = k + 1` this says `|p k - p l| ≥ 2`.

No seven natural numbers satisfy these conditions. (The longest sequence has six terms, for
example `5, 2, 4, 1, 3, 0`.) This file proves the arithmetic statement. The graph theory is in
`GeodesicRails.lean`.
-/

namespace Erdos1016.ExactMaximum.GirthFive

/-- **The rail lemma.** No seven natural numbers `p 0, ..., p 6` are pairwise different, with
`|p k - p l| ≤ (l - k) + 2` for `k < l` and `|p k - p (k+1)| ≥ 2`. -/
theorem rail_bound (p : ℕ → ℕ)
    (hne : ∀ k l, k < l → l ≤ 6 → p k ≠ p l)
    (hgeo : ∀ k l, k < l → l ≤ 6 → p l ≤ p k + (l - k) + 2 ∧ p k ≤ p l + (l - k) + 2)
    (hstep : ∀ k, k < 6 → p k + 2 ≤ p (k + 1) ∨ p (k + 1) + 2 ≤ p k) : False := by
  -- the consecutive steps
  have s0 : p 0 + 2 ≤ p 1 ∨ p 1 + 2 ≤ p 0 := hstep 0 (by norm_num)
  have s1 : p 1 + 2 ≤ p 2 ∨ p 2 + 2 ≤ p 1 := hstep 1 (by norm_num)
  have s2 : p 2 + 2 ≤ p 3 ∨ p 3 + 2 ≤ p 2 := hstep 2 (by norm_num)
  have s3 : p 3 + 2 ≤ p 4 ∨ p 4 + 2 ≤ p 3 := hstep 3 (by norm_num)
  have s4 : p 4 + 2 ≤ p 5 ∨ p 5 + 2 ≤ p 4 := hstep 4 (by norm_num)
  have s5 : p 5 + 2 ≤ p 6 ∨ p 6 + 2 ≤ p 5 := hstep 5 (by norm_num)
  -- the bounds from the shortest path, and the pairs of different positions
  have g01 : p 1 ≤ p 0 + 1 + 2 ∧ p 0 ≤ p 1 + 1 + 2 := hgeo 0 1 (by norm_num) (by norm_num)
  have g02 : p 2 ≤ p 0 + 2 + 2 ∧ p 0 ≤ p 2 + 2 + 2 := hgeo 0 2 (by norm_num) (by norm_num)
  have g03 : p 3 ≤ p 0 + 3 + 2 ∧ p 0 ≤ p 3 + 3 + 2 := hgeo 0 3 (by norm_num) (by norm_num)
  have g04 : p 4 ≤ p 0 + 4 + 2 ∧ p 0 ≤ p 4 + 4 + 2 := hgeo 0 4 (by norm_num) (by norm_num)
  have g05 : p 5 ≤ p 0 + 5 + 2 ∧ p 0 ≤ p 5 + 5 + 2 := hgeo 0 5 (by norm_num) (by norm_num)
  have g06 : p 6 ≤ p 0 + 6 + 2 ∧ p 0 ≤ p 6 + 6 + 2 := hgeo 0 6 (by norm_num) (by norm_num)
  have g12 : p 2 ≤ p 1 + 1 + 2 ∧ p 1 ≤ p 2 + 1 + 2 := hgeo 1 2 (by norm_num) (by norm_num)
  have g13 : p 3 ≤ p 1 + 2 + 2 ∧ p 1 ≤ p 3 + 2 + 2 := hgeo 1 3 (by norm_num) (by norm_num)
  have g14 : p 4 ≤ p 1 + 3 + 2 ∧ p 1 ≤ p 4 + 3 + 2 := hgeo 1 4 (by norm_num) (by norm_num)
  have g15 : p 5 ≤ p 1 + 4 + 2 ∧ p 1 ≤ p 5 + 4 + 2 := hgeo 1 5 (by norm_num) (by norm_num)
  have g16 : p 6 ≤ p 1 + 5 + 2 ∧ p 1 ≤ p 6 + 5 + 2 := hgeo 1 6 (by norm_num) (by norm_num)
  have g23 : p 3 ≤ p 2 + 1 + 2 ∧ p 2 ≤ p 3 + 1 + 2 := hgeo 2 3 (by norm_num) (by norm_num)
  have g24 : p 4 ≤ p 2 + 2 + 2 ∧ p 2 ≤ p 4 + 2 + 2 := hgeo 2 4 (by norm_num) (by norm_num)
  have g25 : p 5 ≤ p 2 + 3 + 2 ∧ p 2 ≤ p 5 + 3 + 2 := hgeo 2 5 (by norm_num) (by norm_num)
  have g26 : p 6 ≤ p 2 + 4 + 2 ∧ p 2 ≤ p 6 + 4 + 2 := hgeo 2 6 (by norm_num) (by norm_num)
  have g34 : p 4 ≤ p 3 + 1 + 2 ∧ p 3 ≤ p 4 + 1 + 2 := hgeo 3 4 (by norm_num) (by norm_num)
  have g35 : p 5 ≤ p 3 + 2 + 2 ∧ p 3 ≤ p 5 + 2 + 2 := hgeo 3 5 (by norm_num) (by norm_num)
  have g36 : p 6 ≤ p 3 + 3 + 2 ∧ p 3 ≤ p 6 + 3 + 2 := hgeo 3 6 (by norm_num) (by norm_num)
  have g45 : p 5 ≤ p 4 + 1 + 2 ∧ p 4 ≤ p 5 + 1 + 2 := hgeo 4 5 (by norm_num) (by norm_num)
  have g46 : p 6 ≤ p 4 + 2 + 2 ∧ p 4 ≤ p 6 + 2 + 2 := hgeo 4 6 (by norm_num) (by norm_num)
  have g56 : p 6 ≤ p 5 + 1 + 2 ∧ p 5 ≤ p 6 + 1 + 2 := hgeo 5 6 (by norm_num) (by norm_num)
  have n02 : p 0 ≠ p 2 := hne 0 2 (by norm_num) (by norm_num)
  have n03 : p 0 ≠ p 3 := hne 0 3 (by norm_num) (by norm_num)
  have n04 : p 0 ≠ p 4 := hne 0 4 (by norm_num) (by norm_num)
  have n05 : p 0 ≠ p 5 := hne 0 5 (by norm_num) (by norm_num)
  have n06 : p 0 ≠ p 6 := hne 0 6 (by norm_num) (by norm_num)
  have n13 : p 1 ≠ p 3 := hne 1 3 (by norm_num) (by norm_num)
  have n14 : p 1 ≠ p 4 := hne 1 4 (by norm_num) (by norm_num)
  have n15 : p 1 ≠ p 5 := hne 1 5 (by norm_num) (by norm_num)
  have n16 : p 1 ≠ p 6 := hne 1 6 (by norm_num) (by norm_num)
  have n24 : p 2 ≠ p 4 := hne 2 4 (by norm_num) (by norm_num)
  have n25 : p 2 ≠ p 5 := hne 2 5 (by norm_num) (by norm_num)
  have n26 : p 2 ≠ p 6 := hne 2 6 (by norm_num) (by norm_num)
  have n35 : p 3 ≠ p 5 := hne 3 5 (by norm_num) (by norm_num)
  have n36 : p 3 ≠ p 6 := hne 3 6 (by norm_num) (by norm_num)
  have n46 : p 4 ≠ p 6 := hne 4 6 (by norm_num) (by norm_num)
  rcases s0 with a0 | a0 <;> rcases s1 with a1 | a1 <;> rcases s2 with a2 | a2 <;>
    rcases s3 with a3 | a3 <;> rcases s4 with a4 | a4 <;> rcases s5 with a5 | a5 <;> omega

end Erdos1016.ExactMaximum.GirthFive
