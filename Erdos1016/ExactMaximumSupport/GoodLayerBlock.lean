import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Four consecutive good layers

The blocks starting at `1 + 4*i` are disjoint. If each of `B+1` blocks
contained a bad layer, selecting one from each would inject `Fin (B+1)`
into a set of at most `B` bad layers.
-/

namespace Erdos1016.ExactMaximumSupport.GoodLayerBlock

/-- At most `B` bad indices cannot meet all `B+1` disjoint four-index blocks. -/
theorem exists_four_good (bad : Finset ℕ) (B L : ℕ) (hbad : bad.card ≤ B)
    (hL : 4 * (B + 1) ≤ L) :
    ∃ k : ℕ, 1 ≤ k ∧ k + 3 ≤ L ∧
      ∀ j ∈ Finset.Icc k (k + 3), j ∉ bad := by
  classical
  by_contra hn
  have hhit (i : Fin (B + 1)) :
      ∃ j : ℕ, j ∈ bad ∧ 1 + 4 * i.val ≤ j ∧ j ≤ 1 + 4 * i.val + 3 := by
    by_contra hnone
    apply hn
    refine ⟨1 + 4 * i.val, by omega, by have hi := i.isLt; omega, ?_⟩
    intro j hj hmem
    exact hnone ⟨j, hmem, (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
  choose f hf using hhit
  let pick : Fin (B + 1) → {j : ℕ // j ∈ bad} := fun i => ⟨f i, (hf i).1⟩
  have hinj : Function.Injective pick := by
    intro i j hij
    have he : f i = f j := congrArg Subtype.val hij
    have hi := (hf i).2
    have hj := (hf j).2
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective pick hinj
  have himpossible : B + 1 ≤ bad.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  omega

/-- The paper's rank and bad-layer bounds give four good interior layers. -/
theorem exists_four_good_interior (bad : Finset ℕ) (ell C g b : ℕ)
    (hell : b ≤ ell + C) (hb : 9 * C + 8 * g + 9 ≤ b)
    (hbad : bad.card ≤ 2 * C + 2 * g) :
    ∃ k : ℕ, 1 ≤ k ∧ k + 3 < ell ∧
      ∀ j ∈ Finset.Icc k (k + 3), j ∉ bad := by
  have hL : 4 * (2 * C + 2 * g + 1) ≤ ell - 1 := by omega
  obtain ⟨k, hk, hkl, hgood⟩ := exists_four_good bad (2 * C + 2 * g) (ell - 1) hbad hL
  exact ⟨k, hk, by omega, hgood⟩

end Erdos1016.ExactMaximumSupport.GoodLayerBlock
