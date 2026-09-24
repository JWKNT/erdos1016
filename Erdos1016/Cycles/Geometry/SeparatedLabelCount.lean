import Erdos1016.Cycles.Selection.ConditionalPenaltyBounds

set_option autoImplicit false

/-!
# Counting separated labels on a cycle segment

A segment has `m` successive positions. Apart
from at most one exceptional position, each marked position carries the
label of one of the previously selected cycles. Two positions with the
same label are at least `Δ` steps apart. Consequently the number of marked
positions is at most `1 + j * ceil (m / Δ)`.

The geometric task of constructing those labels from the pruned two-core
is separate. The results here prove the counting consequence; they do not
assume that consequence or the conditional probability estimate.
-/

noncomputable section

namespace Erdos1016.Proof.ConditionalDegreeTwoSpacing

private theorem quotient_lt_ceil (m Δ : ℕ) (hΔ : 0 < Δ)
    (a : Fin m) : a.val / Δ < Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  have hΔreal : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hceil := Nat.le_ceil ((m : ℝ) / (Δ : ℝ))
  have hbound : m ≤ Nat.ceil ((m : ℝ) / (Δ : ℝ)) * Δ := by
    have hreal := (div_le_iff₀ hΔreal).mp hceil
    exact_mod_cast hreal
  exact (Nat.div_lt_iff_lt_mul hΔ).mpr (lt_of_lt_of_le a.isLt hbound)

/-- A block of `Δ` successive positions contains at most one occurrence of
each label. Injecting marked positions into `(label, block number)` gives
the sharp ceiling bound, including the empty-segment case. -/
theorem card_le_labels_mul_ceil
    {ι : Type*} [Fintype ι] {m Δ : ℕ}
    (S : Finset (Fin m)) (label : S → ι) (hΔ : 0 < Δ)
    (hseparated : ∀ a b : S, a.val.val < b.val.val →
      label a = label b → a.val.val + Δ ≤ b.val.val) :
    S.card ≤ Fintype.card ι * Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  classical
  let blockCount := Nat.ceil ((m : ℝ) / (Δ : ℝ))
  let encode : S → ι × Fin blockCount := fun a =>
    (label a, ⟨a.val.val / Δ, quotient_lt_ceil m Δ hΔ a.val⟩)
  have hinjective : Function.Injective encode := by
    intro a b heq
    have hlabel : label a = label b := congrArg Prod.fst heq
    have hblock : a.val.val / Δ = b.val.val / Δ :=
      congrArg (fun p : ι × Fin blockCount => p.2.val) heq
    have hnotlt : ¬ a.val.val < b.val.val := by
      intro hlt
      have hsep := hseparated a b hlt hlabel
      have ha := Nat.div_mul_le_self a.val.val Δ
      have hb := Nat.lt_mul_div_succ b.val.val hΔ
      rw [← hblock] at hb
      nlinarith
    have hnotgt : ¬ b.val.val < a.val.val := by
      intro hlt
      have hsep := hseparated b a hlt hlabel.symm
      have hb := Nat.div_mul_le_self b.val.val Δ
      have ha := Nat.lt_mul_div_succ a.val.val hΔ
      rw [hblock] at ha
      nlinarith
    apply Subtype.ext
    apply Fin.ext
    omega
  have hcard := Fintype.card_le_of_injective encode hinjective
  simpa [blockCount] using hcard

/-- Allowing an exceptional set costs exactly its cardinality. This form is
useful before the geometric proof establishes that there is at most one
unlabelled tree meeting the connected protector. -/
theorem card_le_exceptional_add_labels_mul_ceil
    {ι : Type*} [Fintype ι] {m Δ : ℕ}
    (S E : Finset (Fin m)) (label : ↥(S \ E) → ι) (hΔ : 0 < Δ)
    (hseparated : ∀ a b : ↥(S \ E), a.val.val < b.val.val →
      label a = label b → a.val.val + Δ ≤ b.val.val) :
    S.card ≤ E.card + Fintype.card ι * Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  have hcount := card_le_labels_mul_ceil (S \ E) label hΔ hseparated
  have hcover : S ⊆ E ∪ (S \ E) := by
    intro a ha
    by_cases hE : a ∈ E
    · exact Finset.mem_union_left _ hE
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ha, hE⟩)
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  omega





end Erdos1016.Proof.ConditionalDegreeTwoSpacing

end
