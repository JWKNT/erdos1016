import Erdos1016.Probability.Cylinders.SubspacePartnerCount

set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Cardinality bound for exceptional partners

Each exceptional index contributes a two dimensional subspace of its
intersection with a fixed subspace. The triple rank hypothesis makes these
chosen planes distinct, so the existing pair encoding bounds their number.
-/

noncomputable section

namespace Erdos1016.Proof.ExceptionalPartnerCardinality

open Erdos1016.Proof.PartnerCounting


theorem exceptional_card_le_two_pow_two_mul
    {W ι : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] [Fintype W] [Fintype ι]
    (S : Submodule F₂ W) (T : ι → Submodule F₂ W)
    (E : ι → Prop) [DecidablePred E]
    (hS : Module.finrank F₂ S ≤ 3)
    (hpair : ∀ i : ι, E i → 2 ≤ Module.finrank F₂ (PairIntersection S (T i)))
    (htriple : ∀ i j : ι, E i → E j → i ≠ j →
      Module.finrank F₂ (TripleIntersection S (T i) (T j)) ≤ 1) :
    Fintype.card {i : ι // E i} ≤ 2 ^ (2 * 3) := by
  classical
  let P : {i : ι // E i} → Submodule F₂ W := fun i =>
    Submodule.span F₂ (Set.range (fun k : Fin 2 =>
      ((Classical.choose (exists_linearIndependent_of_le_finrank
        (R := F₂) (M := PairIntersection S (T i.1)) (n := 2) (hpair i.1 i.2)) k : PairIntersection S (T i.1)) : W)))
  have hPdim : ∀ i : {i : ι // E i}, Module.finrank F₂ (P i) = 2 := by
    intro i
    let v : Fin 2 → PairIntersection S (T i.1) := Classical.choose
      (exists_linearIndependent_of_le_finrank
        (R := F₂) (M := PairIntersection S (T i.1)) (n := 2) (hpair i.1 i.2))
    have hv : LinearIndependent F₂ (fun k => (v k : W)) :=
      (Classical.choose_spec (exists_linearIndependent_of_le_finrank
        (R := F₂) (M := PairIntersection S (T i.1)) (n := 2) (hpair i.1 i.2))).map'
          (PairIntersection S (T i.1)).subtype (PairIntersection S (T i.1)).ker_subtype
    have hdim := finrank_span_eq_card hv
    simpa [P, v, Fintype.card_fin] using hdim
  have hPbelow : ∀ i : {i : ι // E i}, P i ≤ PairIntersection S (T i.1) := by
    intro i
    apply Submodule.span_le.2
    rintro x ⟨k, rfl⟩
    exact (Classical.choose (exists_linearIndependent_of_le_finrank
      (R := F₂) (M := PairIntersection S (T i.1)) (n := 2) (hpair i.1 i.2)) k).2
  have htriple' : ∀ (i j : {i : ι // E i}), i.val ≠ j.val →
      Module.finrank F₂ (TripleIntersection S (T i.val) (T j.val)) ≤ 1 := by
    intro i j hij
    simpa [TripleIntersection, PairIntersection] using
      htriple i.val j.val i.property j.property hij
  have hplanes := exceptional_partners_le_number_of_planes
    S T E P hPdim hPbelow htriple'
  have hbound := number_of_planes_le_two_pow_two_mul S 3 hS
  exact hplanes.trans hbound

theorem exceptional_card_le_64
    {W ι : Type*} [AddCommGroup W] [Module F₂ W]
    [FiniteDimensional F₂ W] [Fintype W] [Fintype ι]
    (S : Submodule F₂ W) (T : ι → Submodule F₂ W)
    (E : ι → Prop) [DecidablePred E]
    (hS : Module.finrank F₂ S ≤ 3)
    (hpair : ∀ i : ι, E i → 2 ≤ Module.finrank F₂ (PairIntersection S (T i)))
    (htriple : ∀ i j : ι, E i → E j → i ≠ j →
      Module.finrank F₂ (TripleIntersection S (T i) (T j)) ≤ 1) :
    Fintype.card {i : ι // E i} ≤ 64 := by
  have h := exceptional_card_le_two_pow_two_mul S T E hS hpair htriple
  norm_num at h ⊢
  exact h

end Erdos1016.Proof.ExceptionalPartnerCardinality
