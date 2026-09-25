import Erdos1016.Probability.Cylinders.ExceptionalPartnerCount

set_option autoImplicit false
set_option maxHeartbeats 600000

/-!
# Exceptional partners for rank-two region constraints

The many-region argument uses constraints of rank at most two.  If three
distinct regions have common constraint space of rank at most one, then each
region has at most sixteen exceptional partners.  The extra diagonal slot in
the second-moment sum is accounted for separately, giving the convenient
constant seventeen used by the probability wrapper.
-/

noncomputable section

namespace Erdos1016.Proof.ManyCyclicRegionsExceptionalPartners

open Erdos1016.Proof.PartnerCounting

local notation "𝔽" => ZMod 2

/-- General-dimension form of the exceptional-partner plane count. -/
theorem exceptional_card_le_two_pow_two_mul_of_dim
    {W ι : Type*} [AddCommGroup W] [Module 𝔽 W]
    [FiniteDimensional 𝔽 W] [Fintype W] [Fintype ι]
    (S : Submodule 𝔽 W) (T : ι → Submodule 𝔽 W)
    (E : ι → Prop) [DecidablePred E]
    (d : ℕ) (hS : Module.finrank 𝔽 S ≤ d)
    (hpair : ∀ i : ι, E i → 2 ≤ Module.finrank 𝔽 (PairIntersection S (T i)))
    (htriple : ∀ i j : ι, E i → E j → i ≠ j →
      Module.finrank 𝔽 (TripleIntersection S (T i) (T j)) ≤ 1) :
    Fintype.card {i : ι // E i} ≤ 2 ^ (2 * d) := by
  classical
  let P : {i : ι // E i} → Submodule 𝔽 W := fun i =>
    Submodule.span 𝔽 (Set.range (fun k : Fin 2 =>
      ((Classical.choose (exists_linearIndependent_of_le_finrank
        (R := 𝔽) (M := PairIntersection S (T i.1)) (n := 2)
        (hpair i.1 i.2)) k : PairIntersection S (T i.1)) : W)))
  have hPdim : ∀ i : {i : ι // E i}, Module.finrank 𝔽 (P i) = 2 := by
    intro i
    let v : Fin 2 → PairIntersection S (T i.1) := Classical.choose
      (exists_linearIndependent_of_le_finrank
        (R := 𝔽) (M := PairIntersection S (T i.1)) (n := 2)
        (hpair i.1 i.2))
    have hv : LinearIndependent 𝔽 (fun k => (v k : W)) :=
      (Classical.choose_spec (exists_linearIndependent_of_le_finrank
        (R := 𝔽) (M := PairIntersection S (T i.1)) (n := 2)
        (hpair i.1 i.2))).map'
          (PairIntersection S (T i.1)).subtype
          (PairIntersection S (T i.1)).ker_subtype
    have hdim := finrank_span_eq_card hv
    simpa [P, v, Fintype.card_fin] using hdim
  have hPbelow : ∀ i : {i : ι // E i}, P i ≤ PairIntersection S (T i.1) := by
    intro i
    apply Submodule.span_le.2
    rintro x ⟨k, rfl⟩
    exact (Classical.choose (exists_linearIndependent_of_le_finrank
      (R := 𝔽) (M := PairIntersection S (T i.1)) (n := 2)
      (hpair i.1 i.2)) k).2
  have htriple' : ∀ (i j : {i : ι // E i}), i.val ≠ j.val →
      Module.finrank 𝔽 (TripleIntersection S (T i.val) (T j.val)) ≤ 1 := by
    intro i j hij
    simpa [TripleIntersection, PairIntersection] using
      htriple i.val j.val i.property j.property hij
  have hplanes := exceptional_partners_le_number_of_planes
    S T E P hPdim hPbelow htriple'
  have hbound := number_of_planes_le_two_pow_two_mul S d hS
  exact hplanes.trans hbound







end Erdos1016.Proof.ManyCyclicRegionsExceptionalPartners

end
