import Mathlib

set_option autoImplicit false
noncomputable section

namespace Erdos1016.Proof.ConditionalMoments.InvalidTupleMass

open scoped BigOperators

local instance forestLawDecidableRel {α : Type*} (R : α → α → Prop) : DecidableRel R :=
  fun a b => Classical.propDecidable (R a b)

/-- Recursive pairwise compatibility: every earlier coordinate is unrelated
(to R) to the final coordinate. For symmetric R this is pairwise
compatibility. -/
def pairwiseRGood {α : Type*} (R : α → α → Prop) :
    (n : ℕ) → (Fin n → α) → Prop
  | 0, _ => True
  | n + 1, u =>
      pairwiseRGood R n (Fin.init u) ∧
        ∀ i : Fin n, ¬ R ((Fin.init u) i) (u (Fin.last n))

/-- If R contains the diagonal, a tuple compatible at every distinct pair
must be injective. -/
theorem pairwiseRGood_injective {α : Type*} (R : α → α → Prop)
    (hdiag : ∀ a, R a a) :
    ∀ n (u : Fin n → α), pairwiseRGood R n u → Function.Injective u := by
  intro n
  induction n with
  | zero =>
      intro u hu i
      exact Fin.elim0 i
  | succ n ih =>
      intro u hu i j hij
      have hpre : Function.Injective (Fin.init u) := ih (Fin.init u) hu.1
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | hi
      · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | hj
        · have hp : (Fin.init u) i' = (Fin.init u) j' := by
            simpa [Fin.init] using hij
          exact congrArg Fin.castSucc (hpre hp)
        · subst j
          exfalso
          have hR : R ((Fin.init u) i') (u (Fin.last n)) := by
            simpa [Fin.init, hij] using hdiag (u (Fin.last n))
          exact hu.2 i' hR
      · subst i
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | hj
        · exfalso
          have hR : R ((Fin.init u) j') (u (Fin.last n)) := by
            have hR' : R (u j'.castSucc) (u (Fin.last n)) := by
              rw [← hij]
              exact hdiag _
            simpa [Fin.init] using hR'
          exact hu.2 j' hR
        · subst j
          rfl

noncomputable def invalidTupleProductMass {α : Type*} [Fintype α]
    (n : ℕ) (R : α → α → Prop) (w : α → ℝ) : ℝ := by
  classical
  exact ∑ u : Fin n → α,
    if ¬ pairwiseRGood R n u then ∏ i, w (u i) else 0

/-- Product mass of all length-n tuples is lambdaVar^n. -/
theorem tuple_product_mass_eq_pow {α : Type*} [Fintype α]
    (n : ℕ) (w : α → ℝ) (lambdaVar : ℝ) (hlambdaVar : (∑ a, w a) = lambdaVar) :
    (∑ u : Fin n → α, ∏ i, w (u i)) = lambdaVar ^ n := by
  classical
  calc
    (∑ u : Fin n → α, ∏ i, w (u i)) =
        ∑ u ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset α)),
          ∏ i, w (u i) := by simp
    _ = (∑ a ∈ (Finset.univ : Finset α), w a) ^ n := by
      simpa using (Finset.sum_pow' (s := (Finset.univ : Finset α)) w n).symm
    _ = lambdaVar ^ n := by simp [hlambdaVar]

/-- The total product weight of tuples whose recursive pairwise compatibility
fails is at most one `d` charge per coordinate pair. The row-load hypothesis
is oriented from an earlier coordinate toward a later one; `R a a` ensures
that every non-injective tuple is included among the failures. -/
theorem invalid_tuple_product_mass_le_choose_two
    {α : Type*} [Fintype α] (n : ℕ) (R : α → α → Prop)
    (w : α → ℝ) (lambdaVar d : ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hdiag : ∀ a, R a a)
    (hrow : ∀ a, (∑ b, if R a b then w b else 0) ≤ d)
    (hlambdaVar : (∑ a, w a) = lambdaVar) (hd : 0 ≤ d) :
    invalidTupleProductMass n R w ≤
      (Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1) := by
  classical
  induction n with
  | zero =>
      simp [invalidTupleProductMass, pairwiseRGood]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [invalidTupleProductMass, pairwiseRGood, hdiag, hlambdaVar]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let e := Fin.snocEquiv (fun _ : Fin (n + 1) => α)
        have hsum (f : (Fin (n + 1) → α) → ℝ) :
            (∑ u : Fin (n + 1) → α, f u) =
              ∑ x : α, ∑ t : Fin n → α, f (Fin.snoc t x) := by
          rw [← Equiv.sum_comp e f]
          change (∑ p : α × (Fin n → α), f (Fin.snoc p.2 p.1)) = _
          simp [Fintype.sum_prod_type]
        have hweight (x : α) (t : Fin n → α) :
            (∏ i : Fin (n + 1), w ((Fin.snoc t x : Fin (n + 1) → α) i)) =
              (∏ i : Fin n, w (t i)) * w x := by
          simp [Fin.prod_univ_castSucc]
        have hbadpoint (x : α) (t : Fin n → α) :
            (if ¬ pairwiseRGood R (n + 1) (Fin.snoc t x) then
                (∏ i : Fin n, w (t i)) * w x else 0) ≤
              (if ¬ pairwiseRGood R n t then
                (∏ i : Fin n, w (t i)) * w x else 0) +
                (∏ i : Fin n, w (t i)) * w x *
                  (∑ i : Fin n, if R (t i) x then 1 else 0) := by
          by_cases ht : pairwiseRGood R n t
          · simp only [pairwiseRGood, Fin.init_snoc, Fin.snoc_last, ht, true_and]
            by_cases hnew : ∀ i : Fin n, ¬ R (t i) x
            · simp [hnew]
            · have hsome : ∃ i : Fin n, R (t i) x := by
                simpa only [not_forall, not_not] using hnew
              obtain ⟨i, hi⟩ := hsome
              have hle : (1 : ℝ) ≤
                  ((Finset.univ.filter (fun i : Fin n => R (t i) x)).card : ℝ) := by
                have hcard : 1 ≤ (Finset.univ.filter
                    (fun i : Fin n => R (t i) x)).card :=
                  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr
                    ⟨Finset.mem_univ _, hi⟩⟩
                exact_mod_cast hcard
              have hwt : 0 ≤ (∏ i : Fin n, w (t i)) * w x :=
                mul_nonneg (Finset.prod_nonneg fun i _ => hw (t i)) (hw x)
              simp [pairwiseRGood, Fin.init_snoc, Fin.snoc_last, ht, hnew]
              nlinarith [mul_le_mul_of_nonneg_left hle hwt]
          · have hwt : 0 ≤ (∏ i : Fin n, w (t i)) * w x :=
              mul_nonneg (Finset.prod_nonneg fun i _ => hw (t i)) (hw x)
            have hcount : 0 ≤
                ((Finset.univ.filter (fun i : Fin n => R (t i) x)).card : ℝ) :=
              Nat.cast_nonneg _
            have hprodcount := mul_nonneg hwt hcount
            simp [pairwiseRGood, Fin.init_snoc, Fin.snoc_last, ht]
            nlinarith [hwt, hprodcount]
        have hbad : invalidTupleProductMass (n + 1) R w =
            ∑ x : α, ∑ t : Fin n → α,
              if ¬ pairwiseRGood R (n + 1) (Fin.snoc t x) then
                (∏ i : Fin n, w (t i)) * w x else 0 := by
          unfold invalidTupleProductMass
          rw [hsum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro t ht
          simp [hweight]
        have hfirst :
            (∑ x : α, ∑ t : Fin n → α,
              if ¬ pairwiseRGood R n t then
                (∏ i : Fin n, w (t i)) * w x else 0) =
              lambdaVar * invalidTupleProductMass n R w := by
          rw [Finset.sum_comm]
          calc
            (∑ t : Fin n → α, ∑ x : α,
                if ¬ pairwiseRGood R n t then
                  (∏ i : Fin n, w (t i)) * w x else 0) =
              ∑ t : Fin n → α,
                (if ¬ pairwiseRGood R n t then
                  ∏ i : Fin n, w (t i) else 0) * (∑ x : α, w x) := by
                apply Finset.sum_congr rfl
                intro t ht
                by_cases hb : ¬ pairwiseRGood R n t
                · simp [hb, Finset.mul_sum]
                · simp [hb]
            _ = lambdaVar * invalidTupleProductMass n R w := by
              calc
                _ = (∑ t : Fin n → α,
                    if ¬ pairwiseRGood R n t then ∏ i : Fin n, w (t i) else 0) *
                      (∑ x : α, w x) := by rw [← Finset.sum_mul]
                _ = lambdaVar *
                    (∑ t : Fin n → α,
                      if ¬ pairwiseRGood R n t then ∏ i : Fin n, w (t i) else 0) := by
                  rw [hlambdaVar]
                  ring
                _ = lambdaVar * invalidTupleProductMass n R w := by
                  rw [invalidTupleProductMass]
        have hsecond :
            (∑ x : α, ∑ t : Fin n → α,
              (∏ i : Fin n, w (t i)) * w x *
                (∑ i : Fin n, if R (t i) x then 1 else 0)) ≤
              (n : ℝ) * d * lambdaVar ^ n := by
          have hinner (t : Fin n → α) :
              (∑ x : α, w x * (∑ i : Fin n, if R (t i) x then 1 else 0)) ≤
                (n : ℝ) * d := by
            calc
              _ = ∑ i : Fin n, ∑ x : α, if R (t i) x then w x else 0 := by
                simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
                rw [Finset.sum_comm]
              _ ≤ ∑ _i : Fin n, d := by
                exact Finset.sum_le_sum fun i _ => hrow (t i)
              _ = (n : ℝ) * d := by simp
          calc
            _ = ∑ t : Fin n → α,
                  (∏ i : Fin n, w (t i)) *
                    (∑ x : α, w x *
                      (∑ i : Fin n, if R (t i) x then 1 else 0)) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro t ht
                calc
                  (∑ x : α,
                      (∏ i : Fin n, w (t i)) * w x *
                        (∑ i : Fin n, if R (t i) x then 1 else 0)) =
                    (∏ i : Fin n, w (t i)) *
                      (∑ x : α, w x *
                        (∑ i : Fin n, if R (t i) x then 1 else 0)) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
                  _ = _ := rfl
              _ ≤ ∑ t : Fin n → α,
                    (∏ i : Fin n, w (t i)) * ((n : ℝ) * d) := by
                apply Finset.sum_le_sum
                intro t ht
                exact mul_le_mul_of_nonneg_left (hinner t)
                  (Finset.prod_nonneg fun i _ => hw (t i))
              _ = (n : ℝ) * d * lambdaVar ^ n := by
                rw [← Finset.sum_mul]
                rw [tuple_product_mass_eq_pow n w lambdaVar hlambdaVar]
                ring
        have hrec : invalidTupleProductMass (n + 1) R w ≤
            lambdaVar * invalidTupleProductMass n R w + (n : ℝ) * d * lambdaVar ^ n := by
          rw [hbad]
          calc
            _ ≤ ∑ x : α, ∑ t : Fin n → α,
                ((if ¬ pairwiseRGood R n t then
                  (∏ i : Fin n, w (t i)) * w x else 0) +
                  (∏ i : Fin n, w (t i)) * w x *
                    (∑ i : Fin n, if R (t i) x then 1 else 0)) := by
              apply Finset.sum_le_sum
              intro x hx
              apply Finset.sum_le_sum
              intro t ht
              exact hbadpoint x t
            _ = lambdaVar * invalidTupleProductMass n R w +
                  (∑ x : α, ∑ t : Fin n → α,
                    (∏ i : Fin n, w (t i)) * w x *
                      (∑ i : Fin n, if R (t i) x then 1 else 0)) := by
              simp_rw [Finset.sum_add_distrib]
              rw [hfirst]
            _ ≤ _ := add_le_add_left hsecond _
        have hlambdaVarnonneg : 0 ≤ lambdaVar := by
          rw [← hlambdaVar]
          exact Finset.sum_nonneg fun a _ => hw a
        have hpow : 0 ≤ lambdaVar ^ n := by positivity
        have hchoose : (Nat.choose (n + 1) 2 : ℝ) =
            (Nat.choose n 2 : ℝ) + n := by
          have hNat : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
            have := Nat.choose_succ_succ n 1
            norm_num at this ⊢
            omega
          exact_mod_cast hNat
        have hfinal :
            lambdaVar * ((Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1)) +
                (n : ℝ) * d * lambdaVar ^ n ≤
              (Nat.choose (n + 1) 2 : ℝ) * d * lambdaVar ^ n := by
          by_cases hpowzero : lambdaVar = 0
          · rw [hpowzero]
            have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
            simp [hnne]
          · have hpowmul : lambdaVar * lambdaVar ^ (n - 1) = lambdaVar ^ n := by
              calc
                lambdaVar * lambdaVar ^ (n - 1) =
                    lambdaVar ^ (n - 1) * lambdaVar := by ring
                _ = lambdaVar ^ ((n - 1) + 1) := by rw [pow_succ]
                _ = lambdaVar ^ n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
            calc
              _ = (Nat.choose n 2 : ℝ) * d *
                    (lambdaVar * lambdaVar ^ (n - 1)) +
                    (n : ℝ) * d * lambdaVar ^ n := by ring
              _ = ((Nat.choose n 2 : ℝ) + n) * d * lambdaVar ^ n := by
                rw [hpowmul]
                ring
              _ = (Nat.choose (n + 1) 2 : ℝ) * d * lambdaVar ^ n := by
                exact congrArg (fun c : ℝ => c * d * lambdaVar ^ n) hchoose.symm
              _ ≤ (Nat.choose (n + 1) 2 : ℝ) * d * lambdaVar ^ n := le_rfl
        have hstep :
            lambdaVar * invalidTupleProductMass n R w +
                (n : ℝ) * d * lambdaVar ^ n ≤
              lambdaVar * ((Nat.choose n 2 : ℝ) * d * lambdaVar ^ (n - 1)) +
                (n : ℝ) * d * lambdaVar ^ n := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left ih hlambdaVarnonneg) _
        exact hrec.trans (hstep.trans hfinal)

end Erdos1016.Proof.ConditionalMoments.InvalidTupleMass
