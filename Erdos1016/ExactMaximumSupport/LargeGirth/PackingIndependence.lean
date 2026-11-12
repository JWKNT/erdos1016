import Erdos1016.ExactMaximumSupport.LargeGirth.PackingProduct
import Erdos1016.Probability.Cylinders.Affine
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.SupIndep

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Independent cylinder factors for a direct sum of local spaces

The restriction map onto the product of local duals is proved surjective.
Its uniform image law follows from the exact linear fiber equivalence.
Thus the product expectation uses the entire ambient dual space.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingIndependence

open BoundaryDecay BoundaryTrace
open Proof.AffineCylinders
local instance packingIndependenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Reindexing the entire finite space preserves an average. -/
theorem average_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : average (fun a => f (e a)) = average f := by
  unfold average
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- An unused independent coordinate has no effect on an average. -/
theorem average_prod_left {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℝ) : average (fun z : A × B => f z.1) = average f := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := B)
  unfold average
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Fintype.card_prod, Nat.cast_mul]
  simpa only [mul_comm (Fintype.card A : ℝ) (Fintype.card B : ℝ)] using
    mul_div_mul_left (∑ i, f i) (Fintype.card A : ℝ) hb

/-- Surjective linear maps send the full uniform law to the full uniform law. -/
theorem average_surjective_linear {K A B : Type*} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [Fintype A] [Fintype B] (f : A →ₗ[K] B) (hf : Function.Surjective f) (g : B → ℝ) :
    average (fun a => g (f a)) = average g := by
  classical
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  calc
    _ = average (fun z : B × LinearMap.ker f => g z.1) :=
      average_equiv (surjectiveEquivProdKer f hf) (fun z => g z.1)
    _ = _ := average_prod_left g

variable {W ι : Type*} [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W]
  [Fintype W] [Fintype ι]

/-- Sum the actual subspace vectors in the ambient vector space. -/
def sumMap (L : ι → Submodule F₂ W) : (∀ i, L i) →ₗ[F₂] W :=
  LinearMap.lsum F₂ (fun i => L i) F₂ (fun i => (L i).subtype)

omit [FiniteDimensional F₂ W] [Fintype W] in
@[simp] theorem sumMap_apply (L : ι → Submodule F₂ W) (z : ∀ i, L i) :
    sumMap L z = ∑ i, (z i : W) := by
  simp [sumMap, LinearMap.lsum_apply]

omit [FiniteDimensional F₂ W] [Fintype W] in
/-- Direct-sum independence makes the actual summation map injective. -/
theorem sumMap_injective (L : ι → Submodule F₂ W) (hL : iSupIndep L) :
    Function.Injective (sumMap L) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  funext i
  apply Subtype.ext
  have hrest : (∑ j ∈ Finset.univ.erase i, (z j : W)) ∈ ⨆ j, ⨆ (_ : j ≠ i), L j := by
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem
      (Finset.mem_erase.mp hj).1 (z j).2)
  have heq : (∑ j ∈ Finset.univ.erase i, (z j : W)) + (z i : W) = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simpa only [sumMap_apply] using hz
  have hother : (z i : W) ∈ ⨆ j, ⨆ (_ : j ≠ i), L j := by
    rw [eq_neg_of_add_eq_zero_right heq]
    exact Submodule.neg_mem _ hrest
  exact (Submodule.disjoint_def.mp ((iSupIndep_def.mp hL) i)) (z i : W) (z i).2 hother

/-- Simultaneously restrict an ambient dual vector to every local space. -/
def restrictions (L : ι → Submodule F₂ W) :
    Module.Dual F₂ W →ₗ[F₂] (∀ i, Module.Dual F₂ (L i)) :=
  LinearMap.pi fun i => (L i).dualRestrict

omit [FiniteDimensional F₂ W] [Fintype W] in
/-- Every tuple of local assignments extends when the local spaces form a direct sum. -/
theorem restrictions_surjective (L : ι → Submodule F₂ W) (hL : iSupIndep L) :
    Function.Surjective (restrictions L) := by
  classical
  intro a
  let f : Module.Dual F₂ (∀ i, L i) := LinearMap.lsum F₂ (fun i => L i) F₂ a
  obtain ⟨x, hx⟩ := LinearMap.dualMap_surjective_of_injective (sumMap_injective L hL) f
  refine ⟨x, ?_⟩
  funext i
  ext v
  change x (v : W) = a i v
  have he := LinearMap.congr_fun hx (Pi.single i v)
  simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply, sumMap,
    LinearMap.lsum_piSingle, Submodule.subtype_apply, f] using he

/-- Exact density of the zero assignment in a local dual space. -/
theorem dual_zero_density (L : Submodule F₂ W) :
    Finite.density (fun x : Module.Dual F₂ L => x = 0) =
      1 / (2 : ℝ) ^ Module.finrank F₂ L := by
  classical
  have hc : Fintype.card (Module.Dual F₂ L) = 2 ^ Module.finrank F₂ L := by
    have hh := Module.natCard_eq_pow_finrank (K := F₂) (V := Module.Dual F₂ L)
    simpa only [Nat.card_eq_fintype_card, ZMod.card, Subspace.dual_finrank_eq] using hh
  have hcount : Finite.count (fun x : Module.Dual F₂ L => x = 0) = 1 := by
    unfold Finite.count
    rw [Finset.sum_eq_single 0]
    · norm_num
    · intro x _ hx
      exact if_neg hx
    · simp
  rw [Finite.density, hcount, hc, Nat.cast_pow, Nat.cast_ofNat]

/-- The direct-sum cylinder factors have their exact product expectation. -/
theorem average_cylinder_product (L : ι → Submodule F₂ W) (hL : iSupIndep L) :
    average (fun x : Module.Dual F₂ W =>
      ∏ i, (1 - indicator (Cylinder (L i) 0) x / 2)) =
        ∏ i, (1 - (1 / (2 : ℝ) ^ Module.finrank F₂ (L i)) / 2) := by
  classical
  let f (i : ι) (a : Module.Dual F₂ (L i)) : ℝ :=
    1 - indicator (fun z : Module.Dual F₂ (L i) => z = 0) a / 2
  have hpoint : (fun x : Module.Dual F₂ W => ∏ i, (1 - indicator (Cylinder (L i) 0) x / 2)) =
      fun x => ∏ i, f i (restrictions L x i) := by
    rfl
  rw [hpoint]
  change average (fun x => (fun z : ∀ i, Module.Dual F₂ (L i) => ∏ i, f i (z i))
    (restrictions L x)) = _
  rw [average_surjective_linear (restrictions L) (restrictions_surjective L hL)
    (fun z => ∏ i, f i (z i)), PackingProduct.average_pi_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hh : average (f i) = 1 - Finite.density (fun a : Module.Dual F₂ (L i) => a = 0) / 2 := by
    simp only [f, div_eq_mul_inv]
    rw [average_sub, average_const, average_mul_right, average_indicator]
  rw [hh, dual_zero_density]

omit [Fintype W] in
/-- A zero cylinder in the double dual is pointwise zero evaluation on the subspace. -/
theorem cylinder_eval_iff (L : Submodule F₂ (Module.Dual F₂ W)) (x : W) :
    Cylinder L 0 (Module.evalEquiv F₂ W x) ↔ ∀ f ∈ L, f x = 0 := by
  constructor
  · intro h f hf
    exact LinearMap.congr_fun h ⟨f, hf⟩
  · intro h
    ext f
    exact h f f.2

/-- Evaluation on the original finite space has the same exact product law. -/
theorem average_evaluation_product
    (L : ι → Submodule F₂ (Module.Dual F₂ W)) (hL : iSupIndep L) :
    average (fun x : W =>
      ∏ i, (1 - indicator (fun y => ∀ f ∈ L i, f y = 0) x / 2)) =
        ∏ i, (1 - (1 / (2 : ℝ) ^ Module.finrank F₂ (L i)) / 2) := by
  classical
  have heq : (fun x : W => ∏ i, (1 - indicator (fun y => ∀ f ∈ L i, f y = 0) x / 2)) =
      fun x => ∏ i, (1 - indicator (Cylinder (L i) 0) (Module.evalEquiv F₂ W x) / 2) := by
    funext x
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : ∀ f ∈ L i, f x = 0
    · simp only [indicator, cylinder_eval_iff, if_pos h]
    · simp only [indicator, cylinder_eval_iff, if_neg h]
  rw [heq]
  change average (fun x => (fun y : Module.Dual F₂ (Module.Dual F₂ W) =>
    ∏ i, (1 - indicator (Cylinder (L i) 0) y / 2)) (Module.evalEquiv F₂ W x)) = _
  calc
    _ = average (fun y : Module.Dual F₂ (Module.Dual F₂ W) =>
        ∏ i, (1 - indicator (Cylinder (L i) 0) y / 2)) :=
      average_equiv (Module.evalEquiv F₂ W).toEquiv
        (fun y => ∏ i, (1 - indicator (Cylinder (L i) 0) y / 2))
    _ = _ := average_cylinder_product L hL

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingIndependence
