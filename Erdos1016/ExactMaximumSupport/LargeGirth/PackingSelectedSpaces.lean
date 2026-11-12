import Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelection
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingIndependence
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingProbabilityBounds

set_option autoImplicit false

/-!
# Independent local spaces under a two-fifths product bound

The input is the actual uniform average of the zero-space penalties. The
selection, independent product law, and bounds for zero spaces are proved.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelectedSpaces

open BoundaryDecay

variable {ι W : Type*} [DecidableEq ι]
  [AddCommGroup W] [Module F₂ W] [FiniteDimensional F₂ W] [Fintype W]

local instance selectedSpacesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def penalty (L : Submodule F₂ (Module.Dual F₂ W)) (x : W) : ℝ :=
  1 - indicator (fun y => ∀ f ∈ L, f y = 0) x / 2

omit [FiniteDimensional F₂ W] in
theorem penalty_bounds (L : Submodule F₂ (Module.Dual F₂ W)) (x : W) :
    0 ≤ penalty L x ∧ penalty L x ≤ 1 := by
  unfold penalty indicator
  split_ifs <;> norm_num

omit [FiniteDimensional F₂ W] in
theorem product_antitone (L : ι → Submodule F₂ (Module.Dual F₂ W))
    {A s : Finset ι} (hA : A ⊆ s) (x : W) :
    (∏ i ∈ s, penalty (L i) x) ≤ ∏ i ∈ A, penalty (L i) x := by
  rw [← Finset.prod_sdiff hA]
  exact mul_le_of_le_one_left (Finset.prod_nonneg fun i _ => (penalty_bounds (L i) x).1)
    (Finset.prod_le_one (fun i _ => (penalty_bounds (L i) x).1)
      (fun i _ => (penalty_bounds (L i) x).2))

theorem average_independent (L : ι → Submodule F₂ (Module.Dual F₂ W))
    (A : Finset ι) (hA : A.SupIndep L) :
    average (fun x : W => ∏ i ∈ A, penalty (L i) x) =
      ∏ i ∈ A, (1 - (1 / (2 : ℝ)^Module.finrank F₂ (L i)) / 2) := by
  have h := PackingIndependence.average_evaluation_product
    (fun i : A => L i.1) hA.independent
  calc
    _ = average (fun x : W => ∏ i : A, penalty (L i.1) x) := by
      apply congrArg average
      funext x
      exact (Finset.prod_coe_sort A (fun i => penalty (L i) x)).symm
    _ = ∏ i : A, (1 - (1 / (2 : ℝ)^Module.finrank F₂ (L i.1)) / 2) := h
    _ = _ := Finset.prod_coe_sort A
      (fun i => (1 - (1 / (2 : ℝ)^Module.finrank F₂ (L i)) / 2))

theorem factor_bounds (n : ℕ) :
    0 ≤ 1 - (1 / (2 : ℝ)^n) / 2 ∧ 1 - (1 / (2 : ℝ)^n) / 2 ≤ 1 := by
  have hp : (1 : ℝ) ≤ (2 : ℝ)^n := one_le_pow₀ (by norm_num)
  have hi : 1 / (2 : ℝ)^n ≤ 1 := (div_le_one (by positivity)).mpr hp
  have hi0 : 0 ≤ 1 / (2 : ℝ)^n := by positivity
  constructor <;> linarith

theorem factor_le (n d : ℕ) (hd : 1 ≤ d) (hn : n ≤ d - 1) :
    1 - (1 / (2 : ℝ)^n) / 2 ≤ 1 - 1 / (2 : ℝ)^d := by
  have hp : (2 : ℝ)^(n + 1) ≤ (2 : ℝ)^d :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2^(n+1)) hp
  have he : (1 / (2 : ℝ)^n) / 2 = 1 / (2 : ℝ)^(n+1) := by
    rw [pow_succ, div_div]
  rw [he]
  linarith

theorem average_independent_le (L : ι → Submodule F₂ (Module.Dual F₂ W))
    (A : Finset ι) (hA : A.SupIndep L) (d : ℕ) (hd : 1 ≤ d)
    (hdim : ∀ i ∈ A, Module.finrank F₂ (L i) ≤ d - 1) :
    average (fun x : W => ∏ i ∈ A, penalty (L i) x) ≤
      (1 - 1 / (2 : ℝ)^d)^A.card := by
  rw [average_independent L A hA]
  calc
    _ ≤ ∏ _i ∈ A, (1 - 1 / (2 : ℝ)^d) := Finset.prod_le_prod
      (fun i _ => (factor_bounds (Module.finrank F₂ (L i))).1)
      (fun i hi => factor_le _ d hd (hdim i hi))
    _ = _ := by simp

theorem zero_spaces_card_le_one (s : Finset ι)
    (L : ι → Submodule F₂ (Module.Dual F₂ W))
    (hprob : (2 / 5 : ℝ) ≤ average (fun x : W => ∏ i ∈ s, penalty (L i) x)) :
    (s.filter fun i => L i = ⊥).card ≤ 1 := by
  let Z := s.filter fun i => L i = ⊥
  have hpoint (x : W) : (∏ i ∈ Z, penalty (L i) x) = (1 / 2 : ℝ)^Z.card := by
    calc
      _ = ∏ _i ∈ Z, (1 / 2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hz := (Finset.mem_filter.mp hi).2
        norm_num [penalty, indicator, hz]
      _ = _ := by simp
  have hh : (2 / 5 : ℝ) ≤ (1 / 2 : ℝ)^Z.card := by
    calc
      _ ≤ average (fun x : W => ∏ i ∈ s, penalty (L i) x) := hprob
      _ ≤ average (fun x : W => ∏ i ∈ Z, penalty (L i) x) :=
        average_mono (product_antitone L (Finset.filter_subset _ _) )
      _ = _ := by simp only [hpoint, average_const]
  exact PackingProbabilityBounds.zero_space_count_le_one Z.card hh

/-- Every omitted nonzero space meets the selected sum. The selected family
has fewer than `2^d` members; at most one candidate space is zero. -/
theorem exists_selected (s : Finset ι) (L : ι → Submodule F₂ (Module.Dual F₂ W))
    (d : ℕ) (hd : 1 ≤ d)
    (hdim : ∀ i ∈ s, Module.finrank F₂ (L i) ≤ d - 1)
    (hprob : (2 / 5 : ℝ) ≤ average (fun x : W => ∏ i ∈ s, penalty (L i) x)) :
    ∃ A ⊆ s, A.SupIndep L ∧ (∀ i ∈ A, L i ≠ ⊥) ∧ A.card < 2^d ∧
      (∀ i ∈ s, i ∉ A → L i = ⊥ ∨ ¬ Disjoint (L i) (A.sup L)) ∧
      (s.filter fun i => L i = ⊥).card ≤ 1 := by
  let S := s.filter fun i => L i ≠ ⊥
  obtain ⟨A, hAS, hind, hrel⟩ := PackingSelection.exists_maximal_independent S L
  have hAs : A ⊆ s := hAS.trans (Finset.filter_subset _ _)
  have hAprob : (2 / 5 : ℝ) ≤ (1 - 1 / (2 : ℝ)^d)^A.card := by
    calc
      _ ≤ average (fun x : W => ∏ i ∈ s, penalty (L i) x) := hprob
      _ ≤ average (fun x : W => ∏ i ∈ A, penalty (L i) x) :=
        average_mono (product_antitone L hAs)
      _ ≤ _ := average_independent_le L A hind d hd (fun i hi => hdim i (hAs hi))
  refine ⟨A, hAs, hind, fun i hi => (Finset.mem_filter.mp (hAS hi)).2,
    PackingProbabilityBounds.selected_card_lt_two_pow d A.card hAprob, ?_,
    zero_spaces_card_le_one s L hprob⟩
  intro i hi hiA
  by_cases hz : L i = ⊥
  · exact Or.inl hz
  · exact Or.inr (hrel i (Finset.mem_filter.mpr ⟨hi, hz⟩) hiA)

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingSelectedSpaces
