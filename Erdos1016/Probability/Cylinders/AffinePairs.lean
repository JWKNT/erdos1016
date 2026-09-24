import Erdos1016.Probability.Cylinders.Affine

set_option autoImplicit false

/-!
# Intersections of affine cylinders

Compatible assignments on two subspaces combine into one assignment on their
sum.  The intersection probability is therefore controlled by the dimension
of that sum; the dimension identity for `sup` and `inf` gives the common-mode
factor in the paper's pair formula.
-/

noncomputable section

namespace Erdos1016.Proof.AffineCylinderPairs

open Erdos1016.Proof.AffineCylinders hiding F₂

abbrev F₂ := Erdos1016.Proof.AffineCylinders.F₂

variable {W : Type*} [AddCommGroup W] [Module F₂ W]
  [FiniteDimensional F₂ W] [Fintype W] [Fintype F₂]

def SumSubspace (L M : Submodule F₂ W) : Submodule F₂ W := L ⊔ M
def CommonSubspace (L M : Submodule F₂ W) : Submodule F₂ W := L ⊓ M

/-- The canonical inclusions of two subspaces into their sum. -/
def leftIncl (L M : Submodule F₂ W) : L →ₗ[F₂] SumSubspace L M :=
  Submodule.inclusion le_sup_left

def rightIncl (L M : Submodule F₂ W) : M →ₗ[F₂] SumSubspace L M :=
  Submodule.inclusion le_sup_right

/-- Assignments on `L` and `M` are compatible if one linear assignment on
their sum restricts to both of them. -/
def Compatible (L M : Submodule F₂ W) (a : Module.Dual F₂ L)
    (b : Module.Dual F₂ M) : Prop :=
  ∃ c : Module.Dual F₂ (SumSubspace L M),
    c.comp (leftIncl L M) = a ∧ c.comp (rightIncl L M) = b

/-- A cylinder on the sum is exactly the conjunction of its two restrictions. -/
theorem cylinder_sup_iff (L M : Submodule F₂ W)
    (c : Module.Dual F₂ (SumSubspace L M)) (x : Module.Dual F₂ W) :
    Cylinder (SumSubspace L M) c x ↔
      Cylinder L (c.comp (leftIncl L M)) x ∧
        Cylinder M (c.comp (rightIncl L M)) x := by
  constructor
  · intro h
    constructor
    · apply LinearMap.ext
      intro l
      have hh := congrArg (fun f : Module.Dual F₂ (SumSubspace L M) => f (leftIncl L M l)) h
      simpa [Cylinder, Submodule.dualRestrict_apply] using hh
    · apply LinearMap.ext
      intro m
      have hh := congrArg (fun f : Module.Dual F₂ (SumSubspace L M) => f (rightIncl L M m)) h
      simpa [Cylinder, Submodule.dualRestrict_apply] using hh
  · rintro ⟨hL, hM⟩
    apply LinearMap.ext
    intro z
    rcases Submodule.mem_sup.mp z.2 with ⟨l, hl, m, hm, hlm⟩
    have hl' : x l = c ⟨l, (le_sup_left : L ≤ L ⊔ M) hl⟩ := by
      have hh := congrArg (fun f : Module.Dual F₂ L => f ⟨l, hl⟩) hL
      simpa [Cylinder, Submodule.dualRestrict_apply] using hh
    have hm' : x m = c ⟨m, (le_sup_right : M ≤ L ⊔ M) hm⟩ := by
      have hh := congrArg (fun f : Module.Dual F₂ M => f ⟨m, hm⟩) hM
      simpa [Cylinder, Submodule.dualRestrict_apply] using hh
    change x z.1 = c z
    rw [← hlm]
    simp only [map_add, hl', hm']
    calc
      c ⟨l, (le_sup_left : L ≤ L ⊔ M) hl⟩ +
          c ⟨m, (le_sup_right : M ≤ L ⊔ M) hm⟩ =
          c (⟨l, (le_sup_left : L ≤ L ⊔ M) hl⟩ +
            ⟨m, (le_sup_right : M ≤ L ⊔ M) hm⟩) := by rw [map_add]
      _ = c z := congrArg c (Subtype.ext hlm)

/-- For compatible assignments, the pair intersection is a single cylinder
on the sum, hence has probability `2^(-dim(L+M))`. -/
theorem compatible_pair_probability (L M : Submodule F₂ W)
    (a : Module.Dual F₂ L) (b : Module.Dual F₂ M)
    (hcompat : Compatible L M a b) :
    probability (fun x => Cylinder L a x ∧ Cylinder M b x) =
      1 / (2 : ℝ) ^ Module.finrank F₂ (SumSubspace L M) := by
  classical
  obtain ⟨c, hcL, hcM⟩ := hcompat
  have hevents : ∀ x, (Cylinder L a x ∧ Cylinder M b x) ↔
      Cylinder (SumSubspace L M) c x := by
    intro x
    rw [cylinder_sup_iff]
    simp [hcL, hcM]
  have hcards :
      Nat.card {x : Module.Dual F₂ W //
        Cylinder L a x ∧ Cylinder M b x} =
      Nat.card {x : Module.Dual F₂ W // Cylinder (SumSubspace L M) c x} := by
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) hevents)
  rw [probability, hcards]
  exact cylinder_probability (SumSubspace L M) c

/-- Any point in a pair intersection induces a compatible assignment on the
sum, by restricting that point to the sum. -/
theorem pair_nonempty_implies_compatible (L M : Submodule F₂ W)
    (a : Module.Dual F₂ L) (b : Module.Dual F₂ M)
    (h : ∃ x, Cylinder L a x ∧ Cylinder M b x) : Compatible L M a b := by
  classical
  obtain ⟨x, hL, hM⟩ := h
  let c : Module.Dual F₂ (SumSubspace L M) := (SumSubspace L M).dualRestrict x
  have hc : Cylinder (SumSubspace L M) c x := rfl
  have ⟨hcL, hcM⟩ := (cylinder_sup_iff L M c x).mp hc
  have hcLeq : L.dualRestrict x = c.comp (leftIncl L M) := by
    simpa [Cylinder] using hcL
  have hLeqa : L.dualRestrict x = a := by simpa [Cylinder] using hL
  have hca : c.comp (leftIncl L M) = a := by
    exact hcLeq.symm.trans hLeqa
  have hcMeq : M.dualRestrict x = c.comp (rightIncl L M) := by
    simpa [Cylinder] using hcM
  have hMeqb : M.dualRestrict x = b := by simpa [Cylinder] using hM
  have hcb : c.comp (rightIncl L M) = b := by
    exact hcMeq.symm.trans hMeqb
  exact ⟨c, hca, hcb⟩

/-- Incompatible assignments give disjoint affine cylinders and hence zero
joint probability. -/
theorem incompatible_pair_probability (L M : Submodule F₂ W)
    (a : Module.Dual F₂ L) (b : Module.Dual F₂ M)
    (hcompat : ¬ Compatible L M a b) :
    probability (fun x => Cylinder L a x ∧ Cylinder M b x) = 0 := by
  classical
  have hempty : IsEmpty {x : Module.Dual F₂ W //
      Cylinder L a x ∧ Cylinder M b x} := by
    refine ⟨fun x => hcompat (pair_nonempty_implies_compatible L M a b ?_)⟩
    exact ⟨x.1, x.2⟩
  have hnum : Nat.card {x : Module.Dual F₂ W //
      Cylinder L a x ∧ Cylinder M b x} = 0 := by
    letI := hempty
    simp [Nat.card_eq_fintype_card]
  unfold probability
  simp [hnum]

/-- The compatible pair formula, with the common mode retained explicitly. -/
theorem compatible_pair_common_mode (L M : Submodule F₂ W)
    (a : Module.Dual F₂ L) (b : Module.Dual F₂ M)
    (hcompat : Compatible L M a b) :
    probability (fun x => Cylinder L a x ∧ Cylinder M b x) =
      (2 : ℝ) ^ Module.finrank F₂ (CommonSubspace L M) *
        probability (Cylinder L a) * probability (Cylinder M b) := by
  rw [compatible_pair_probability L M a b hcompat,
      cylinder_probability L a, cylinder_probability M b]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq L M
  have hdim' :
      Module.finrank F₂ (SumSubspace L M) +
        Module.finrank F₂ (CommonSubspace L M) =
        Module.finrank F₂ L + Module.finrank F₂ M := by
    simpa [SumSubspace, CommonSubspace] using hdim
  have hpow :
      (2 : ℝ) ^ Module.finrank F₂ (SumSubspace L M) *
        (2 : ℝ) ^ Module.finrank F₂ (CommonSubspace L M) =
      (2 : ℝ) ^ Module.finrank F₂ L * (2 : ℝ) ^ Module.finrank F₂ M := by
    rw [← pow_add, ← pow_add, hdim']
  have h1 : (2 : ℝ) ^ Module.finrank F₂ (SumSubspace L M) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ Module.finrank F₂ (CommonSubspace L M) ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ Module.finrank F₂ L ≠ 0 := by positivity
  have h4 : (2 : ℝ) ^ Module.finrank F₂ M ≠ 0 := by positivity
  field_simp
  nlinarith

end Erdos1016.Proof.AffineCylinderPairs
