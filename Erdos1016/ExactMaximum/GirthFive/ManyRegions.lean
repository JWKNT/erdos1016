import Erdos1016.PolynomialBound.Product

set_option autoImplicit false

/-!
# A family of disjoint regions multiplies

`PolynomialBound.Product.forest_density_le_mul` is the product law for two disjoint regions.
This file has the same law for a finite family `U i` of pairwise disjoint regions and for the
words `x + f`, where `x` is a uniform even word and `f` is a fixed word. Suppose that, for every
even word `x`, the words `x + z + f` with `z` an even word on the internal edges of `U i` are
forests on these edges with proportion at most `a i`. Then `x + f` is a forest with probability
at most the product of the `a i` (`affine_forest_density_le_prod`).

The proof is an induction over the family. One step averages over the even words of one region.
These words vanish on the internal edges of the other regions, so the other factors do not
change.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.GirthFive

open FiniteMultiGraph BoundaryDecay

local instance manyRegionsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- The indicator of the event that `x + f` is a forest on the internal edges of `U`. -/
def regionIndicator (f : G.EdgeWord) (U : Finset G.Vertex) (x : G.CycleSpace) : ℝ :=
  if G.IsForestWord (G.restrictEdges (G.internalEdges U) (x.1 + f)) then 1 else 0

theorem regionIndicator_nonneg (f : G.EdgeWord) (U : Finset G.Vertex) (x : G.CycleSpace) :
    0 ≤ regionIndicator G f U x := by
  unfold regionIndicator
  split_ifs <;> norm_num

/-- An even word on the internal edges of a disjoint region does not change the indicator. -/
theorem regionIndicator_add_disjoint (f : G.EdgeWord) (U V : Finset G.Vertex)
    (hUV : Disjoint V U) (x : G.CycleSpace) (z : G.internalCycleSpace V) :
    regionIndicator G f U (x + z.1) = regionIndicator G f U x := by
  have hw : G.restrictEdges (G.internalEdges U) ((x + z.1).1 + f) =
      G.restrictEdges (G.internalEdges U) (x.1 + f) := by
    funext e
    by_cases he : e ∈ G.internalEdges U
    · have hz : z.1.1 e = 0 := G.internal_vanish_on_disjoint V U hUV z e he
      have hval : ((x + z.1).1 + f) e = (x.1 + f) e := by
        show x.1 e + z.1.1 e + f e = x.1 e + f e
        rw [hz, add_zero]
      simp only [restrictEdges, he, if_true, hval]
    · simp [restrictEdges, he]
  unfold regionIndicator
  rw [hw]

/-- The sum of the indicator over the even words of the region itself, from the density bound. -/
theorem sum_regionIndicator_le (f : G.EdgeWord) (U : Finset G.Vertex) (a : ℝ)
    (h : ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace U =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U) (x.1 + z.1.1 + f))) ≤ a)
    (x : G.CycleSpace) :
    (∑ z : G.internalCycleSpace U, regionIndicator G f U (x + z.1)) ≤
      a * Fintype.card (G.internalCycleSpace U) := by
  have hW : (0 : ℝ) < Fintype.card (G.internalCycleSpace U) := by
    exact_mod_cast Fintype.card_pos
  have h' : average (indicator (fun z : G.internalCycleSpace U =>
      G.IsForestWord (G.restrictEdges (G.internalEdges U) (x.1 + z.1.1 + f)))) ≤ a := h x
  unfold average at h'
  have hsum := (div_le_iff₀ hW).mp h'
  refine le_trans (le_of_eq ?_) hsum
  apply Finset.sum_congr rfl
  intro z _
  rfl

/-- **Product over a part of the family.** -/
theorem sum_prod_regionIndicator_le {ι : Type*} [DecidableEq ι] (f : G.EdgeWord)
    (U : ι → Finset G.Vertex) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace (U i) =>
      G.IsForestWord (G.restrictEdges (G.internalEdges (U i)) (x.1 + z.1.1 + f))) ≤ a i)
    (s : Finset ι) :
    (∑ x : G.CycleSpace, ∏ i ∈ s, regionIndicator G f (U i) x) ≤
      (∏ i ∈ s, a i) * Fintype.card G.CycleSpace := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hW : (0 : ℝ) < Fintype.card (G.internalCycleSpace (U j)) := by
      exact_mod_cast Fintype.card_pos
    -- the product over `s` does not change under an even word of the region `j`
    have hrest (x : G.CycleSpace) (z : G.internalCycleSpace (U j)) :
        (∏ i ∈ s, regionIndicator G f (U i) (x + z.1)) =
          ∏ i ∈ s, regionIndicator G f (U i) x := by
      apply Finset.prod_congr rfl
      intro i hi
      have hij : j ≠ i := fun hji => hj (hji ▸ hi)
      exact regionIndicator_add_disjoint G f (U i) (U j) (hdisj j i hij) x z
    -- translation by an even word preserves the sum
    have hshift (z : G.internalCycleSpace (U j)) :
        (∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) (x + z.1)) =
          ∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) x :=
      Fintype.sum_equiv (Equiv.addRight z.1) _ _ (fun _ => rfl)
    have hcount : (Fintype.card (G.internalCycleSpace (U j)) : ℝ) *
        (∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) x) =
        ∑ x : G.CycleSpace, (∏ i ∈ s, regionIndicator G f (U i) x) *
          ∑ z : G.internalCycleSpace (U j), regionIndicator G f (U j) (x + z.1) := by
      calc
        _ = ∑ _z : G.internalCycleSpace (U j),
              ∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) x := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ∑ z : G.internalCycleSpace (U j),
              ∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) (x + z.1) := by
          apply Finset.sum_congr rfl
          intro z _
          exact (hshift z).symm
        _ = ∑ x : G.CycleSpace, ∑ z : G.internalCycleSpace (U j),
              ∏ i ∈ insert j s, regionIndicator G f (U i) (x + z.1) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.prod_insert hj, hrest x z, mul_comm]
    have hbound : (∑ x : G.CycleSpace, (∏ i ∈ s, regionIndicator G f (U i) x) *
          ∑ z : G.internalCycleSpace (U j), regionIndicator G f (U j) (x + z.1)) ≤
        ∑ x : G.CycleSpace, (∏ i ∈ s, regionIndicator G f (U i) x) *
          (a j * Fintype.card (G.internalCycleSpace (U j))) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (sum_regionIndicator_le G f (U j) (a j) (h j) x)
        (Finset.prod_nonneg fun i _ => regionIndicator_nonneg G f (U i) x)
    have hmain : (Fintype.card (G.internalCycleSpace (U j)) : ℝ) *
        (∑ x : G.CycleSpace, ∏ i ∈ insert j s, regionIndicator G f (U i) x) ≤
        (Fintype.card (G.internalCycleSpace (U j)) : ℝ) *
          ((∏ i ∈ insert j s, a i) * Fintype.card G.CycleSpace) := by
      rw [hcount]
      refine hbound.trans ?_
      rw [← Finset.sum_mul, Finset.prod_insert hj]
      have hih := mul_le_mul_of_nonneg_right ih
        (mul_nonneg (ha j) hW.le)
      nlinarith [hih]
    exact le_of_mul_le_mul_left hmain hW

/-- **Product of a family of regions.** If every parity class of each region of a pairwise
disjoint family has forest proportion at most `a i`, then the word `x + f`, with `x` a uniform
even word, is a forest with probability at most the product of the `a i`. -/
theorem affine_forest_density_le_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : G.EdgeWord) (U : ι → Finset G.Vertex) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace (U i) =>
      G.IsForestWord (G.restrictEdges (G.internalEdges (U i)) (x.1 + z.1.1 + f))) ≤ a i) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (x.1 + f)) ≤ ∏ i, a i := by
  have hV : (0 : ℝ) < Fintype.card G.CycleSpace := by
    exact_mod_cast Fintype.card_pos
  have hpoint (x : G.CycleSpace) :
      indicator (fun x : G.CycleSpace => G.IsForestWord (x.1 + f)) x ≤
        ∏ i, regionIndicator G f (U i) x := by
    by_cases hx : G.IsForestWord (x.1 + f)
    · have hall : ∀ i, regionIndicator G f (U i) x = 1 := by
        intro i
        unfold regionIndicator
        rw [if_pos (hx.restrictEdges (G.internalEdges (U i)))]
      simp only [indicator, if_pos hx, hall, Finset.prod_const_one, le_refl]
    · simp only [indicator, if_neg hx]
      exact Finset.prod_nonneg fun i _ => regionIndicator_nonneg G f (U i) x
  have hsum : (∑ x : G.CycleSpace,
      indicator (fun x : G.CycleSpace => G.IsForestWord (x.1 + f)) x) ≤
      (∏ i, a i) * Fintype.card G.CycleSpace :=
    (Finset.sum_le_sum fun x _ => hpoint x).trans
      (sum_prod_regionIndicator_le G f U hdisj a ha h Finset.univ)
  have hgoal : average (indicator (fun x : G.CycleSpace => G.IsForestWord (x.1 + f))) ≤
      ∏ i, a i := by
    unfold average
    exact (div_le_iff₀ hV).mpr hsum
  exact hgoal

end Erdos1016.ExactMaximum.GirthFive
