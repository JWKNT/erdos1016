import Erdos1016.Probability.Cylinders.RegionCycleEvents
import Erdos1016.Probability.Moments.SecondMoments
import Erdos1016.CycleSpace.Graphical.DisjointRegionCuts
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# The finite packing product in the ambient cycle space

Internal shifts use the actual even words supported on each region.
Disjoint regions have separate internal edge labels, including adjacent regions.
On a zero cut, only one internal shift gives a forest.
Averaging all internal shifts proves the packing product without a quotient model.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingProduct

open FiniteMultiGraph BoundaryDecay
local instance packingProductDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Uniform averages commute on two finite spaces. -/
theorem average_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  unfold average
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

/-- Independent uniform coordinates multiply. These are the full finite spaces. -/
theorem average_pi_prod {ι : Type*} [Fintype ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    average (fun z : ∀ i, A i => ∏ i, f i (z i)) = ∏ i, average (f i) := by
  unfold average
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

variable (G : FiniteMultiGraph)

/-- The local forest event under an actual internal even shift. -/
def localForest (U : Finset G.Vertex) (x : G.CycleSpace) (z : G.internalCycleSpace U) : Prop :=
  G.IsForestWord (G.restrictEdges (G.internalEdges U) (x.1 + z.1.1))

/-- The paper's factor uses the original labelled zero-cut event. -/
def cutFactor (U : Finset G.Vertex) (x : G.CycleSpace) : ℝ :=
  1 - indicator (DisjointRegionCuts.ZeroCut G U) x / 2

theorem cutFactor_nonneg (U : Finset G.Vertex) (x : G.CycleSpace) : 0 ≤ cutFactor G U x := by
  unfold cutFactor indicator
  split_ifs <;> norm_num

theorem cutFactor_le_one (U : Finset G.Vertex) (x : G.CycleSpace) : cutFactor G U x ≤ 1 := by
  unfold cutFactor indicator
  split_ifs <;> norm_num

/-- A zero cut makes the internal affine class the actual internal cycle space. -/
theorem local_density_eq_of_zeroCut (U : Finset G.Vertex) (x : G.CycleSpace)
    (hx : DisjointRegionCuts.ZeroCut G U x) :
    Finite.density (localForest G U x) = 1 / (Fintype.card (G.internalCycleSpace U) : ℝ) := by
  classical
  let a : G.internalCycleSpace U := G.restrictInternal U
    ⟨x, (G.mem_zeroCutSpace_iff U x).mpr hx⟩
  have heq (z : G.internalCycleSpace U) :
      G.restrictEdges (G.internalEdges U) (x.1 + z.1.1) = (a + z).1.1 := by
    ext e
    change (if e ∈ G.internalEdges U then x.1 e + z.1.1 e else 0) =
      (if e ∈ G.internalEdges U then x.1 e else 0) + z.1.1 e
    by_cases he : e ∈ G.internalEdges U <;> simp [he, z.2 e]
  have hiff (z : G.internalCycleSpace U) : localForest G U x z ↔ a + z = 0 := by
    unfold localForest
    rw [heq]
    constructor
    · intro hf
      have hz := G.word_eq_zero_of_boundary_zero_of_forest (a + z).1.1 (a + z).1.2 hf
      exact Subtype.ext (Subtype.ext hz)
    · intro hz
      rw [hz]
      exact G.zero_isForestWord
  calc
    _ = Finite.density (fun z : G.internalCycleSpace U => z = 0) :=
      Finite.density_equiv (Equiv.addLeft a) hiff
    _ = _ := by
      have hc : Finite.count (fun z : G.internalCycleSpace U => z = 0) = 1 := by
        unfold Finite.count
        rw [Finset.sum_eq_single 0]
        · norm_num
        · intro z _ hz
          exact if_neg hz
        · simp
      rw [Finite.density, hc]

/-- A cyclic region loses at least one half on its zero-cut event. -/
theorem local_density_le_cutFactor (U : Finset G.Vertex)
    (hcyc : ∃ z : G.internalCycleSpace U, z ≠ 0) (x : G.CycleSpace) :
    Finite.density (localForest G U x) ≤ cutFactor G U x := by
  by_cases hx : DisjointRegionCuts.ZeroCut G U x
  · rw [local_density_eq_of_zeroCut G U x hx]
    have hh := G.internalCycleFactor_ge_half U hcyc
    unfold internalCycleFactor at hh
    simp only [cutFactor, indicator, if_pos hx]
    linarith
  · simpa only [cutFactor, indicator, if_neg hx, zero_div, sub_zero] using
      Finite.density_le_one (localForest G U x)

/-- The actual packing product inequality. Connectedness and a degree bound
are unnecessary once each region has a nonzero internal even word. -/
theorem forest_density_le_cut_product {ι : Type*} [Fintype ι]
    (U : ι → Finset G.Vertex)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcyc : ∀ i, ∃ z : G.internalCycleSpace (U i), z ≠ 0)
    (E : Finset G.Edge) (hE : ∀ i, G.internalEdges (U i) ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      average (fun x : G.CycleSpace => ∏ i, cutFactor G (U i) x) := by
  classical
  let A := ∀ i, G.internalCycleSpace (U i)
  let shift (z : A) : G.CycleSpace := ∑ i, (z i).1
  let f : G.CycleSpace → ℝ :=
    indicator (fun x => G.IsForestWord (G.restrictEdges E x.1))
  let g (x : G.CycleSpace) (i : ι) : G.internalCycleSpace (U i) → ℝ :=
    indicator (localForest G (U i) x)
  have hrestrict (x : G.CycleSpace) (z : A) (i : ι) :
      G.restrictEdges (G.internalEdges (U i)) (x + shift z).1 =
        G.restrictEdges (G.internalEdges (U i)) (x.1 + (z i).1.1) := by
    ext e
    by_cases he : e ∈ G.internalEdges (U i)
    · have hsum : (shift z).1 e = (z i).1.1 e := by
        change (∑ j, (z j).1).1 e = _
        simp only [Submodule.coe_sum, Finset.sum_apply]
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact G.internal_vanish_on_disjoint (U j) (U i) (hdisj hji) (z j) e he
        · simp
      simp only [restrictEdges, he, if_true]
      change x.1 e + (shift z).1 e = x.1 e + (z i).1.1 e
      rw [hsum]
    · simp [restrictEdges, he]
  have hpoint (x : G.CycleSpace) (z : A) : f (x + shift z) ≤ ∏ i, g x i (z i) := by
    by_cases hx : G.IsForestWord (G.restrictEdges E (x + shift z).1)
    · have hall (i : ι) : localForest G (U i) x (z i) := by
        unfold localForest
        rw [← hrestrict]
        apply hx.mono
        intro e he
        by_cases hm : e ∈ G.internalEdges (U i)
        · simpa only [restrictEdges, hm, hE i hm, if_true] using he
        · simp [restrictEdges, hm] at he
      simp only [f, g, indicator, hx, hall, ↓reduceIte, Finset.prod_const_one, le_refl]
    · have hz : f (x + shift z) = 0 := by simp only [f, indicator, if_neg hx]
      rw [hz]
      apply Finset.prod_nonneg
      intro i _
      simp only [g, indicator]
      split_ifs <;> norm_num
  have hrow (x : G.CycleSpace) :
      average (fun z : A => f (x + shift z)) ≤ ∏ i, cutFactor G (U i) x := by
    calc
      _ ≤ average (fun z : A => ∏ i, g x i (z i)) := average_mono (hpoint x)
      _ = ∏ i, average (g x i) := average_pi_prod (g x)
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finite.density_nonneg (localForest G (U i) x)
        · intro i _
          exact local_density_le_cutFactor G (U i) (hcyc i) x
  have htranslate (z : A) : average (fun x => f (x + shift z)) = average f := by
    unfold average
    congr 1
    exact Fintype.sum_equiv (Equiv.addRight (shift z)) _ _ (fun _ => rfl)
  change average f ≤ _
  calc
    _ = average (fun _z : A => average f) := (average_const (average f)).symm
    _ = average (fun z : A => average (fun x => f (x + shift z))) := by
      simp only [htranslate]
    _ = average (fun x => average (fun z : A => f (x + shift z))) :=
      (average_comm (fun x z => f (x + shift z))).symm
    _ ≤ _ := average_mono hrow

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingProduct
