import Erdos1016.Cycles.Counting.WeightedVertexLoad

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CycleNeighborhoodLoad

open scoped BigOperators
open BoundaryDecay
open GraphBalls

/-- An anchor may be a previously deleted cycle. It need not belong to the
residual graph whose cycles contribute the load. -/
theorem anchor_neighbor_mass_le
    {α V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (F : Finset α) (support : α → Finset V) (mass : α → ℝ)
    (anchor : Finset V) (q L : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hdegree : ∀ v, J.degree v ≤ 3)
    (hload : ∀ v, vertexLoad F support mass v ≤ A)
    (hmass : ∀ C ∈ F, 0 ≤ mass C) (hanchor : anchor.card ≤ L) :
    (∑ D ∈ F, if ∃ v ∈ graphBall J anchor q, v ∈ support D then mass D else 0) ≤
      (3 : ℝ) * L * 2 ^ q * A := by
  classical
  have hcard : (graphBall J anchor q).card ≤ 3 * L * 2 ^ q :=
    (graphBall_card_le J anchor q hdegree).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hanchor))
  have h := touching_partner_mass_le (fun u v : V => u = v) F support mass
    hmass A hA hload 1 (3 * L * 2 ^ q) (graphBall J anchor q)
    (by
      intro u _
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' : u = a := by simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      have hb' : u = b := by simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hb
      exact ha'.symm.trans hb') hcard
  simpa [Touch, Nat.cast_mul, Nat.cast_pow, mul_assoc] using h

/-- A vertex-load estimate survives an injective embedding of the physical
vertices. This permits measuring proximity in the original ordinary graph,
while counting walks in its surviving core. -/
theorem vertexLoad_image_le
    {α V W : Type*} [DecidableEq V] [DecidableEq W]
    (F : Finset α) (support : α → Finset V) (mass : α → ℝ)
    (f : V → W) (hf : Function.Injective f) (A : ℝ) (hA : 0 ≤ A)
    (hload : ∀ v, vertexLoad F support mass v ≤ A) (v : W) :
    vertexLoad F (fun C => (support C).image f) mass v ≤ A := by
  classical
  by_cases hv : ∃ u, f u = v
  · obtain ⟨u, rfl⟩ := hv
    have hmem (C : α) : f u ∈ (support C).image f ↔ u ∈ support C := by
      exact Finset.mem_image.trans ⟨fun ⟨a, ha, he⟩ => hf he ▸ ha, fun hu => ⟨u, hu, rfl⟩⟩
    have heq : vertexLoad F (fun C => (support C).image f) mass (f u) =
        vertexLoad F support mass u := by
      unfold vertexLoad
      apply Finset.sum_congr rfl
      intro C _
      by_cases hu : u ∈ support C
      · simp only [if_pos hu, if_pos ((hmem C).mpr hu)]
      · simp only [if_neg hu, if_neg (fun h => hu ((hmem C).mp h))]
    rw [heq]
    exact hload u
  · have hmem (C : α) : v ∉ (support C).image f := by
      intro h
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
      exact hv ⟨u, hu⟩
    simpa only [vertexLoad, if_neg (hmem _), Finset.sum_const_zero] using hA





end Erdos1016.Proof.CycleNeighborhoodLoad
