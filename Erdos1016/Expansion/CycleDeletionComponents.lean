import Erdos1016.Expansion.SmallComponents

set_option autoImplicit false

/-!
# Local order bound from expansion and a component boundary budget

The FEW girth argument needs an order bound for each component left after
deleting a protector. This isolates the elementary expansion step: once the
component boundary is charged to the protector, expansion bounds its order.
The charging estimate itself depends on the component/protector geometry.
-/
noncomputable section

namespace Erdos1016.Proof.CycleDeletionComponents

open Erdos1016.SafeCore

variable {G : PhysicalGraph}






open Erdos1016.CycleSupply Erdos1016.BoundaryDecay

/-- The union of pairwise-disjoint selected cycle supports has cut at most
 the sum of their lengths. Chords can only lower each individual cut. -/
theorem cycleFamily_cut_le_sum_lengths
    (F : Finset G.CycleWord)
    (hdis : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hcubic : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3) :
    cutSize G (F.biUnion Cycle.vertices) ≤ ∑ C ∈ F, Erdos1016.BoundaryDecay.Cycle.length C := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [cutSize, ownerCut, crossing]
  | @insert C F hCF ih =>
      have hpair : ∀ A ∈ F, ∀ B ∈ F, A ≠ B →
          Disjoint (Cycle.vertices A) (Cycle.vertices B) := by
        intro A hA B hB hne
        exact hdis A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne
      have hCpair : ∀ A ∈ F, Disjoint (Cycle.vertices C) (Cycle.vertices A) := by
        intro A hA
        have hne : C ≠ A := fun heq => hCF (heq ▸ hA)
        exact hdis C (Finset.mem_insert_self C F) A (Finset.mem_insert_of_mem hA) hne
      have hdisUnion : Disjoint (Cycle.vertices C) (F.biUnion Cycle.vertices) := by
        apply Finset.disjoint_left.2
        intro v hvC hvF
        obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.1 hvF
        exact (Finset.disjoint_left.1 (hCpair A hA)) hvC hvA
      have hcut := cutSize_union G (Cycle.vertices C) (F.biUnion Cycle.vertices) hdisUnion
      have hCcut : cutSize G (Cycle.vertices C) ≤ Erdos1016.BoundaryDecay.Cycle.length C :=
        cycle_cut_le_length G C (hcubic C (Finset.mem_insert_self C F))
      have hFcut : cutSize G (F.biUnion Cycle.vertices) ≤ ∑ A ∈ F, Erdos1016.BoundaryDecay.Cycle.length A :=
        ih hpair (fun A hA => hcubic A (Finset.mem_insert_of_mem hA))
      have hresult : cutSize G ((insert C F).biUnion Cycle.vertices) ≤
          Erdos1016.BoundaryDecay.Cycle.length C + ∑ A ∈ F, Erdos1016.BoundaryDecay.Cycle.length A := by
        rw [Finset.biUnion_insert]
        omega
      simpa [Finset.sum_insert hCF] using hresult

/-- Componentwise Section 6 estimate. A component of the complement of at
most K disjoint selected cycles has boundary at most K L, hence order at most
K L / κ when it is small. -/
theorem small_component_card_le_cycle_budget
    (F : Finset G.CycleWord) (K L : ℕ) (κ : ℝ)
    (hκ : 0 < κ) (hExp : HasExpansion G Finset.univ κ)
    (hcard : F.card ≤ K)
    (hdis : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hcubic : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hlen : ∀ A ∈ F, Erdos1016.BoundaryDecay.Cycle.length A ≤ L)
    (C : Finset G.Vertex) (hC : C ∈ components G (F.biUnion Cycle.vertices)ᶜ)
    (hsmall : (C.card : ℝ) ≤ (G.vertexCount : ℝ) / 2) :
    (C.card : ℝ) ≤ ((K * L : ℕ) : ℝ) / κ := by
  have hcutComp : cutSize G C ≤ cutSize G (F.biUnion Cycle.vertices) :=
    component_cut_le_removed_cut G hC
  have hcutFamily := cycleFamily_cut_le_sum_lengths F hdis hcubic
  have hsum : (∑ A ∈ F, Erdos1016.BoundaryDecay.Cycle.length A) ≤ K * L := by
    calc
      _ ≤ ∑ _A ∈ F, L := by
        apply Finset.sum_le_sum
        intro A hA
        exact hlen A hA
      _ = F.card * L := by simp
      _ ≤ K * L := Nat.mul_le_mul_right L hcard
  have hcut : cutSize G C ≤ K * L := hcutComp.trans (hcutFamily.trans hsum)
  have hexp := small_region_expansion G κ hExp C hsmall
  have hcutR : (cutSize G C : ℝ) ≤ (K : ℝ) * L := by
    exact_mod_cast hcut
  have hmul : κ * (C.card : ℝ) ≤ (K : ℝ) * L := hexp.trans hcutR
  have hmul' : (C.card : ℝ) * κ ≤ (K : ℝ) * L := by simpa [mul_comm] using hmul
  have hdiv := (le_div_iff₀ hκ).2 hmul'
  simpa only [Nat.cast_mul] using hdiv

end Erdos1016.Proof.CycleDeletionComponents
