import Erdos1016.Expansion.Connectors
import Erdos1016.Cycles.Selection.ProtectedPacking

set_option autoImplicit false

/-!
# Maximal short-cycle packing and an actual small transversal

The finite maximal family is constructed, not supplied as a maximality
hypothesis. The FEW output hits every original physical short cycle, and a
connected enlargement preserves this exclusion. No subsequent two-core or
nonbacktracking assertion is bundled into the theorem.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
variable (G : PhysicalGraph)

def IsCyclePacking (F : Finset G.CycleWord) : Prop :=
  ∀ C ∈ F, ∀ E ∈ F, C ≠ E → Disjoint (Cycle.vertices C) (Cycle.vertices E)

def shortCycles (U : Finset G.Vertex) (D : ℕ) : Finset G.CycleWord :=
  by
    classical
    exact Finset.univ.filter fun C =>
      Cycle.vertices C ⊆ U ∧ BoundaryDecay.Cycle.length C ≤ D

@[simp] theorem mem_shortCycles (U : Finset G.Vertex) (D : ℕ) (C : G.CycleWord) :
    C ∈ shortCycles G U D ↔
      Cycle.vertices C ⊆ U ∧ BoundaryDecay.Cycle.length C ≤ D := by
  simp [shortCycles]

def cyclePackingVertices (F : Finset G.CycleWord) : Finset G.Vertex :=
  F.biUnion Cycle.vertices

/-- This predicate means exclusion of every literal cycle word with the
stated length. It does not speak only about a chosen generating family. -/
def NoShortCycles (U : Finset G.Vertex) (D : ℕ) : Prop :=
  ∀ C : G.CycleWord, Cycle.vertices C ⊆ U → D < BoundaryDecay.Cycle.length C

theorem noShortCycles_mono {U V : Finset G.Vertex} {D : ℕ}
    (h : NoShortCycles G U D) (hVU : V ⊆ U) : NoShortCycles G V D :=
  by
    intro C hC
    change ∀ C, Cycle.vertices C ⊆ U → D < BoundaryDecay.Cycle.length C at h
    exact h C (hC.trans hVU)

private theorem not_disjoint_has_vertex {α : Type*} [DecidableEq α]
    {A B : Finset α} (h : ¬ Disjoint A B) : ∃ v ∈ A, v ∈ B := by
  by_contra hn
  apply h
  apply Finset.disjoint_left.2
  intro v hvA hvB
  exact hn ⟨v, hvA, hvB⟩

/-- Finite maximal packing, with its full domination/hitting certificate. -/
theorem exists_maximal_cycle_packing (F : Finset G.CycleWord) :
    ∃ I ⊆ F, IsCyclePacking G I ∧
      ∀ C ∈ F, ∃ E ∈ I, ∃ v ∈ Cycle.vertices C, v ∈ Cycle.vertices E := by
  classical
  let R : G.CycleWord → G.CycleWord → Prop := fun C E =>
    ¬ Disjoint (Cycle.vertices C) (Cycle.vertices E)
  have hR : Symmetric R := by
    intro C E h hdis
    exact h hdis.symm
  obtain ⟨I, hIF, hI, hdom⟩ := exists_independent_dominating R hR F
  refine ⟨I, hIF, ?_, ?_⟩
  · intro C hC E hE hne
    by_contra hdis
    exact hI C hC E hE hne hdis
  · intro C hC
    obtain ⟨E, hE, hCE⟩ := Finset.mem_biUnion.1 (hdom hC)
    have hCE' : C = E ∨ R E C := by
      simp only [BoundaryDecay.closedNeighbors, Finset.mem_filter] at hCE
      exact hCE.2
    rcases hCE' with hCE | hCE
    · subst C
      obtain ⟨v, hv⟩ := Cycle.vertices_nonempty E
      exact ⟨E, hE, v, hv, hv⟩
    · obtain ⟨v, hvE, hvC⟩ := not_disjoint_has_vertex hCE
      exact ⟨E, hE, v, hvC, hvE⟩

/-- The maximal packing supplies the entire short-cycle transversal. -/
theorem short_cycle_transversal (U : Finset G.Vertex) (D : ℕ) :
    ∃ I ⊆ shortCycles G U D,
      IsCyclePacking G I ∧
      cyclePackingVertices G I ⊆ U ∧
      (cyclePackingVertices G I).card ≤ D * I.card ∧
      NoShortCycles G (U \ cyclePackingVertices G I) D := by
  obtain ⟨I, hIF, hI, hdom⟩ := exists_maximal_cycle_packing G (shortCycles G U D)
  have hsub : cyclePackingVertices G I ⊆ U := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hv
    exact ((mem_shortCycles G U D C).1 (hIF hC)).1 hvC
  refine ⟨I, hIF, hI, hsub, ?_, ?_⟩
  · calc
      (cyclePackingVertices G I).card ≤ ∑ C ∈ I, (Cycle.vertices C).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ I, D := by
        apply Finset.sum_le_sum
        intro C hC
        rw [← BoundaryDecay.Cycle.length_eq_vertices_card]
        exact ((mem_shortCycles G U D C).1 (hIF hC)).2
      _ = D * I.card := by simp [Nat.mul_comm]
  · intro C hC
    by_contra hlen
    have hsmall : C ∈ shortCycles G U D :=
      (mem_shortCycles G U D C).2 ⟨hC.trans Finset.sdiff_subset, le_of_not_gt hlen⟩
    obtain ⟨E, hE, v, hvC, hvE⟩ := hdom C hsmall
    have hvX : v ∈ cyclePackingVertices G I := Finset.mem_biUnion.2 ⟨E, hE, hvE⟩
    exact (Finset.mem_sdiff.1 (hC hvC)).2 hvX

/-- Exhaustive finite MANY/FEW split, including the exact integer bound
for the transversal in the FEW branch. -/
theorem short_cycle_dichotomy (U : Finset G.Vertex) (D K : ℕ) (hK : 0 < K) :
    (∃ F ⊆ shortCycles G U D, IsCyclePacking G F ∧ K ≤ F.card) ∨
    (∃ X ⊆ U, X.card ≤ D * (K - 1) ∧ NoShortCycles G (U \ X) D) := by
  obtain ⟨I, hIF, hI, hXU, hXsize, hshort⟩ := short_cycle_transversal G U D
  by_cases hmany : K ≤ I.card
  · exact Or.inl ⟨I, hIF, hI, hmany⟩
  · right
    have hcard : I.card ≤ K - 1 := by omega
    exact ⟨cyclePackingVertices G I, hXU,
      hXsize.trans (Nat.mul_le_mul_left D hcard), hshort⟩

/-- The FEW transversal can be connected to the existing protector inside
H itself. Every excluded cycle statement concerns original vertex sets. -/
theorem short_cycle_dichotomy_connected
    (h : ℝ) (hh : 0 < h) (hExp : HasExpansion G Finset.univ h)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (W₀ : Finset G.Vertex) (hW₀ : ConnectedRegion G W₀)
    (D K : ℕ) (hK : 0 < K) :
    (∃ F ⊆ shortCycles G W₀ᶜ D, IsCyclePacking G F ∧ K ≤ F.card) ∨
    (∃ W, ConnectedRegion G W ∧ W₀ ⊆ W ∧
      W.card ≤ W₀.card + D * (K - 1) * (2 * connectorRadius G h + 1) ∧
      NoShortCycles G Wᶜ D) := by
  rcases short_cycle_dichotomy G W₀ᶜ D K hK with hmany | ⟨X, hX, hsize, hshort⟩
  · exact Or.inl hmany
  · right
    obtain ⟨W, hW, hW₀W, hXW, hWsize⟩ :=
      connected_enlargement_logarithmic G h hh hExp hdeg W₀ hW₀ X
    have hsize' := Nat.mul_le_mul_right (2 * connectorRadius G h + 1) hsize
    have hsub : Wᶜ ⊆ W₀ᶜ \ X := by
      intro v hv
      refine Finset.mem_sdiff.2 ⟨Finset.mem_compl.2 ?_, ?_⟩
      · intro hv₀
        exact (Finset.mem_compl.1 hv) (hW₀W hv₀)
      · intro hvX
        exact (Finset.mem_compl.1 hv) (hXW hvX)
    exact ⟨W, hW, hW₀W, by omega, noShortCycles_mono G hshort hsub⟩



end Erdos1016.CycleSupply
