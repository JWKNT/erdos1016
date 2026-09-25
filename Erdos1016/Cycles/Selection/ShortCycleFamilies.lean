import Erdos1016.Cycles.Geometry.Supports

set_option autoImplicit false

/-! Pure short-cycle families and exclusion predicates, independent of connector or packing arguments. -/

noncomputable section
namespace Erdos1016.CycleSupply
open BoundaryDecay
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

end Erdos1016.CycleSupply
