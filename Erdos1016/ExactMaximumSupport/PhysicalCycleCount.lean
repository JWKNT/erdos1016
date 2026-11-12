import Erdos1016.CycleCount.Statement
import Erdos1016.Cycles.Geometry.CycleWalkExistence
import Erdos1016.ExactMaximumSupport.CubicReduction.PhysicalCycles
import Erdos1016.ExactMaximum.NetMinimal

set_option autoImplicit false

/-!
# Exact cycle counts in the physical and simple graph models

Every physical cycle word has an ordinary cycle-walk representative.
Its unordered edge set determines the binary word. Thus both models count
each cycle once, which supplies the realization step for lower bounds.
-/

noncomputable section
namespace Erdos1016.CycleCount

open Nonbacktracking

/-- Physical cycle words inject into ordinary cycle edge sets. -/
theorem cycleCount_le_numCycles_toSimpleGraph (P : PhysicalGraph) :
    cycleCount P ≤ numCycles P.toSimpleGraph := by
  classical
  have hex (C : P.CycleWord) : ∃ s : cycleEdgeSets P.toSimpleGraph,
      ∀ e : P.Edge, C.1 e ≠ 0 ↔ physicalPair P e ∈ s.1 := by
    obtain ⟨u, p, hp, hC⟩ := exists_cycle_walk_of_cycleWord P C
    refine ⟨⟨{a | a ∈ p.edges}, u, p, hp, rfl⟩, ?_⟩
    intro e
    rw [← hC]
    exact walkWord_nonzero_iff P p e
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro C D hCD
    apply Subtype.ext
    apply BoundaryTrace.Network.word_eq_of_support
    · intro e he
      exact (hf D e).mpr (hCD ▸ (hf C e).mp he)
    · intro e he
      exact (hf C e).mpr (hCD.symm ▸ (hf D e).mp he)
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold cycleCount numCycles
  rw [← Nat.card_eq_fintype_card, ← Set.Nat.card_coe_set_eq]
  exact hcard

/-- The ordinary cycle-edge-set count equals the physical cycle-word count. -/
theorem numCycles_toSimpleGraph_eq (P : PhysicalGraph) :
    numCycles P.toSimpleGraph = Fintype.card P.CycleWord :=
  Nat.le_antisymm (numCycles_toSimpleGraph_le P) (cycleCount_le_numCycles_toSimpleGraph P)

/-- A simple physical graph and its labelled multigraph realization have
exactly the same cycle count. -/
theorem numCycles_toSimpleGraph_eq_asMultigraph (P : PhysicalGraph) :
    numCycles P.toSimpleGraph = (ShortProof.CycleCore.asMultigraph P).numCycles := by
  rw [numCycles_toSimpleGraph_eq, ExactMaximumSupport.CubicReduction.asMultigraph_numCycles]

end Erdos1016.CycleCount
