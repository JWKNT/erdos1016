import Erdos1016.CycleSpace.Graphical.EvenLinkAssignments
import Erdos1016.CycleSpace.Graphical.LinkPairWitnesses
import Erdos1016.CycleSpace.Graphical.TotalLinkParity

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalLinkPairSpan

open Erdos1016
open Erdos1016.Proof.GraphicalLinkMap

open Erdos1016.Proof.GraphicalAbstractLinks

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p





/-- Actual cycle words realize every pair assignment, viewed in the linear
map range. -/
theorem pairAssignmentSpan_le_linkMap_range (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) :
    pairAssignmentSpan (ι := LinkIndex G u v) ≤
      LinearMap.range (linkMap G u v) := by
  apply Submodule.span_le.2
  rintro z ⟨i, j, hij, rfl⟩
  obtain ⟨x, hx⟩ := GraphicalLinkPairWitnesses.pairLinkMap_cycleWitness
    G u v hne i j hij
  exact ⟨x, hx⟩

/-- Whenever there is at least one link, the actual graph link map reaches all
even-parity assignments. This is the constructive half of the exact
surjectivity theorem; the reverse inclusion is the all-cycle-even lemma. -/
theorem evenLinkAssignments_le_linkMap_range (G : PhysicalGraph) (u v : G.Vertex)
    (hne : u ≠ v) [Nonempty (LinkIndex G u v)] :
    EvenLinkAssignments (ι := LinkIndex G u v) ≤
      LinearMap.range (linkMap G u v) := by
  rw [← pairAssignmentSpan_eq_even (ι := LinkIndex G u v)]
  exact pairAssignmentSpan_le_linkMap_range G u v hne









end Erdos1016.Proof.GraphicalLinkPairSpan
