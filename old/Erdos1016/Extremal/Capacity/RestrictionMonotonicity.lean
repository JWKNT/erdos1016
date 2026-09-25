import Erdos1016.Extremal.Capacity.RestrictedMultiplicity
import Erdos1016.Extremal.Capacity.RestrictedCapacityEquiv

set_option autoImplicit false

/-!
# Restriction monotonicity for physical edge subgraphs

Combine the counting argument for restricted edge words with the exact
reindexing equivalence to state the paper's restriction monotonicity directly
for the physical graph on a chosen edge set.
-/

namespace Erdos1016.Proof.CapacityBridge

open Erdos1016

/-- Restricting to an edge subgraph can only increase normalized numerical
linear-forest capacity. -/
theorem normalizedLinearForestCapacity_le_restrictPhysical
    (G : PhysicalGraph) (E : Finset G.Edge) :
    G.normalizedLinearForestCapacity ≤
      (G.restrictPhysical E).normalizedLinearForestCapacity := by
  rw [G.restrictPhysical_normalizedLinearForestCapacity]
  exact normalizedLinearForestCapacity_le_restricted G E

end Erdos1016.Proof.CapacityBridge
