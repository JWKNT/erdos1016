import Erdos1016.ExactMaximum.PoleInputs
import Erdos1016.ExactMaximumSupport.NetworkPoleLayers

set_option autoImplicit false

/-!
# The path-rich pole layer input

This wrapper discharges the exact layer statement used by the pole-counting proof.
The network, distances, and vertex cardinalities are unchanged.
-/

noncomputable section

namespace Erdos1016.ExactMaximumSupport

/-- The uniform two-port layer bound in the exact-maximum interface. -/
theorem poleLayerBoundStatement : ExactMaximum.PoleLayerBoundStatement := by
  classical
  obtain ⟨B, hB⟩ := NetworkPoleLayers.exists_two_port_layer_bound_501
  refine ⟨9 * B, ?_⟩
  intro V E _ _ N s t hN hdeg hcubic hst hp j
  have h := hB N s t hN hdeg hcubic hst hp (j : ℤ)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Int.natCast_inj] using h

end Erdos1016.ExactMaximumSupport
