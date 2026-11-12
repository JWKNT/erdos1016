import Erdos1016.ExactMaximum.Remaining
import Erdos1016.ExactMaximumSupport.GapInput
import Erdos1016.ExactMaximumSupport.SecondOrder

set_option autoImplicit false

/-!
# Independent checks of both main mathematical endpoints

Each theorem below has no mathematical premise. The graph-count definitions,
both parity formulas, and the positive second-order bounds are checked explicitly.
-/
noncomputable section
namespace Erdos1016.EndpointAudit
open ExactMaximum CycleCount Filter Asymptotics

/-- The exact maximum over all finite simple graphs of the prescribed rank. -/
theorem exact_maximum : ∃ R : ℕ,∀r,R≤r → maxCycles r=horakKim r :=
  exactMaximumStatement_of_gap ExactMaximumSupport.gapStatement

/-- The odd-rank formula, stated without the Horak--Kim abbreviation. -/
theorem odd_exact : ∃Q : ℕ,∀q,Q≤q →
    maxCycles (2*q+1)=2^(2*q)+(4*q+1)*2^(q-1)-3*q := by
  obtain ⟨R,hR⟩ := exact_maximum
  refine ⟨max R 1,?_⟩
  intro q hq
  have hR' : R≤2*q+1 := by omega
  rw [hR _ hR']
  have hh := horakKim_odd q (by omega)
  omega

/-- The even-rank formula, stated without the Horak--Kim abbreviation. -/
theorem even_exact : ∃Q : ℕ,∀q,Q≤q →
    maxCycles (2*q+2)=2^(2*q+1)+(4*q+9)*2^(q-1)-3*q-4 := by
  obtain ⟨R,hR⟩ := exact_maximum
  refine ⟨max R 1,?_⟩
  intro q hq
  have hR' : R≤2*q+2 := by omega
  rw [hR _ hR']
  have hh := horakKim_even q (by omega)
  omega

/-- The usual real half-exponent formulation of the sharp second-order term. -/
theorem second_order :
    (fun r : ℕ => (maxCycles r : ℝ)-(2 : ℝ)^(r-1)) =Θ[atTop]
      (fun r : ℕ => (r : ℝ)*(2 : ℝ)^((r : ℝ)/2)) :=
  ExactMaximumSupport.sharpSecondOrder_rpow_of_exactMaximum exact_maximum

/-- Positive explicit constants also check the sign and scale of the excess. -/
theorem second_order_bounds : ∃R : ℕ,∀r,R≤r →
    (r : ℝ)*(2 : ℝ)^((r : ℝ)/2)/8≤(maxCycles r : ℝ)-(2 : ℝ)^(r-1) ∧
    (maxCycles r : ℝ)-(2 : ℝ)^(r-1)≤2*((r : ℝ)*(2 : ℝ)^((r : ℝ)/2)) :=
  ExactMaximumSupport.sharpSecondOrder_explicit_of_exactMaximum exact_maximum

/-- Every finite simple graph is covered, with the usual Euler rank equation. -/
theorem graph_upper : ∃R : ℕ,∀(n : ℕ)(G : SimpleGraph (Fin n))(r : ℕ),
    r+n=Nat.card G.edgeSet+Nat.card G.ConnectedComponent → R≤r → numCycles G≤horakKim r := by
  obtain ⟨R,hR⟩ := exact_maximum
  refine ⟨R,?_⟩
  intro n G r hr hlarge
  rw [←hR r hlarge]
  exact numCycles_le_maxCycles G r hr

/-- For every sufficiently large rank, an actual finite simple graph attains the formula. -/
theorem graph_attainment : ∃R : ℕ,∀r,R≤r → ∃(n : ℕ)(G : SimpleGraph (Fin n)),
    r+n=Nat.card G.edgeSet+Nat.card G.ConnectedComponent ∧ numCycles G=horakKim r := by
  obtain ⟨R,hR⟩ := exact_maximum
  refine ⟨max R 3,?_⟩
  intro r hr
  obtain ⟨n,G,hG,hC⟩ := maxCycles_mem r (by omega)
  exact ⟨n,G,hG,hC.trans (hR r (by omega))⟩

end Erdos1016.EndpointAudit

#print Erdos1016.CycleCount.cycleCounts
#print Erdos1016.CycleCount.maxCycles
#print Erdos1016.CycleCount.cycleEdgeSets
#print Erdos1016.CycleCount.numCycles
#print axioms Erdos1016.EndpointAudit.exact_maximum
#print axioms Erdos1016.EndpointAudit.odd_exact
#print axioms Erdos1016.EndpointAudit.even_exact
#print axioms Erdos1016.EndpointAudit.second_order
#print axioms Erdos1016.EndpointAudit.second_order_bounds
#print axioms Erdos1016.EndpointAudit.graph_upper
#print axioms Erdos1016.EndpointAudit.graph_attainment
