import Erdos1016.Probability.Cylinders.IncidentTripleEvents

set_option autoImplicit false

/-!
# Audit interface for exceptional selected-triple partners

A triple imposes at most three independent binary constraints. This is the
rank bound currently available from the graph-specific definitions alone; a
uniform bound on the number of other indices whose common rank exceeds one
requires an additional combinatorial lemma about the indexed family.
-/

noncomputable section

namespace Erdos1016.Proof.TripleConstraintRank

open Erdos1016
open Erdos1016.Proof.ActiveTripleBridge

local notation "F₂" => ZMod 2

theorem tripleConstraintSpace_finrank_le_three
    (G : PhysicalGraph) (e : Fin 3 → G.Edge) :
    Module.finrank F₂ (tripleConstraintSpace G e) ≤ 3 := by
  unfold tripleConstraintSpace
  have h := LinearMap.finrank_range_le (tripleObservation G e).dualMap
  have hdom : Module.finrank F₂ (Fin 3 → F₂) = 3 := by
    norm_num [Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype] at h
  simpa [hdom] using h

end Erdos1016.Proof.TripleConstraintRank
