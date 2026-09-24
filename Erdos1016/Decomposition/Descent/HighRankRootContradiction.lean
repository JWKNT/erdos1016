import Erdos1016.Decomposition.Descent.CleanupRootDescent
import Erdos1016.Decomposition.Descent.ExponentialRootComparison

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.HighRankRootContradiction

open Erdos1016 SafeCore CleanupSpecification PortExpansion
open FiniteForestDescent

/-- The packing coefficient is fixed by the two-exterior stopping scale.
It is uniform in the cleanup input and its rank scale. -/
def packingCoefficient (T₀ : ℕ → ℕ) : ℕ :=
  ManyRegionsLogCutoff.fixedCutCoefficient (fixedCutCap T₀)



end Erdos1016.Proof.HighRankRootContradiction

end
