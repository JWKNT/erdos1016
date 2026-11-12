import Erdos1016.ExactMaximum.PoleCycleCount
import Erdos1016.ExactMaximum.PoleBridges
import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleCycleBound
import Erdos1016.ExactMaximum.SmallCutCase
import Erdos1016.ExactMaximumSupport.PoleThinLayers
import Erdos1016.ExactMaximumSupport.CycleTwoStrands
import Erdos1016.ExactMaximumSupport.LayerMatchingInput

set_option autoImplicit false

/-!
# The complete few-cycles theorem and the small-cut case

The proved thin-layer and local matching statements discharge the global count.
Bridge decomposition and port suppression then give the theorem for all poles.
The four-cut and bounded-girth cases remain separate obligations.
-/
namespace Erdos1016.ExactMaximumSupport.PoleFewCycles

/-- The global count for actual bridgeless two-poles has no unproved local input. -/
theorem bridgelessFewCyclesStatement : ExactMaximum.BridgelessFewCyclesStatement :=
  ExactMaximum.bridgelessFewCyclesStatement_of_layers thinLayersStatement
    CycleTwoStrands.twoStrandsStatement layerMatchingStatement

/-- Bridge decomposition gives the squared bound for all weak two-poles. -/
theorem twoPoleFewCyclesStatement : ExactMaximum.TwoPoleFewCyclesStatement :=
  ExactMaximum.twoPoleFewCyclesStatement_of_bridgeless bridgelessFewCyclesStatement

/-- Theorem 5.4 at margin `1/1000`, including all port and bridge reductions. -/
theorem fewCyclesStatement : ExactMaximum.FewCyclesStatement :=
  ExactMaximum.fewCyclesStatement_of_twoPole twoPoleFewCyclesStatement

/-- Proposition 6.3, with no remaining mathematical hypotheses. -/
theorem threeCutStatement : ExactMaximum.ThreeCutStatement :=
  ExactMaximum.threeCutStatement_of_poles fewCyclesStatement
    ExactMaximum.poleCycleBoundStatement

end Erdos1016.ExactMaximumSupport.PoleFewCycles
