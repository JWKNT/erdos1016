import Erdos1016.CycleSpace.LoopCoordinate
import Erdos1016.Cleanup.Paths.ClosedCorridorCycles
import Erdos1016.Cleanup.Paths.CorridorTailNodup
import Erdos1016.Cleanup.Protection.CorridorWitnessAvoidance
import Erdos1016.Cleanup.Compression.EndpointIncidenceBijection
import Erdos1016.Cleanup.Transport.CompressedComponentLift
import Erdos1016.Cleanup.Transport.ReducedForestEventTransfer
import Erdos1016.Cleanup.Root.OutsideComponentRoot
import Erdos1016.Cleanup.Protection.PostProtectionSimplicity
import Erdos1016.Probability.Regions.TripleCutPackingBound

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ParallelProtectionComplement

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ComponentExtraction
open Erdos1016.Proof.PostProtectionSimplicity


/-- The finite index set of ordered, eligible parallel-edge pairs used by the
post-protection construction. -/
def eligibleParallelPairIndices (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    Finset (Γ.Edge × Γ.Edge) := by
  classical
  exact Finset.univ.filter fun p => parallelOutside Γ P p.1 p.2



def eligibleUnorderedParallelPairIndices (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :
    Finset (Γ.Edge × Γ.Edge) :=
  (eligibleParallelPairIndices Γ P).filter fun p =>
    (Fintype.equivFin Γ.Edge p.1).val < (Fintype.equivFin Γ.Edge p.2).val






























end Erdos1016.Proof.ParallelProtectionComplement

end
