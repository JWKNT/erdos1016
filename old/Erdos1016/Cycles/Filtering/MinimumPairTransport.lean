import Erdos1016.Cycles.Filtering.ThetaCandidates
import Erdos1016.Cycles.Filtering.ThetaPairRelabel

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.MinimumPairArcTransport

open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.PhysicalThetaPairRelabel

variable (G : PhysicalGraph)

/-- The original left-right source cycle becomes one of the three indexed
constituents after the minimum pair is relabelled as the base pair. -/
def sourceLeftRightTag (p : ThetaPair) : Fin 3 :=
  match p with
  | .leftRight => 0
  | .leftExternal => 1
  | .externalRight => 2

/-- Before comparing to a separately chosen candidate decomposition, the
minimum-pair relabelling itself preserves the source arcs exactly. -/
theorem sourceLeftRight_arcPairCorrespondence
    {u v : G.Vertex} (t : ThetaPaths G.toSimpleGraph u v) (p : ThetaPair) :
    ArcPairCorrespondence G
      (thetaPairPaths G t (0 : Fin 3)).1
      (thetaPairPaths G t (0 : Fin 3)).2
      (thetaPairPaths G (thetaAtPair t p)
        (sourceLeftRightTag p)).1
      (thetaPairPaths G (thetaAtPair t p)
        (sourceLeftRightTag p)).2 := by
  cases p <;> simp [ArcPairCorrespondence, thetaPairPaths, thetaAtPair,
    sourceLeftRightTag]



end Erdos1016.Proof.MinimumPairArcTransport
end
