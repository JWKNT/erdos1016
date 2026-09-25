import Erdos1016.Cycles.Filtering.ReturnTheta

set_option autoImplicit false

namespace Erdos1016.Proof.PhysicalThetaPairRelabel

open Erdos1016.Proof.ExternalReturnTheta
open SimpleGraph

variable {V : Type*} {H : SimpleGraph V} [DecidableEq V]

/-- The two branch cycle selected from the original theta. -/
def pairCycle {u v : V} (t : ThetaPaths H u v) : ThetaPair → H.Walk u u
  | .leftRight => leftRightCycle H t
  | .leftExternal => leftExternalCycle H t
  | .externalRight => externalRightCycle H t

/-- The original branch omitted by a selected pair-cycle. -/
def omittedBranch {u v : V} (t : ThetaPaths H u v) : ThetaPair → H.Walk u v
  | .leftRight => t.external
  | .leftExternal => t.right
  | .externalRight => t.left

/-- Reindex the original theta so that the selected pair occupies the two
cycle positions and the omitted branch is the external branch. No geometric
correspondence is assumed: every branch is one of the original walks. -/
def thetaAtPair {u v : V} (t : ThetaPaths H u v) : ThetaPair → ThetaPaths H u v
  | .leftRight => t
  | .leftExternal => {
      left := t.left
      right := t.external
      external := t.right
      left_path := t.left_path
      right_path := t.external_path
      external_path := t.right_path
      left_right_vertices := t.left_external_vertices
      left_external_vertices := t.left_right_vertices
      right_external_vertices := fun x hx hy => t.right_external_vertices x hy hx
      left_right_edges := t.left_external_edges
      left_external_edges := t.left_right_edges
      right_external_edges := fun e he hne => by
        exact t.right_external_edges e hne he
    }
  | .externalRight => {
      left := t.external
      right := t.right
      external := t.left
      left_path := t.external_path
      right_path := t.right_path
      external_path := t.left_path
      left_right_vertices := fun x hx hy => t.right_external_vertices x hy hx
      left_external_vertices := fun x hx hy => t.left_external_vertices x hy hx
      right_external_vertices := fun x hx hy => t.left_right_vertices x hy hx
      left_right_edges := fun e he hne => t.right_external_edges e hne he
      left_external_edges := fun e he hne => t.left_external_edges e hne he
      right_external_edges := fun e he hne => by
        exact t.left_right_edges e hne he
    }

theorem thetaAtPair_base_eq {u v : V} (t : ThetaPaths H u v) (p : ThetaPair) :
    leftRightCycle H (thetaAtPair t p) = pairCycle t p := by
  cases p <;> rfl

theorem thetaAtPair_external_eq {u v : V} (t : ThetaPaths H u v) (p : ThetaPair) :
    (thetaAtPair t p).external = omittedBranch t p := by
  cases p <;> rfl



end Erdos1016.Proof.PhysicalThetaPairRelabel
