import Erdos1016.Cycles.Counting.CycleRootChoice
import Erdos1016.Nonbacktracking.Walks.SplitRunCoordinates

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.RootedCyclePrefixes

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.CollisionSliceInstantiation
open Erdos1016.Proof.CycleRootChoice

variable (G : PhysicalGraph)

private theorem run_one_head_eq_tail {d e : Dart G} (r : Run G 1 d e) :
    head G d = tail G e := by
  rcases r with ⟨u, hu, rest⟩
  have he : u = e := rest.2
  subst e
  exact hu.2.1

private theorem runDarts_one_eq_pair {d e : Dart G} (r : Run G 1 d e) :
    runDarts G 1 r = [d, e] := by
  rcases r with ⟨u, hu, rest⟩
  have he : u = e := rest.2
  subst e
  simp [runDarts]

/-- Split the closed run of a rooted simple cycle at its repeated seam dart.
The prefix is a fixed-endpoint run from the chosen root vertex back to itself. -/
def rootedCycleEndpointPrefix {ell : ℕ} {v : G.Vertex}
    (c : RootedSimpleCycle G ell)
    (x : RootChoices c.1.2) (hx : x.1 = v) (orientation : Bool) :
    EndpointRuns G (ell - 1) v v := by
  let rr := rootedCycleRun c.1.2 c.2.1 x orientation
  let r : Run G ell rr.1 rr.1 :=
    Eq.ndrec (motive := fun k => Run G k rr.1 rr.1) rr.2.2 c.2.2
  let z := splitRun G (Nat.sub_le ell 1) r
  have hell : 1 ≤ ell := by
    have h := c.2.1.three_le_length
    omega
  have hsub : ell - (ell - 1) = 1 := by omega
  have htail : tail G rr.1 = v := by
    have heq : rr.1 = rootedCycleStartDart c.1.2 c.2.1 x orientation := by
      rfl
    calc
      tail G rr.1 = tail G (rootedCycleStartDart c.1.2 c.2.1 x orientation) :=
        congrArg (tail G) heq
      _ = x.1 := rootedCycleStartDart_tail c.1.2 c.2.1 x orientation
      _ = v := hx
  have hhead : head G z.1 = v := by
    have hlast : head G z.1 = tail G rr.1 := by
      apply run_one_head_eq_tail G
      simpa [hsub] using z.2.2
    exact hlast.trans htail
  refine ⟨⟨rr.1, z.1, z.2.1⟩, ?_⟩
  change (tail G rr.1, head G z.1) = (v, v)
  exact Prod.ext htail hhead

/-- The endpoint prefix retains exactly the dart serialization of the
rooted simple cycle, with the duplicated seam dart removed. -/
theorem rootedCycleEndpointPrefix_darts {ell : ℕ} {v : G.Vertex}
    (c : RootedSimpleCycle G ell)
    (x : RootChoices c.1.2) (hx : x.1 = v) (orientation : Bool) :
    runDarts G (ell - 1)
        (rootedCycleEndpointPrefix G c x hx orientation).1.2.2 =
      walkDarts G (rootedOrientedWalk c.1.2 x orientation) := by
  let rr := rootedCycleRun c.1.2 c.2.1 x orientation
  let r : Run G ell rr.1 rr.1 :=
    Eq.ndrec (motive := fun k => Run G k rr.1 rr.1) rr.2.2 c.2.2
  let z0 := splitRun G (Nat.sub_le ell 1) r
  have hell : 1 ≤ ell := by
    have h := c.2.1.three_le_length
    omega
  have hsub : ell - (ell - 1) = 1 := by omega
  let suffix : Run G 1 z0.1 rr.1 :=
    Eq.ndrec (motive := fun k => Run G k z0.1 rr.1) z0.2.2 hsub
  let z : (f : Dart G) × Run G (ell - 1) rr.1 f × Run G 1 f rr.1 :=
    ⟨z0.1, z0.2.1, suffix⟩
  have hsplit := runDarts_splitRun G (Nat.sub_le ell 1) r
  have htail : (runDarts G (ell - (ell - 1)) z0.2.2).tail = [rr.1] := by
    calc
      _ = (runDarts G 1 suffix).tail := by
        have hcast : runDarts G 1 suffix =
            runDarts G (ell - (ell - 1)) z0.2.2 := by
          simpa [suffix] using (runDarts_cast hsub z0.2.2)
        rw [← hcast]
      _ = [rr.1] := by
        rw [runDarts_one_eq_pair G suffix]
        simp
  have hclosed : runDarts G ell r =
      walkDarts G (rootedOrientedWalk c.1.2 x orientation) ++ [rr.1] := by
    have h0 := rootedCycleRun_darts c.1.2 c.2.1 x orientation
    have hd : rr.1 = rootedCycleStartDart c.1.2 c.2.1 x orientation := rfl
    calc
      runDarts G ell r =
          runDarts G c.1.2.length (rootedCycleRun c.1.2 c.2.1 x orientation).2.2 := by
            simpa [rr, r] using
              (runDarts_cast c.2.2
                (rootedCycleRun c.1.2 c.2.1 x orientation).2.2)
      _ = walkDarts G (rootedOrientedWalk c.1.2 x orientation) ++ [rr.1] := by
        rw [h0, hd]
  have hprefix : runDarts G (ell - 1) z0.2.1 =
      walkDarts G (rootedOrientedWalk c.1.2 x orientation) := by
    have hsplit' : runDarts G ell r =
        runDarts G (ell - 1) z0.2.1 ++ [rr.1] := by
      simpa [z0, htail] using hsplit
    have happend := hsplit'.symm.trans hclosed
    exact List.append_cancel_right happend
  change runDarts G (ell - 1) z0.2.1 = _
  exact hprefix

end Erdos1016.Proof.RootedCyclePrefixes

end
