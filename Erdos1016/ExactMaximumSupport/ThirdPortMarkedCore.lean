import Erdos1016.ExactMaximumSupport.ThirdPortReduction
import Erdos1016.ExactMaximum.PoleBridges

set_option autoImplicit false

/-!
# The connected full component and its marked label

Remove only isolated vertices after suppressing the unused port. The retained
edge has a canonical physical label in the connected core, whose two subtype
projections are the original label. The original thread is part of the output.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance markedCoreDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- The positive-degree induced network keeps every physical edge. -/
abbrev positive := N.induce fun z => 0 < N.deg (fun _ => 1) z

/-- The canonical image of an original label in the positive-degree network. -/
def positiveEdge (e : E) : {g : E // N.inside (fun z => 0 < N.deg (fun _ => 1) z) g} :=
  ⟨e,N.deg_src_pos (show (fun _ : E => (1 : Bit)) e ≠ 0 from one_ne_zero),
    N.deg_dst_pos (show (fun _ : E => (1 : Bit)) e ≠ 0 from one_ne_zero)⟩

omit [Fintype V] in
@[simp] theorem positiveEdge_val (e : E) : (positiveEdge N e).1 = e := rfl

/-- Normalization to a connected full two-pole preserves exact counts and rank. -/
theorem connected_full_two_pole (s t : V) (hN : N.IsWeakTwoPole s t)
    (hbl : N.IsBridgeless) (hfull : N.IsFullPair s t) :
    ∃ (hs : 0 < N.deg (fun _ => 1) s) (ht : 0 < N.deg (fun _ => 1) t),
      (positive N).IsBridgelessTwoPole ⟨s,hs⟩ ⟨t,ht⟩ ∧
      (positive N).IsFullPair ⟨s,hs⟩ ⟨t,ht⟩ ∧
      networkRank (positive N) = networkRank N ∧
      (positive N).numPaths ⟨s,hs⟩ ⟨t,ht⟩ = N.numPaths s t ∧
      (positive N).numCycles = N.numCycles := by
  obtain ⟨hs,ht,hpole,hc,hr,hp⟩ := N.isBridgelessTwoPole_induce hN hbl
  refine ⟨hs,ht,hpole,?_,hr,hp,hc⟩
  change (positive N).numPaths ⟨s,hs⟩ ⟨t,ht⟩ = 2 ^ networkRank (positive N)
  rw [hp,hr]
  exact hfull

/-- The full bridgeless three-pole supplies a connected full two-pole while
retaining its original thread and the exact marked physical edge. -/
theorem exists_connected_marked_suppression (s t v : V) (hN : N.IsWeakPole)
    (hbl : N.IsBridgeless) (hs : N.IsPort s) (ht : N.IsPort t) (hv : N.IsPort v)
    (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (honly : ∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v)
    (hfull : N.IsFullPair s t) :
    ∃ (e f : E) (u w : V) (T : N.Thread e f u v w),
      let M := N.suppress e f u w T.huw
      ∃ (hs' : 0 < M.deg (fun _ => 1) s) (ht' : 0 < M.deg (fun _ => 1) t),
        (positive M).IsBridgelessTwoPole ⟨s,hs'⟩ ⟨t,ht'⟩ ∧
        (positive M).IsFullPair ⟨s,hs'⟩ ⟨t,ht'⟩ ∧
        networkRank (positive M) = networkRank N ∧
        (positive M).numPaths ⟨s,hs'⟩ ⟨t,ht'⟩ = N.numPaths s t ∧
        (positive M).numCycles = N.numCycles ∧
        (positiveEdge M ⟨e,T.hef⟩).1.1 = e := by
  obtain ⟨e,f,u,w,T,hpole,hfull',hr,hp,hc,_,_⟩ :=
    ThirdPortReduction.exists_full_two_pole_thread N s t v hN hs ht hv hst hsv htv honly hfull
  obtain ⟨hs',ht',hcore,hcorefull,hcorerank,hcorepaths,hcorecycles⟩ :=
    connected_full_two_pole (N.suppress e f u w T.huw) s t hpole
      ((ThirdPortReduction.bridgeless_suppress_iff N T).2 hbl) hfull'
  exact ⟨e,f,u,w,T,hs',ht',hcore,hcorefull,hcorerank.trans hr,
    hcorepaths.trans hp,hcorecycles.trans hc,rfl⟩

end Erdos1016.ExactMaximumSupport.ThirdPortMarkedCore
