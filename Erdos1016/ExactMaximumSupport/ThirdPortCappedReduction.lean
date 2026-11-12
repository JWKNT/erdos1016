import Erdos1016.ExactMaximumSupport.MarkedPathCount
import Erdos1016.ExactMaximumSupport.ThirdPortRestoredCore
import Erdos1016.ExactMaximumSupport.FullPairCappedLadder
import Erdos1016.ExactMaximumSupport.ThirdPortBridgeInduction

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The third-port theorem from concrete capped-ladder counts

The marked physical edge survives suppression, removal of isolates, and relabeling.
Only its concrete capped-ladder continuation count remains as a premise.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
local instance cappedReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private abbrev defaultSuppressedFintype {E : Type*} [Fintype E] (f : E) :
    Fintype {g : E // g≠f} := inferInstance

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Integrality supplies the seven-eighths alternative through rank three. -/
theorem small_rank (s t : V) (hr : networkRank N ≤ 3) :
    N.IsFullPair s t ∨ 8*N.numPaths s t ≤ 7*2^networkRank N := by
  have hupper := N.numPaths_le_two_pow s t
  have hpow : 2^networkRank N ≤ 8 := by
    calc _ ≤ 2^3 := Nat.pow_le_pow_right (by decide) hr
         _ = 8 := by norm_num
  by_cases hfull : N.IsFullPair s t
  · exact Or.inl hfull
  · right
    change N.numPaths s t ≠ 2^networkRank N at hfull
    omega

local instance (priority := 2000) cappedReductionHighDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem numPaths_fintype {A B : Type*} (M : Network A B)
    (i j : Fintype B) (s t : A) :
    @Network.numPaths A B i M s t = @Network.numPaths A B j M s t := by
  rw [Subsingleton.elim i j]

variable {e f : E} {u v w : V} (T : N.Thread e f u v w)
variable {V' E' : Type*} [Fintype V'] [Fintype E'] {K : Network V' E'}
variable (R : NetworkIso (ThirdPortRestoredCore.core N T) K)

omit [Fintype V] in
/-- The normalized marked label still joins the original thread endpoints. -/
theorem marked_joins
    (hu : 0 < (ThirdPortRestoredCore.suppressed N T).deg (fun _ => 1) u)
    (hw : 0 < (ThirdPortRestoredCore.suppressed N T).deg (fun _ => 1) w) :
    (ThirdPortRestoredCore.core N T).Joins (ThirdPortRestoredCore.marked N T)
      ⟨u,hu⟩ ⟨w,hw⟩ := by
  have hj := N.suppress_joins_of_eq T.huw ⟨e,T.hef⟩ rfl
  rcases hj with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact Or.inl ⟨Subtype.ext hs,Subtype.ext ht⟩
  · exact Or.inr ⟨Subtype.ext hs,Subtype.ext ht⟩

/-- The original third-port count is the orientation-free count in its concrete core. -/
theorem numPaths_eq_count (t : V)
    (hu : 0 < (ThirdPortRestoredCore.suppressed N T).deg (fun _ => 1) u)
    (hw : 0 < (ThirdPortRestoredCore.suppressed N T).deg (fun _ => 1) w)
    (ht : 0 < (ThirdPortRestoredCore.suppressed N T).deg (fun _ => 1) t) :
    N.numPaths v t = MarkedPathCount.count K (R.edges (ThirdPortRestoredCore.marked N T))
      (R.vertices ⟨t,ht⟩) := by
  rw [MarkedPathCount.count_of_joins K (R.map_joins (marked_joins N T hu hw))]
  rw [ThirdPortRestoredCore.numPaths_restored_in_model N T R t hu hw ht]
  simp only [MarkedPathCount.branch,R.vertices.injective.eq_iff,Subtype.mk.injEq]
  apply congrArg₂ (fun a b : ℕ => a+b)
  · split_ifs
    · rfl
    · exact numPaths_fintype _ _ _ _ _
  · split_ifs
    · rfl
    · exact numPaths_fintype _ _ _ _ _

attribute [-instance] cappedReductionHighDecidable

/-- The sole remaining count ranges over actual labels of the concrete capped model. -/
def CappedMarkedCountStatement : Prop :=
  ∀ (k : ℕ) (T : Fin (k+1) → Kind) (e : CappedEdge T),
    MarkedPathCount.count (capped T) e (Sum.inr true)=2^(weight T+1) ∨
      8*MarkedPathCount.count (capped T) e (Sum.inr true)≤7*2^(weight T+1)

/-- All original graph reductions leave only the concrete capped marked-edge count. -/
theorem bridgelessThirdPortStatement_of_capped (h : CappedMarkedCountStatement) :
    ThirdPortBridgeInduction.BridgelessThirdPortStatement := by
  intro V E _ _ N hN hbl s t v hs ht hv hst hsv htv honly hfull
  by_cases hr : networkRank N ≤ 3
  · exact small_rank N v t hr
  obtain ⟨e,f,u,w,T,hdata⟩ :=
    ThirdPortMarkedCore.exists_connected_marked_suppression
      N s t v hN hbl hs ht hv hst hsv htv honly hfull
  letI : Fintype {g : E // g≠f} :=
    @Subtype.fintype E (fun g => g≠f) (fun g => Classical.propDecidable (g≠f)) inferInstance
  have hinst : (@Subtype.fintype E (fun g => g≠f)
      (fun g => @instDecidableNot (g=f) (Classical.propDecidable (g=f))) inferInstance) =
      (inferInstance : Fintype {g : E // g≠f}) := Subsingleton.elim _ _
  dsimp only [ThirdPortMarkedCore.positive,ThirdPortMarkedCore.markedCoreDecidable] at hdata
  rw [hinst] at hdata
  obtain ⟨hs',ht',hcore,hcorefull,hcorerank,_,_,_⟩ := hdata
  let M := ThirdPortRestoredCore.suppressed N T
  have hu : 0 < M.deg (fun _ => 1) u := by
    have hh := M.deg_src_pos (x := fun _ => 1) (e := ⟨e,T.hef⟩) one_ne_zero
    rw [N.suppress_src_of_eq T.huw ⟨e,T.hef⟩ rfl] at hh
    exact hh
  have hw : 0 < M.deg (fun _ => 1) w := by
    have hh := M.deg_dst_pos (x := fun _ => 1) (e := ⟨e,T.hef⟩) one_ne_zero
    rw [N.suppress_dst_of_eq T.huw ⟨e,T.hef⟩ rfl] at hh
    exact hh
  have hcore' : (ThirdPortRestoredCore.core N T).IsBridgelessTwoPole ⟨s,hs'⟩ ⟨t,ht'⟩ := by
    exact hcore
  have hcorefull' : (ThirdPortRestoredCore.core N T).IsFullPair ⟨s,hs'⟩ ⟨t,ht'⟩ := by
    exact hcorefull
  have hcorerank' : networkRank (ThirdPortRestoredCore.core N T)=networkRank N := by
    exact hcorerank
  obtain ⟨k,A,I,_,hit,hweight⟩ := FullPairCappedLadder.exists_capped_ladder
    (ThirdPortRestoredCore.core N T) hcore' hcorefull' (by omega)
  have htimage : I.symm.vertices ⟨t,ht'⟩=Sum.inr true := by
    change I.vertices.symm ⟨t,ht'⟩=Sum.inr true
    rw [←hit,I.vertices.symm_apply_apply]
  have hcount := numPaths_eq_count N T I.symm t hu hw ht'
  rw [htimage] at hcount
  have hbound := h k A (I.symm.edges (ThirdPortRestoredCore.marked N T))
  rw [hweight,hcorerank',←hcount] at hbound
  exact hbound

/-- The full gap theorem follows from the remaining explicit capped-model count. -/
theorem gapStatement_of_capped (h : CappedMarkedCountStatement) : ExactMaximum.GapStatement :=
  PoleGapInduction.gapStatement_of_thirdPort
    (ThirdPortBridgeInduction.thirdPortStatement_of_bridgeless
      (bridgelessThirdPortStatement_of_capped h))

end Erdos1016.ExactMaximumSupport.ThirdPortCappedReduction
