import Erdos1016.ExactMaximumSupport.PoleOutsideRank
import Erdos1016.ExactMaximumSupport.PolePathRank
import Erdos1016.ExactMaximumSupport.NetworkGeodesic
import Erdos1016.ExactMaximumSupport.BridgelessLayers
import Erdos1016.ExactMaximumSupport.PoleParallelCount
import Erdos1016.ExactMaximumSupport.NetworkPathMarker
import Erdos1016.ExactMaximumSupport.LayerCountLedger

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The thin-layer input for path-rich poles

The outside-rank theorem bounds the excess over two vertices per inner layer.
Nonordinary thin layers are charged to parallel-edge vertices outside the path.
All constants are uniform, including poles of rank one.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleThinLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Proposition 5.3, including its final counting step, in the original network model. -/
theorem thinLayersStatement : ExactMaximum.ThinLayersStatement := by
  obtain ⟨C,hC⟩ := PoleOutsideRank.poleOutsideRankStatement
  refine ⟨10 * C + 8,?_⟩
  intro V E _ _ N s t hN hpaths
  obtain ⟨A,hA,hshort⟩ := NetworkGeodesic.exists_shortest_path N hN.connected s t hN.ne
  have hdegree (v : V) : N.deg (fun _ => 1) v ≤ 3 := by
    by_cases hs : v = s
    · subst v
      exact hN.deg_s.le.trans (by decide)
    by_cases ht : v = t
    · subst v
      exact hN.deg_t.le.trans (by decide)
    exact (hN.deg_other v hs ht).le
  have hout := hC V E N s t A hN.connected hN.deg_s.le hN.deg_t.le
    hN.deg_other hA hshort hpaths
  have horder := PolePathRank.bridgeless_order N s t hN
  have hdefect : networkRank N ≤ N.graph.dist s t + C := by
    have h := PolePathRank.bridgeless_path_rank N s t hN A hA
    rw [hshort] at h
    omega
  let level : V → ℕ := N.graph.dist s
  let ell := N.graph.dist s t
  have hcard (j : ℕ) : (LayerCountLedger.layer level j).card =
      Nat.card {v : V // N.graph.dist s v = j} := by
    simp only [LayerCountLedger.layer, level, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hlower (j : ℕ) (hj : 0 < j) (hjell : j < ell) :
      2 ≤ (LayerCountLedger.layer level j).card := by
    rw [hcard]
    exact BridgelessLayers.internal_layer_card_ge_two N s t hN j hj hjell
  have hthin (j : ℕ) : LayerCountLedger.Thin level ell j ↔ N.IsThinLayer s t j := by
    unfold LayerCountLedger.Thin Network.IsThinLayer
    rw [hcard]
  have hsmall : (LayerCountLedger.exceptional level ell).card ≤ 6 * C + 6 :=
    LayerCountLedger.exceptional_card_le level ell C hlower (by omega)
  have hell : ell ≤ networkRank N + 1 :=
    LayerCountLedger.ell_le_rank_add_one level ell (networkRank N) hlower horder
  let bad : Finset V := Finset.univ.filter fun v => N.deg A v = 0 ∧ N.OnParallel v
  have hbad : bad.card ≤ 2 * C := by
    have h := PoleParallelCount.card_parallel_outside_le_twice_rank N A hA
      hN.deg_s.le hN.deg_t.le hdegree
    exact h.trans (Nat.mul_le_mul_left 2 hout)
  have hcharge (j : ℕ) (hj : LayerCountLedger.Thin level ell j)
      (hno : ¬ N.IsOrdinaryLayer s t j) : ∃ v ∈ bad, level v = j := by
    obtain ⟨v,hv,hzero,hparallel⟩ :=
      NetworkPathMarker.parallel_witness_of_not_ordinary N hN.connected hA hshort j
        ((hthin j).mp hj) hno
    exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero,hparallel⟩,hv⟩
  have hordinary := LayerCountLedger.nonordinary_card_le level ell
    (N.IsOrdinaryLayer s t) bad hcharge
  constructor
  · intro v
    have hd := LayerCountLedger.level_le_ell_add_exceptional level ell v
      (fun j hj => BridgelessLayers.exists_vertex_at_distance N hN.connected s v j hj)
    change level v ≤ networkRank N + (10 * C + 8)
    omega
  · have hcount : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} =
        (Finset.univ.filter fun v => ¬ N.IsOrdinaryLayer s t (level v)).card := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, level]
    rw [hcount]
    omega

end Erdos1016.ExactMaximumSupport
