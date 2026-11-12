import Erdos1016.ExactMaximumSupport.NetworkExteriorRank
import Erdos1016.ExactMaximumSupport.GeodesicPathMarker
import Erdos1016.ExactMaximumSupport.ThinIntervalSize
import Erdos1016.Graph.Multigraph.SubcubicOrder
import Erdos1016.Graph.Multigraph.InducedDeletionBounds
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Order and path-deletion rank of an actual two-pole

The connected degree ledger gives order twice rank. An actual terminal path
has one more support vertex than edge, and each support vertex has at most
one physical incidence leaving the support. The exterior cubic ledger then
gives the path-length plus exterior-rank bound, also for an empty exterior.
No shortestness or bridgelessness is needed for these two identities.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.PolePathRank
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph LargeGirth

local instance polePathRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The physical order identity for a connected two-pole. -/
theorem physical_order (G : FiniteMultiGraph) (s t : G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hne : s ≠ t)
    (hs : G.degree s = 2) (ht : G.degree t = 2)
    (hother : ∀ v, v ≠ s → v ≠ t → G.degree v = 3) :
    G.vertexCount = 2 * G.cycleRank := by
  have hdeg (v : G.Vertex) : G.degree v ≤ 3 := by
    by_cases hvs : v = s
    · simp [hvs, hs]
    by_cases hvt : v = t
    · simp [hvt, ht]
    exact (hother v hvs hvt).le
  have hcubic (v : G.Vertex) (hv : v ∉ ({s,t} : Finset G.Vertex)) : G.degree v = 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact hother v hv.1 hv.2
  have h := G.order_add_two_eq_twice_rank_add_marked_deficit {s,t} hG hdeg hcubic
  simp [hne, hs, ht] at h
  omega

/-- A bound on the physical cut from the actual outside-incidence bound. -/
theorem cut_le_card_of_outside_incidence (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (hinc : ∀ v ∈ P, G.selectedDegree (ThinIntervalBoundary.outsideWord G P) v ≤ 1) :
    (G.cutEdges P).card ≤ P.card := by
  have hc : (G.cutEdges P).filter
      (fun e => ThinIntervalBoundary.outsideWord G P e ≠ 0) = G.cutEdges P := by
    apply Finset.filter_eq_self.mpr
    intro e he
    have hi : e ∉ G.internalEdges P := by
      simp only [cutEdges, internalEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      tauto
    simp [ThinIntervalBoundary.outsideWord, restrictEdges, hi]
  have hsum := G.sum_region_selectedDegree (ThinIntervalBoundary.outsideWord G P) P
  rw [hc] at hsum
  have hbound : (∑ v ∈ P, G.selectedDegree (ThinIntervalBoundary.outsideWord G P) v) ≤ P.card := by
    calc
      _ ≤ ∑ _v ∈ P, 1 := Finset.sum_le_sum hinc
      _ = _ := by simp
  omega

/-- The complement of an actual terminal path retains rank at least rank minus path length. -/
theorem physical_path_rank (G : FiniteMultiGraph) (s t : G.Vertex)
    (hG : G.toSimpleGraph.Connected) (hloop : G.IsLoopless)
    (hs : G.degree s = 2) (ht : G.degree t = 2)
    (hother : ∀ v, v ≠ s → v ≠ t → G.degree v = 3)
    (A : G.EdgeWord) (hA : G.looplessNetwork.IsPathWord s t (G.nonloopWord A)) :
    G.cycleRank ≤ Network.size A +
      (PieceCore.Induced.graph G (CycleRegions.region G A)ᶜ).cycleRank := by
  let P := GeodesicPathMarker.support G A
  have horder := physical_order G s t hG hA.1 hs ht hother
  have hcard : P.card = Network.size A + 1 := GeodesicPathMarker.path_support_card G hloop hA
  have hcut : (G.cutEdges Pᶜ).card ≤ P.card := by
    rw [G.cutEdges_compl]
    exact cut_le_card_of_outside_incidence G P
      (GeodesicPathMarker.outside_incidence_le_one G hloop hA hs.le ht.le
        (fun v hvs hvt => (hother v hvs hvt).le))
  have hsp : s ∈ P := by
    apply (GeodesicPathMarker.mem_support G A s).mpr
    rw [G.selectedDegree_eq_deg A (hloop.word A), hA.2.1]
    decide
  have htp : t ∈ P := by
    apply (GeodesicPathMarker.mem_support G A t).mpr
    rw [G.selectedDegree_eq_deg A (hloop.word A), hA.2.2.1]
    decide
  have hcubic : ∀ v ∈ Pᶜ, G.degree v = 3 := by
    intro v hv
    have hvp := Finset.mem_compl.mp hv
    exact hother v (fun h => hvp (h ▸ hsp)) (fun h => hvp (h ▸ htp))
  have hledger := ThinIntervalSize.region_ledger G Pᶜ hcubic
  have htotal : Pᶜ.card + P.card = G.vertexCount := by
    simp
  change G.cycleRank ≤ Network.size A + (PieceCore.Induced.graph G Pᶜ).cycleRank
  by_cases hnon : Pᶜ.Nonempty
  · have hcomp := ThinIntervalSize.componentCount_pos G Pᶜ hnon
    omega
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnon
    have hz : Pᶜ.card = 0 := by rw [hempty]; rfl
    omega

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Relabelling retains the number of selected physical labels. -/
theorem size_wordEquiv (A : N.Word) :
    Network.size (NetworkMultigraph.wordEquiv N A) = Network.size A := by
  unfold Network.size
  rw [Finset.card_filter, Finset.card_filter]
  simpa only [NetworkMultigraph.wordEquiv_apply] using
    (Equiv.sum_comp (NetworkMultigraph.edges N)
    (fun e => if NetworkMultigraph.wordEquiv N A e ≠ 0 then 1 else 0)).symm

/-- A connected network with precisely two degree-two ports has order twice rank. -/
theorem order_eq_twice_rank (s t : V) (hN : N.graph.Connected) (hne : s ≠ t)
    (hs : N.deg (fun _ => 1) s = 2) (ht : N.deg (fun _ => 1) t = 2)
    (hother : ∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3) :
    Fintype.card V = 2 * networkRank N := by
  have hh := physical_order (NetworkMultigraph.graph N)
    (NetworkMultigraph.vertices N s) (NetworkMultigraph.vertices N t)
    (NetworkMultigraph.connected N hN)
    (fun h => hne ((NetworkMultigraph.vertices N).injective h))
    (by simpa using hs) (by simpa using ht) (by
      intro v hvs hvt
      obtain ⟨w,rfl⟩ := (NetworkMultigraph.vertices N).surjective v
      simpa using hother w (fun h => hvs (congrArg (NetworkMultigraph.vertices N) h))
        (fun h => hvt (congrArg (NetworkMultigraph.vertices N) h)))
  simpa only [NetworkMultigraph.cycleRank] using hh

/-- The exact exterior expression used in the pole outside-rank theorem. -/
theorem rank_le_path_size_add_outside_rank (s t : V) (hN : N.graph.Connected)
    (hs : N.deg (fun _ => 1) s = 2) (ht : N.deg (fun _ => 1) t = 2)
    (hother : ∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3)
    (A : N.Word) (hA : N.IsPathWord s t A) :
    networkRank N ≤ Network.size A +
      networkRank (N.sub (fun e => N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0)) := by
  rw [NetworkExteriorRank.outside_rank_eq]
  have hp := NetworkMultigraph.isPathWord_push (NetworkMultigraph.relabel N) hA
  rw [← NetworkMultigraph.nonloop_wordEquiv] at hp
  have hh := physical_path_rank (NetworkMultigraph.graph N)
    (NetworkMultigraph.vertices N s) (NetworkMultigraph.vertices N t)
    (NetworkMultigraph.connected N hN) (NetworkMultigraph.isLoopless N)
    (by simpa using hs) (by simpa using ht) (by
      intro v hvs hvt
      obtain ⟨w,rfl⟩ := (NetworkMultigraph.vertices N).surjective v
      simpa using hother w (fun h => hvs (congrArg (NetworkMultigraph.vertices N) h))
        (fun h => hvt (congrArg (NetworkMultigraph.vertices N) h)))
    (NetworkMultigraph.wordEquiv N A) hp
  simpa only [NetworkMultigraph.cycleRank, size_wordEquiv] using hh

/-- The order formula specialized to the existing bridgeless-pole interface. -/
theorem bridgeless_order (s t : V) (hN : N.IsBridgelessTwoPole s t) :
    Fintype.card V = 2 * networkRank N :=
  order_eq_twice_rank N s t hN.connected hN.ne hN.deg_s hN.deg_t hN.deg_other

/-- The rank ledger specialized to the existing bridgeless-pole interface. -/
theorem bridgeless_path_rank (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (A : N.Word) (hA : N.IsPathWord s t A) :
    networkRank N ≤ Network.size A +
      networkRank (N.sub (fun e => N.deg A (N.src e) = 0 ∧ N.deg A (N.dst e) = 0)) :=
  rank_le_path_size_add_outside_rank N s t hN.connected hN.deg_s hN.deg_t hN.deg_other A hA

end Erdos1016.ExactMaximumSupport.PolePathRank
