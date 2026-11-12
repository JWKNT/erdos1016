import Erdos1016.ExactMaximumSupport.ShortCycleCyclicCut
import Erdos1016.ExactMaximumSupport.NetworkMultigraph
import Erdos1016.ExactMaximumSupport.PoleCyclePacking
import Erdos1016.ExactMaximum.NetSmallCut

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A short cycle gives a small cyclic cut in the original network

The canonical physical model keeps every vertex and every parallel label.
Cycles on each shore and the crossing-label cardinality pull back exactly.
The resulting cut is the positive-degree support of the original cycle word.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkShortCycleCut
open BoundaryTrace BoundaryTrace.Network BoundaryDecay FiniteMultiGraph

local instance networkShortCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A cycle in a physical vertex region pulls back to an actual network cycle in that shore. -/
theorem hasCycleIn_pull (U : Finset (NetworkMultigraph.graph N).Vertex)
    (hU : (NetworkMultigraph.graph N).HasCycleIn U) :
    ∃ y : N.Word, N.IsCycleWord y ∧
      Within y (N.inside fun v => NetworkMultigraph.vertices N v ∈ U) := by
  obtain ⟨x,hx,hsupport⟩ := hU
  have hx' := ((NetworkMultigraph.graph N).isCycleWord_iff_looplessNetwork x
    ((NetworkMultigraph.isLoopless N).word x)).mp hx
  have hy := (NetworkMultigraph.relabel N).symm.isCycleWord_push hx'
  refine ⟨(NetworkMultigraph.wordEquiv N).symm x,hy,?_⟩
  intro e he
  have hh := hsupport (NetworkMultigraph.edges N e) he
  simpa only [NetworkMultigraph.src_edges,NetworkMultigraph.dst_edges] using hh

/-- Both actual cyclic shores pull back through the canonical vertex equivalence. -/
theorem cyclicCut_pull (U : Finset (NetworkMultigraph.graph N).Vertex)
    (hU : (NetworkMultigraph.graph N).IsCyclicCut U) :
    N.IsCyclicCut (fun v => NetworkMultigraph.vertices N v ∈ U) := by
  constructor
  · obtain ⟨y,hy,hw⟩ := hasCycleIn_pull N U hU.1
    rw [numCycles_sub]
    haveI : Nonempty {y : N.Word // N.IsCycleWord y ∧
        Within y (N.inside fun v => NetworkMultigraph.vertices N v ∈ U)} := ⟨⟨y,hy,hw⟩⟩
    exact Nat.card_pos
  · obtain ⟨y,hy,hw⟩ := hasCycleIn_pull N Uᶜ hU.2
    have hw' : Within y (N.outside fun v => NetworkMultigraph.vertices N v ∈ U) := by
      intro e he
      exact ⟨Finset.mem_compl.mp (hw e he).1,Finset.mem_compl.mp (hw e he).2⟩
    rw [numCycles_sub]
    haveI : Nonempty {y : N.Word // N.IsCycleWord y ∧
        Within y (N.outside fun v => NetworkMultigraph.vertices N v ∈ U)} := ⟨⟨y,hy,hw'⟩⟩
    exact Nat.card_pos

/-- The crossing-label count is exactly the physical cut cardinality. -/
theorem cutSize_preimage (U : Finset (NetworkMultigraph.graph N).Vertex) :
    N.cutSize (fun v => NetworkMultigraph.vertices N v ∈ U) =
      ((NetworkMultigraph.graph N).cutEdges U).card := by
  have hm (e : E) : N.crosses (fun v => NetworkMultigraph.vertices N v ∈ U) e ↔
      NetworkMultigraph.edges N e ∈ (NetworkMultigraph.graph N).cutEdges U := by
    simp only [Network.crosses,cutEdges,Finset.mem_filter,Finset.mem_univ,true_and,
      NetworkMultigraph.src_edges,NetworkMultigraph.dst_edges]
    tauto
  unfold Network.cutSize
  calc
    _ = Nat.card {e : (NetworkMultigraph.graph N).Edge //
        e ∈ (NetworkMultigraph.graph N).cutEdges U} :=
      Nat.card_congr (Equiv.subtypeEquiv (NetworkMultigraph.edges N) hm)
    _ = _ := by simp

/-- The selected support of a short actual cycle is a small cyclic cut. -/
theorem cycle_support_cyclic_cut (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (z : N.Word) (hz : N.IsCycleWord z) (d : ℕ) (hd : size z ≤ d)
    (hr : 2*d < networkRank N) :
    N.IsCyclicCut (fun v => 0 < N.deg z v) ∧
      N.cutSize (fun v => 0 < N.deg z v) ≤ d := by
  let G := NetworkMultigraph.graph N
  let x := NetworkMultigraph.wordEquiv N z
  have hdeg : ∀ v, G.degree v ≤ 3 := by
    intro v
    obtain ⟨w,rfl⟩ := (NetworkMultigraph.vertices N).surjective v
    simpa only [G,NetworkMultigraph.degree] using hdegree w
  have hx : G.IsCycleWord x := PoleCyclePacking.cycle_wordEquiv N z hz
  have hlength : G.wordLength x ≤ d := by
    simpa only [G,x,PoleCyclePacking.length_wordEquiv] using hd
  have hrank : 2*d < G.cycleRank := by
    simpa only [G,NetworkMultigraph.cycleRank] using hr
  obtain ⟨hcut,hsize⟩ := ShortCycleCyclicCut.cycle_region_cyclic_cut G
    (NetworkMultigraph.isLoopless N) hdeg x hx d hlength hrank
  have hc := cyclicCut_pull N (CycleRegions.region G x) hcut
  have hs := (cutSize_preimage N (CycleRegions.region G x)).trans_le hsize
  simpa only [G,x,PoleCyclePacking.region_wordEquiv] using And.intro hc hs

/-- Rank at least nine turns any cycle of size at most four into a cyclic cut of size at most four. -/
theorem exists_cyclicCut_le_four (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hrank : 9 ≤ networkRank N) (z : N.Word) (hz : N.IsCycleWord z) (hsize : size z ≤ 4) :
    ∃ S : V → Prop, N.IsCyclicCut S ∧ N.cutSize S ≤ 4 := by
  exact ⟨fun v => 0 < N.deg z v,
    cycle_support_cyclic_cut N hdegree z hz 4 hsize (by omega)⟩

/-- A subcubic rank-at-least-nine network with all cyclic cuts at least five has no short cycle. -/
theorem four_lt_size_of_cyclic_cut_lower_bound
    (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3) (hrank : 9 ≤ networkRank N)
    (hcut : ∀ S : V → Prop, N.IsCyclicCut S → 5 ≤ N.cutSize S)
    (z : N.Word) (hz : N.IsCycleWord z) : 4 < size z := by
  by_contra h
  obtain ⟨S,hS,hs⟩ := exists_cyclicCut_le_four N hdegree hrank z hz (by omega)
  have hh := hcut S hS
  omega

end Erdos1016.ExactMaximumSupport.NetworkShortCycleCut
