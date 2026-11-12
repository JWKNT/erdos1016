import Erdos1016.ExactMaximum.PoleInputs
import Erdos1016.ExactMaximumSupport.NetworkMultigraph
import Erdos1016.ExactMaximumSupport.PathExteriorProbability
import Erdos1016.Probability.Avoidance.RegionPackingBound
import Erdos1016.ExactMaximumSupport.CycleRegions

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Short cycles outside a prescribed path

Cycle regions are the actual vertices incident with selected physical labels.
The imported cycle-region lemmas prove their geometry and supply their internal even words.
The network adapter preserves every edge label, including parallel edges.

Path density at least 501/1000 supplies a strict forest margin of 1/2000.
The existing small-cut packing theorem then gives the explicit packing constant.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.PoleCyclePacking
open FiniteMultiGraph BoundaryTrace BoundaryTrace.Network BoundaryDecay CycleRegions

local instance polePackingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The explicit finite bound uses the strict margin 1/2000 below 501/1000. -/
theorem card_le_of_exterior_probability (G : FiniteMultiGraph)
    (hG : G.toSimpleGraph.Connected) (hdegree : ∀ v, G.degree v ≤ 3)
    {ι : Type*} [Fintype ι] (Z : ι → G.EdgeWord) (hz : ∀ i, G.IsCycleWord (Z i))
    (hdisj : Pairwise fun i j => Disjoint (region G (Z i)) (region G (Z j)))
    (P : Finset G.Vertex) (hout : ∀ i, Disjoint (region G (Z i)) P)
    (d : ℕ) (hsize : ∀ i, G.wordLength (Z i) ≤ d)
    (hforest : (501/1000 : ℝ) ≤ Finite.density (fun z : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges Pᶜ) z.1))) :
    Fintype.card ι ≤ 1000 * (d+1) * 2^d := by
  have hE (i : ι) : G.internalEdges (region G (Z i)) ⊆ G.internalEdges Pᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_compl.mpr (fun hp => Finset.disjoint_left.mp (hout i) hh.1 hp),
      Finset.mem_compl.mpr (fun hp => Finset.disjoint_left.mp (hout i) hh.2 hp)⟩
  have h := G.smallCut_packing_card_le (fun i => region G (Z i)) hG hdisj
    (fun i => cycle_region_connected G (Z i) (hz i)) Finset.univ d
    (fun i _ => (cycle_cut_le_length G (Z i) (hz i) hdegree).trans (hsize i))
    (fun i _ => cycle_region_cyclic G (Z i) (hz i))
    (G.internalEdges Pᶜ) (fun i _ => hE i) (1/2000) (by norm_num)
    (lt_of_lt_of_le (by norm_num) hforest)
  have hh : (Fintype.card ι : ℝ) ≤ 1000 * ((d:ℝ)+1) * (2:ℝ)^d := by
    simpa only [Finset.card_univ] using h.trans_eq (by ring)
  exact_mod_cast hh

section NetworkAdapter
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

@[simp] theorem region_wordEquiv (x : N.Word) (v : V) :
    NetworkMultigraph.vertices N v ∈ region (NetworkMultigraph.graph N) (NetworkMultigraph.wordEquiv N x)
      ↔ 0 < N.deg x v := by
  rw [mem_region, NetworkMultigraph.selectedDegree_wordEquiv]

theorem cycle_wordEquiv (x : N.Word) (hx : N.IsCycleWord x) :
    (NetworkMultigraph.graph N).IsCycleWord (NetworkMultigraph.wordEquiv N x) := by
  apply ((NetworkMultigraph.graph N).isCycleWord_iff_looplessNetwork _
    (fun e he => (NetworkMultigraph.isLoopless N e he).elim)).mpr
  rw [NetworkMultigraph.nonloop_wordEquiv]
  exact (NetworkMultigraph.relabel N).isCycleWord_push hx

@[simp] theorem length_wordEquiv (x : N.Word) :
    (NetworkMultigraph.graph N).wordLength (NetworkMultigraph.wordEquiv N x) = size x := by
  unfold FiniteMultiGraph.wordLength size
  rw [Finset.card_filter, Finset.card_filter, ← Equiv.sum_comp (NetworkMultigraph.edges N)]
  simp only [NetworkMultigraph.wordEquiv_apply]

theorem regions_disjoint (x y : N.Word) (hxy : N.VertexDisjoint x y) :
    Disjoint (region (NetworkMultigraph.graph N) (NetworkMultigraph.wordEquiv N x))
      (region (NetworkMultigraph.graph N) (NetworkMultigraph.wordEquiv N y)) := by
  apply Finset.disjoint_left.mpr
  intro v hx hy
  obtain ⟨w, rfl⟩ := (NetworkMultigraph.vertices N).surjective v
  rw [region_wordEquiv] at hx hy
  rcases hxy w with h | h <;> omega

/-- The exact network interface keeps the designated path and every cycle label. -/
theorem network_packing_bound (d : ℕ) (s t : V) (A : N.Word)
    (hN : N.graph.Connected) (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hA : N.IsPathWord s t A) (hpaths : 501*2^networkRank N ≤ 1000*N.numPaths s t)
    {ι : Type*} [Fintype ι] (Z : ι → N.Word) (hz : ∀ i, N.IsCycleWord (Z i))
    (hout : ∀ i, N.VertexDisjoint (Z i) A)
    (hdisj : ∀ i j, i ≠ j → N.VertexDisjoint (Z i) (Z j))
    (hsize : ∀ i, size (Z i) ≤ d) : Fintype.card ι ≤ 1000*(d+1)*2^d := by
  let G := NetworkMultigraph.graph N
  let a := NetworkMultigraph.wordEquiv N A
  let P := region G a
  have hG : G.toSimpleGraph.Connected := NetworkMultigraph.connected N hN
  have hd : ∀ v, G.degree v ≤ 3 := by
    intro v
    obtain ⟨w, rfl⟩ := (NetworkMultigraph.vertices N).surjective v
    simpa only [G, NetworkMultigraph.degree] using hdegree w
  have hp : 501*2^G.cycleRank ≤
      1000*G.looplessNetwork.numPaths (NetworkMultigraph.vertices N s) (NetworkMultigraph.vertices N t) := by
    simpa only [G, NetworkMultigraph.cycleRank, NetworkMultigraph.numPaths] using hpaths
  have ha : G.boundary a =
      G.looplessNetwork.pathDemand (NetworkMultigraph.vertices N s) (NetworkMultigraph.vertices N t) := by
    rw [← G.nonloopWord_boundary]
    exact (NetworkMultigraph.isPathWord_push (NetworkMultigraph.relabel N) hA).boundary_eq
  have hzero : ∀ e ∈ G.internalEdges Pᶜ, a e = 0 := by
    intro e he
    by_contra hne
    have hs : G.src e ∉ P := Finset.mem_compl.mp (Finset.mem_filter.mp he).2.1
    exact hs ((mem_region G a _).mpr (G.selectedDegree_src_pos hne))
  have hf := PathExteriorProbability.restrictedForestProbability_ge_501 G
    (NetworkMultigraph.isLoopless N) hG (NetworkMultigraph.vertices N s)
    (NetworkMultigraph.vertices N t) (fun h => hA.1 ((NetworkMultigraph.vertices N).injective h))
    hp a ha (G.internalEdges Pᶜ) hzero
  apply card_le_of_exterior_probability G hG hd (fun i => NetworkMultigraph.wordEquiv N (Z i))
    (fun i => cycle_wordEquiv N (Z i) (hz i))
    (fun i j hij => regions_disjoint N (Z i) (Z j) (hdisj i j hij)) P
    (fun i => regions_disjoint N (Z i) A (hout i)) d
  · intro i
    simpa only [G, length_wordEquiv] using hsize i
  · exact hf

end NetworkAdapter

/-- Proposition 5.3, Step 3, with the explicit constant `1000*(d+1)*2^d`. -/
theorem poleCyclePackingStatement : ExactMaximum.PoleCyclePackingStatement := by
  intro d
  refine ⟨1000*(d+1)*2^d, ?_⟩
  intro V E _ _ N s t A hN hd hA hp ι _ Z hz hout hdisj hsize
  exact network_packing_bound N d s t A hN hd hA hp Z hz hout hdisj hsize

end Erdos1016.ExactMaximumSupport.PoleCyclePacking
