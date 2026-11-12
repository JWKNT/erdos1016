import Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
import Erdos1016.ExactMaximumSupport.VertexRankDeletion
import Erdos1016.ExactMaximumSupport.CycleLayerSpan
import Erdos1016.ExactMaximumSupport.CycleRegions
import Erdos1016.ExactMaximum.LooplessBridge

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Size of a minimal cyclic interval

The first-layer deletion is a labelled forest. Its rank loss is bounded.
The actual cycle spans the interval, and the physical boundary has a linear bound.
Together these facts bound the entire interval, including its other components.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.ThinIntervalSize
open FiniteMultiGraph LargeGirth ThinIntervalBoundary
local instance intervalSizeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The cubic region ledger allows any number of components. -/
theorem region_ledger (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hcubic : ∀ v∈R,G.degree v=3) :
    R.card+2*(PieceCore.Induced.graph G R).componentCount =
      2*(PieceCore.Induced.graph G R).cycleRank+(G.cutEdges R).card := by
  have he := (PieceCore.Induced.graph G R).euler_formula
  rw [PieceCore.Induced.vertexCount,PieceCore.Induced.edgeCount] at he
  have hd := G.sum_region_degree R
  have hs : (∑ v∈R,G.degree v)=3*R.card := by
    rw [Finset.sum_congr rfl hcubic]
    simp [Nat.mul_comm]
  rw [hs] at hd
  omega

theorem componentCount_pos (G : FiniteMultiGraph) (R : Finset G.Vertex) (hR : R.Nonempty) :
    0<(PieceCore.Induced.graph G R).componentCount := by
  obtain ⟨v,hv⟩ := hR
  let w : (PieceCore.Induced.graph G R).Vertex := PieceCore.Induced.vertices G R ⟨v,hv⟩
  apply Fintype.card_pos_iff.mpr
  exact ⟨(PieceCore.Induced.graph G R).toSimpleGraph.connectedComponentMk w⟩

/-- The physical span estimate also keeps every nonloop parallel label. -/
theorem physical_cycle_span (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (level : G.Vertex → ℤ) (x : G.EdgeWord) (hx : G.IsCycleWord x)
    (hlevel : ∀ e,x e≠0 → level (G.src e)≤level (G.dst e)+1 ∧
      level (G.dst e)≤level (G.src e)+1)
    (u v : G.Vertex) (hu : u∈CycleRegions.region G x) (hv : v∈CycleRegions.region G x) :
    2*(level v-level u).toNat≤G.wordLength x := by
  have hn := (G.isCycleWord_iff_looplessNetwork x (hloop.word x)).mp hx
  have hp (w : G.Vertex) (hw : w∈CycleRegions.region G x) :
      0<G.looplessNetwork.deg (G.nonloopWord x) w := by
    rw [← G.selectedDegree_eq_deg x (hloop.word x)]
    exact (CycleRegions.mem_region G x w).mp hw
  have h := CycleLayerSpan.twice_level_difference_le_support G.looplessNetwork level
    (G.nonloopWord x) hn (fun e he => hlevel e.1 he) u v (hp u hu) (hp v hv)
  have hcard : (Finset.univ.filter fun e : NonloopEdge G => G.nonloopWord x e≠0).card =
      G.wordLength x := by
    unfold wordLength
    rw [Finset.card_filter,Finset.card_filter]
    exact Equiv.sum_comp (Equiv.subtypeUnivEquiv hloop) (fun e => if x e≠0 then 1 else 0)
  rwa [hcard] at h

/-- A first-layer forest and a spanning cycle bound the actual full interval. -/
theorem card_le_of_first_layer_forest (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (level : G.Vertex → ℤ) (a b : ℤ) (θ : ℕ) (hloop : G.IsLoopless)
    (hdeg : ∀ v,G.degree v≤3) (hcubic : ∀ v,v∉P → G.degree v=3)
    (hfurther : ∀ v∈P,G.selectedDegree (outsideWord G P) v≤1)
    (hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1)
    (hwidth : ∀ j,(layer G P level j).card≤θ)
    (hmark : ∀ j,(Probability.LevelWindowBoundary.markedLayer G P level j).card≤1)
    (hforest : G.IsForestWord (G.restrictEdges
      (G.internalEdges (region G P level a b \ layer G P level a)) (fun _ => 1)))
    (x : G.EdgeWord) (hx : G.IsCycleWord x)
    (hsub : CycleRegions.region G x ⊆ region G P level a b)
    (u v : G.Vertex) (hu : u∈CycleRegions.region G x) (hv : v∈CycleRegions.region G x)
    (hua : level u=a) (hvb : level v=b) :
    (region G P level a b).card≤22*(θ+1) := by
  let R := region G P level a b
  have hab : a≤b := by
    have hh := (mem_region G P level a b u).mp (hsub hu)
    omega
  have hrank : (PieceCore.Induced.graph G R).cycleRank≤2*θ := by
    have hh := VertexRankDeletion.rank_region_le_twice_card_of_diff_forest G R
      (layer G P level a) hloop (fun v _ => hdeg v) hforest
    exact hh.trans (Nat.mul_le_mul_left 2 (hwidth a))
  have hcut := cut_region_le_width G P level a b θ hdeg hfurther hlevel hwidth hmark
  have hledger := region_ledger G R (fun w hw => hcubic w ((mem_region G P level a b w).mp hw).1)
  have hcomp := componentCount_pos G R ⟨u,hsub hu⟩
  have hspan := physical_cycle_span G hloop level x hx (fun e _ => hlevel e) u v hu hv
  rw [hua,hvb] at hspan
  have hlength : G.wordLength x≤R.card := by
    rw [← CycleRegions.cycle_region_card G x hx]
    exact Finset.card_le_card hsub
  have hnat : (b-a+3).toNat=(b-a).toNat+3 := by omega
  rw [hnat] at hcut
  dsimp only [R] at hledger hcomp hlength hrank
  omega

end Erdos1016.ExactMaximumSupport.ThinIntervalSize
