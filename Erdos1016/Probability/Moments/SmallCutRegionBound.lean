import Erdos1016.Probability.Moments.SmallCutBound
import Erdos1016.Probability.Cylinders.RegionCycleEvents
import Erdos1016.CycleSpace.Graphical.DisjointRegionCuts

set_option autoImplicit false

/-!
# The small-cut forest bound for actual multigraph regions

This is the geometric form of Corollary 2. The events, uniform marginals,
conditional interior laws, and exceptional-partner count are all supplied
by the actual graph. No correlation or probability estimate is an input.
-/

noncomputable section

namespace Erdos1016.FiniteMultiGraph

open BoundaryDecay

variable {ι : Type*} [Fintype ι]
local instance smallCutRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Any edge set containing a nonempty family of disjoint connected cyclic
regions with cuts at most `d` obeys the manuscript's small-cut estimate. -/
theorem smallCut_forest_bound (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (s : Finset ι) (hs : s.Nonempty) (d : ℕ)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d)
    (hcyclic : ∀ i ∈ s, ∃ z : G.internalCycleSpace (U i), z ≠ 0)
    (E : Finset G.Edge) (hE : ∀ i ∈ s, G.internalEdges (U i) ⊆ E) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤
      (1 / 2 : ℝ) + ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * (s.card : ℝ)) := by
  apply small_cut_event_bound s hs (fun i => G.RegionCycleEvent (U i))
    (fun x => G.IsForestWord (G.restrictEdges E x.1)) (DisjointRegionCuts.Exceptional G U) d
  · intro i hi
    exact G.regionCycleEvent_probability_ge (U i) (hcyclic i hi) d (hcut i hi)
  · intro i hi
    have h := DisjointRegionCuts.exceptional_partner_card_le G U hG hdisj hconn i s
    have heq : (s.filter fun j => i ≠ j ∧ DisjointRegionCuts.Exceptional G U i j) =
        s.filter fun j => j ≠ i ∧ DisjointRegionCuts.Exceptional G U i j := by
      ext j
      simp only [Finset.mem_filter, ne_comm]
    rw [heq]
    exact h.trans (hcut i hi)
  · intro i hi j hj hij hordinary
    apply G.regionCycleEvent_pair_le (U i) (U j) (hdisj hij) 2
    have hcutpair := le_of_not_gt hordinary
    have he (k : ι) : DisjointRegionCuts.ZeroCut G (U k) =
        fun x : G.CycleSpace => x ∈ G.zeroCutSpace (U k) := by
      funext x
      exact propext (G.mem_zeroCutSpace_iff (U k) x).symm
    simpa only [DisjointRegionCuts.Exceptional, he] using hcutpair
  · intro x hx i hi hcycle
    apply G.regionCycleEvent_not_forest (U i) x hcycle
    apply hx.mono
    intro e he
    by_cases hmem : e ∈ G.internalEdges (U i)
    · have hlarge := hE i hi hmem
      simpa only [restrictEdges, hmem, hlarge, ↓reduceIte] using he
    · simp [restrictEdges, hmem] at he

/-- Corollary 2 on precisely the union of the regions' internal edge sets. -/
theorem smallCut_region_union_bound (G : FiniteMultiGraph) (U : ι → Finset G.Vertex)
    (hG : G.toSimpleGraph.Connected)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hconn : ∀ i, (G.toSimpleGraph.induce (↑(U i) : Set G.Vertex)).Connected)
    (s : Finset ι) (hs : s.Nonempty) (d : ℕ)
    (hcut : ∀ i ∈ s, (G.cutEdges (U i)).card ≤ d)
    (hcyclic : ∀ i ∈ s, ∃ z : G.internalCycleSpace (U i), z ≠ 0) :
    Finite.density (fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (s.biUnion fun i => G.internalEdges (U i)) x.1)) ≤
      (1 / 2 : ℝ) + ((d : ℝ) + 1) * (2 : ℝ) ^ d / (2 * (s.card : ℝ)) := by
  apply G.smallCut_forest_bound U hG hdisj hconn s hs d hcut hcyclic
  intro i hi e he
  exact Finset.mem_biUnion.mpr ⟨i, hi, he⟩

end Erdos1016.FiniteMultiGraph
