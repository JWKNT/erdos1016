import Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence
import Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Labeled girth and probability laws for raised-girth regions

Ordinary retained girth transfers to the actual induced labeled multigraph.
The transfer uses the proved cycle-word and simple-walk correspondence.
Further vertex deletion can only increase the original uniform forest probability.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
open FiniteMultiGraph ShortProof.CycleCore CubicReduction Nonbacktracking
local instance raisedGirthTransferDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Ordinary physical girth excludes every short labeled cycle word. -/
theorem physical_no_short_of_girth (H : PhysicalGraph) (D : ℕ)
    (hg : ShortWalks.GirthGreater H.toSimpleGraph D) :
    ¬(asMultigraph H).HasCycleShorterThan (D+1) := by
  rintro ⟨x,hx,hlen⟩
  let C : H.CycleWord := ⟨x,(asMultigraph_isCycleWord_iff H x).mp hx⟩
  obtain ⟨u,p,hp,he⟩ := exists_cycle_walk_of_cycleWord H C
  have heq : H.wordLength C.1=p.length := by
    rw [←he]
    exact cycleWordOfWalk_length H p hp
  have hgt := hg u p hp
  change H.wordLength C.1<D+1 at hlen
  omega

/-- Both retained constructors have exactly the same vertex and physical edge labels. -/
theorem induced_asMultigraph (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hloop : ∀e∈G.internalEdges R,G.src e≠G.dst e)
    (hsimple : ∀e∈G.internalEdges R,∀f∈G.internalEdges R,
      ((G.src e=G.src f ∧ G.dst e=G.dst f) ∨
       (G.src e=G.dst f ∧ G.dst e=G.src f))→e=f) :
    asMultigraph (InducedSimpleRealization.graph G R hloop hsimple)=PieceCore.Induced.graph G R := rfl

/-- Retained ordinary girth gives the actual induced multigraph girth predicate. -/
theorem induced_no_short_of_retained_girth (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hloop : ∀e∈G.internalEdges R,G.src e≠G.dst e)
    (hsimple : ∀e∈G.internalEdges R,∀f∈G.internalEdges R,
      ((G.src e=G.src f ∧ G.dst e=G.dst f) ∨
       (G.src e=G.dst f ∧ G.dst e=G.src f))→e=f)
    (D : ℕ) (hg : ShortWalks.GirthGreater
      (InducedSimpleRealization.graph G R hloop hsimple).toSimpleGraph D) :
    ¬(PieceCore.Induced.graph G R).HasCycleShorterThan (D+1) := by
  rw [←induced_asMultigraph G R hloop hsimple]
  exact physical_no_short_of_girth _ D hg

/-- A retained region's forest event is hereditary under further deletion. -/
theorem forest_restrict_region (G : FiniteMultiGraph) {R S : Finset G.Vertex}
    (hRS : R⊆S) (x : G.EdgeWord)
    (hx : G.IsForestWord (G.restrictEdges (G.internalEdges S) x)) :
    G.IsForestWord (G.restrictEdges (G.internalEdges R) x) := by
  apply hx.mono
  intro e he
  have hmem : e∈G.internalEdges R := by
    by_contra hn
    exact he (by simp [FiniteMultiGraph.restrictEdges,hn])
  have hnonzero : x e≠0 := by simpa [FiniteMultiGraph.restrictEdges,hmem] using he
  have hend := (Finset.mem_filter.mp hmem).2
  have hmemS : e∈G.internalEdges S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hRS hend.1,hRS hend.2⟩
  simpa [FiniteMultiGraph.restrictEdges,hmemS] using hnonzero

/-- The probability uses the same original cycle space on both sides. -/
theorem region_probability_antitone (G : FiniteMultiGraph) {R S : Finset G.Vertex}
    (hRS : R⊆S) : G.regionForestProbability S≤G.regionForestProbability R := by
  rw [G.regionForestProbability_eq_density,G.regionForestProbability_eq_density]
  unfold Finite.density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finite.count_mono (fun x hx => forest_restrict_region G hRS x.1 hx)

/-- Enlarging a deleted set increases its exterior forest probability. -/
theorem exterior_probability_mono (G : FiniteMultiGraph) {P Q : Finset G.Vertex}
    (hPQ : P⊆Q) : G.regionForestProbability Pᶜ≤G.regionForestProbability Qᶜ :=
  region_probability_antitone G (Finset.compl_subset_compl.mpr hPQ)

/-- Every selected stage has actual labeled girth above its current scale. -/
theorem vertices_no_short (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ→ℕ) (n : ℕ) (hD : 2≤D n) (hmax : ∀v,G.degree v≤3) :
    ¬(PieceCore.Induced.graph G
      (P∪RegionPackingSequence.vertices G P D (n+1))ᶜ).HasCycleShorterThan (D n+1) := by
  obtain ⟨hloop,hsimple,hg⟩ := RegionPackingSequence.retained_high_girth G P D n hD hmax
  exact induced_no_short_of_retained_girth G _ hloop hsimple _ hg

end Erdos1016.ExactMaximumSupport.LargeGirth.RaisedGirth
