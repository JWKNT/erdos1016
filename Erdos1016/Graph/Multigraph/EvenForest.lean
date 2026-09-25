import Erdos1016.Graph.Multigraph.Forest
import Erdos1016.Graph.EvenForest
import Erdos1016.Boundary.NetworkRealization

set_option autoImplicit false

/-! A nonzero binary cycle-space word cannot be a labelled multigraph forest. -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph
open BoundaryTrace BoundaryDecay

local instance multigraphEvenForestDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Foresthood includes the loop and parallel-edge exclusions, so its selected
labels form a simple network. Relabelling that network reduces the assertion to
the usual fact that a finite even forest has no edges. -/
theorem word_eq_zero_of_boundary_zero_of_forest
    (G : FiniteMultiGraph) (x : G.EdgeWord)
    (hb : G.boundary x = 0) (hf : G.IsForestWord x) : x = 0 := by
  classical
  let E := {e : G.Edge // x e ≠ 0}
  let N : Network G.Vertex E := {
    src := fun e => G.src e.1
    dst := fun e => G.dst e.1
    noLoops := fun e => hf.1 e.1 e.2 }
  have hs : SimpleNetwork N := by
    intro e f h
    exact Subtype.ext (hf.2.1 e.1 f.1 e.2 f.2 h)
  let y : N.Word := fun e => x e.1
  have hb' : N.boundary y = 0 := by
    rw [← hb]
    funext v
    let f : G.Edge → F₂ := fun e =>
      (if G.src e = v then x e else 0) + (if G.dst e = v then x e else 0)
    have hz : (∑ e : {e : G.Edge // ¬ x e ≠ 0}, f e.1) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hx : x e.1 = 0 := not_ne_iff.mp e.2
      simp [f, hx]
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun e : G.Edge => x e ≠ 0) f
    rw [hz, add_zero] at hsum
    rw [Network.boundary_apply, ← Finset.sum_add_distrib]
    calc
      _ = ∑ e : E, f e.1 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases hsrc : G.src e.1 = v <;> by_cases hdst : G.dst e.1 = v <;>
          simp [N, y, f, hsrc, hdst]
      _ = ∑ e, f e := hsum
      _ = _ := rfl
  have hg : N.selectedGraph y = G.selectedGraph x := by
    ext u v
    constructor
    · rintro ⟨e, he, h | h⟩
      · exact ⟨by intro huv; exact N.noLoops e (h.1.trans (huv.trans h.2.symm)),
          e.1, e.2, Or.inl h⟩
      · exact ⟨by intro huv; exact N.noLoops e (h.1.trans (huv.symm.trans h.2.symm)),
          e.1, e.2, Or.inr h⟩
    · rintro ⟨_, e, he, h⟩
      exact ⟨⟨e, he⟩, he, h⟩
  let H := physicalize N hs
  let z : H.CycleSpace := physicalCycleEquiv N hs ⟨y, hb'⟩
  let iso : N.selectedGraph y ≃g H.selectedGraph z.1 := {
    toEquiv := (physicalReindex N hs).vertices
    map_rel_iff' := by
      intro u v
      exact selected_reindex_adj (physicalReindex N hs) y u v }
  have hforest : H.IsForest z.1 := by
    apply (acyclic_iff_of_iso iso).mp
    rw [hg]
    exact hf.2.2
  have hz : z.1 = 0 :=
    Proof.CycleSpaceForestZero.word_eq_zero_of_boundary_zero_of_forest H z.1 z.2 hforest
  funext e
  by_contra he
  have hye : y ⟨e, he⟩ = 0 := by
    have hz' := congrFun hz ((physicalReindex N hs).edges ⟨e, he⟩)
    simpa [z, physicalCycleEquiv, PhysicalGraph.traceCycleEquiv,
      Network.Reindex.cycleEquiv, Network.Reindex.wordEquiv] using hz'
  exact he hye

/-- Selecting every edge of a nonzero even word rules out a forest, regardless
of what happens on the other edge labels. -/
theorem not_isForestWord_of_even_support
    (G : FiniteMultiGraph) (seed : G.CycleSpace) (hseed : seed.1 ≠ 0)
    (x : G.EdgeWord) (hsub : ∀ e, seed.1 e ≠ 0 → x e ≠ 0) :
    ¬ G.IsForestWord x := by
  intro hx
  exact hseed (G.word_eq_zero_of_boundary_zero_of_forest seed.1 seed.2 (hx.mono hsub))

end Erdos1016.FiniteMultiGraph
