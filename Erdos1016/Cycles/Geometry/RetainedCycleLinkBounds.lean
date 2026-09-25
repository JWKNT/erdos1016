import Erdos1016.Cycles.Geometry.RetainedExteriorLinks
import Erdos1016.Cycles.Geometry.RetainedDirectEdges
import Erdos1016.Cycles.Geometry.CycleWalkExistence
import Erdos1016.Cycles.Selection.RetainedHighGirth
import Erdos1016.Probability.Avoidance.ExteriorCyclicCount
import Erdos1016.Graph.Multigraph.RegionBoundaryUnion
import Erdos1016.Graph.Multigraph.InducedDeletionBounds

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
open ExteriorComponents
open Erdos1016.Nonbacktracking
local instance retainedCycleLinkBoundsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (R : Finset G.Vertex)
  (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
  (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
    ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
      (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)

private theorem walkRegion_cycleWord {v : (graph G R hloop hsimple).Vertex}
    (p : (graph G R hloop hsimple).toSimpleGraph.Walk v v) (hp : p.IsCycle) :
    walkRegion G R hloop hsimple p =
      cycleRegion G R hloop hsimple (cycleWordOfWalk _ p hp) := by
  unfold walkRegion cycleRegion
  congr 1
  ext w
  simp only [List.mem_toFinset]
  exact (used_walkWord_iff _ p hp w).symm

private theorem vertices_cycleWord {v : (graph G R hloop hsimple).Vertex}
    (p : (graph G R hloop hsimple).toSimpleGraph.Walk v v) (hp : p.IsCycle)
    (w : (graph G R hloop hsimple).Vertex) :
    w ∈ BoundaryDecay.Cycle.vertices (cycleWordOfWalk _ p hp) ↔ w ∈ p.support :=
  used_walkWord_iff _ p hp w

omit R hloop hsimple in
/-- Counts all original physical links between two retained cycles: direct
labels and any chosen family of doubly attached exterior components. Only
the actual small-cyclic component cardinal is left in the finite formula. -/
theorem cycle_direct_and_exterior_links_le
    (P : Finset G.Vertex) (F : Finset (Finset G.Vertex)) (D t q : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (C C' : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).CycleWord)
    (hdisjoint : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C'))
    (S : Finset (Component G
      (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ))
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (hF : ∀ A ∈ F, G.ShortCyclicRegion P D A)
    (hhit : ∀ A, G.ShortCyclicRegion P D A → (F.biUnion id ∩ A).Nonempty)
    (hq : 0 < q) (ht : 1 ≤ t) (hbudget : 2 * (t + 2 * q) ≤ D)
    (hattachC : ∀ c ∈ S, ∃ u ∈ cycleRegion G _ hloop hsimple C,
      ∃ x ∈ vertices G _ c, G.toSimpleGraph.Adj u x)
    (hattachC' : ∀ c ∈ S, ∃ v ∈ cycleRegion G _ hloop hsimple C',
      ∃ y ∈ vertices G _ c, G.toSimpleGraph.Adj y v) :
    (G.directLabels (cycleRegion G _ hloop hsimple C) (cycleRegion G _ hloop hsimple C')).card + S.card ≤
      Fintype.card (Component G P) +
      (G.cutEdges (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ).card / (t + 1) +
      (smallCyclicPart G _ P t S).card +
      2 * ((BoundaryDecay.Cycle.length C / q + 1) * (BoundaryDecay.Cycle.length C' / q + 1)) := by
  obtain ⟨a, p, hp, heq⟩ := exists_cycle_walk_of_cycleWord _ C
  obtain ⟨b, p', hp', heq'⟩ := exists_cycle_walk_of_cycleWord _ C'
  have hv (v) : v ∈ BoundaryDecay.Cycle.vertices C ↔ v ∈ p.support := by
    rw [← heq]
    exact vertices_cycleWord G _ hloop hsimple p hp v
  have hv' (v) : v ∈ BoundaryDecay.Cycle.vertices C' ↔ v ∈ p'.support := by
    rw [← heq']
    exact vertices_cycleWord G _ hloop hsimple p' hp' v
  have hreg : walkRegion G _ hloop hsimple p = cycleRegion G _ hloop hsimple C := by
    rw [walkRegion_cycleWord, heq]
  have hreg' : walkRegion G _ hloop hsimple p' = cycleRegion G _ hloop hsimple C' := by
    rw [walkRegion_cycleWord, heq']
  have hlen : p.length = BoundaryDecay.Cycle.length C := by
    rw [← heq, cycleWordOfWalk_length]
  have hlen' : p'.length = BoundaryDecay.Cycle.length C' := by
    rw [← heq', cycleWordOfWalk_length]
  have hdis : Disjoint {v | v ∈ p.support} {v | v ∈ p'.support} := by
    apply Set.disjoint_left.mpr
    intro v h h'
    exact Finset.disjoint_left.mp hdisjoint ((hv v).mpr h) ((hv' v).mpr h')
  have hg := G.retained_girth P (F.biUnion id) D hloop hsimple hmax hhit
  let U := (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ
  have hregion (v) (hh : v ∈ cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C') :
      v ∈ (P ∪ F.biUnion id)ᶜ := by
    rcases Finset.mem_union.mp hh with hh | hh
    · exact cycleRegion_subset G _ hloop hsimple C hh
    · exact cycleRegion_subset G _ hloop hsimple C' hh
  have hPU : P ⊆ U := by
    intro v hv
    apply Finset.mem_compl.mpr
    intro hh
    exact (Finset.mem_compl.mp (hregion v hh)) (Finset.mem_union_left _ hv)
  have hFU : F.biUnion id ⊆ U := by
    intro v hv
    apply Finset.mem_compl.mpr
    intro hh
    exact (Finset.mem_compl.mp (hregion v hh)) (Finset.mem_union_right _ hv)
  have hCU (v) (hh : v ∈ p.support) : vertex G _ hloop hsimple v ∉ U := by
    apply fun h => Finset.mem_compl.mp h (Finset.mem_union_left _ ?_)
    exact (mem_cycleRegion_vertex G _ hloop hsimple C v).mpr ((hv v).mpr hh)
  have hC'U (v) (hh : v ∈ p'.support) : vertex G _ hloop hsimple v ∉ U := by
    apply fun h => Finset.mem_compl.mp h (Finset.mem_union_right _ ?_)
    exact (mem_cycleRegion_vertex G _ hloop hsimple C' v).mpr ((hv' v).mpr hh)
  have ha (c) (hc : c ∈ S) : ∃ u ∈ p.support, ∃ x ∈ vertices G U c,
      G.toSimpleGraph.Adj (vertex G _ hloop hsimple u) x := by
    obtain ⟨u, hu, x, hx, hux⟩ := hattachC c hc
    obtain ⟨v, hvC, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨v, (hv v).mp hvC, x, hx, hux⟩
  have ha' (c) (hc : c ∈ S) : ∃ v ∈ p'.support, ∃ y ∈ vertices G U c,
      G.toSimpleGraph.Adj y (vertex G _ hloop hsimple v) := by
    obtain ⟨v, hvC', y, hy, hyv⟩ := hattachC' c hc
    obtain ⟨u, huC', rfl⟩ := Finset.mem_image.mp hvC'
    exact ⟨u, (hv' u).mp huC', y, hy, hyv⟩
  have hext := exterior_links_le_marked_cut_cyclic_blocks G P U F D t q
    (smallCyclicPart G U P t S).card hloop hsimple S p p' hp hdis hmax hcubic
    hPU hFU hF hCU hC'U hq hg hbudget le_rfl ha ha'
  have hdirect := directLabels_card_le_length_blocks G _ hloop hsimple p p' hp hdis hmax D q hq hg
    (show 2 * (1 + 2 * q) ≤ D by omega)
  rw [hreg, hreg', hlen, hlen'] at hdirect
  rw [hlen, hlen'] at hext
  dsimp only [U] at hext
  omega

omit R hloop hsimple in
/-- The original physical-link count with the small-cyclic term discharged
by the actual forest probability. Constants include both direct labels and
small exterior trees; no correlation estimate is an input. -/
theorem cycle_direct_and_exterior_links_real_le
    (P : Finset G.Vertex) (F : Finset (Finset G.Vertex)) (D t L : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (C C' : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).CycleWord)
    (hdisjoint : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C'))
    (S : Finset (Component G
      (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ))
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (hF : ∀ A ∈ F, G.ShortCyclicRegion P D A)
    (hhit : ∀ A, G.ShortCyclicRegion P D A → (F.biUnion id ∩ A).Nonempty)
    (hD : 8 ≤ D) (hDL : D ≤ L) (ht : 1 ≤ t)
    (hbudget : 2 * (t + 2 * (D / 8)) ≤ D)
    (hL : BoundaryDecay.Cycle.length C ≤ L) (hL' : BoundaryDecay.Cycle.length C' ≤ L)
    (hG : G.toSimpleGraph.Connected) (ε : ℝ) (hε : 0 < ε)
    (hforest : (1 / 2 : ℝ) + ε < G.regionForestProbability Pᶜ)
    (hattachC : ∀ c ∈ S, ∃ u ∈ cycleRegion G _ hloop hsimple C,
      ∃ x ∈ vertices G _ c, G.toSimpleGraph.Adj u x)
    (hattachC' : ∀ c ∈ S, ∃ v ∈ cycleRegion G _ hloop hsimple C',
      ∃ y ∈ vertices G _ c, G.toSimpleGraph.Adj y v) :
    ((G.directLabels (cycleRegion G _ hloop hsimple C)
      (cycleRegion G _ hloop hsimple C')).card : ℝ) + (S.card : ℝ) ≤
      (Fintype.card (Component G P) : ℝ) + 2 * L / (t + 1) +
      ((t : ℝ) + 1) * (2 : ℝ) ^ t / (2 * ε) + 578 * ((L : ℝ) / D) ^ 2 := by
  have hq : 0 < D / 8 := by omega
  have hn := cycle_direct_and_exterior_links_le G P F D t (D / 8) hloop hsimple
    C C' hdisjoint S hmax hcubic hF hhit hq ht hbudget hattachC hattachC'
  let U := (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ
  have hcyc := smallCyclicPart_card_le G U P t S hG ε hε hforest
  have hcut : (G.cutEdges U).card ≤ 2 * L := by
    dsimp only [U]
    rw [G.cutEdges_compl]
    have h := G.cut_two_regular_union_card_le
      (cycleRegion G _ hloop hsimple C) (cycleRegion G _ hloop hsimple C')
      (cycleSeed G _ hloop hsimple C).1.1 (cycleSeed G _ hloop hsimple C').1.1
      (cycleSeed_degree G _ hloop hsimple C) (cycleSeed_degree G _ hloop hsimple C')
      (cycleSeed G _ hloop hsimple C).2 (cycleSeed G _ hloop hsimple C').2 hmax
    rw [cycleRegion_card, cycleRegion_card] at h
    omega
  have hdiv : ((G.cutEdges U).card / (t + 1) : ℕ) ≤
      (2 * L : ℕ) / (t + 1) := Nat.div_le_div_right hcut
  have hdivreal : (((G.cutEdges U).card / (t + 1) : ℕ) : ℝ) ≤
      2 * (L : ℝ) / ((t : ℝ) + 1) := by
    calc
      _ ≤ ((G.cutEdges U).card : ℝ) / ((t : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.cast_div_le (α := ℝ) (m := (G.cutEdges U).card) (n := t + 1))
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcut) (by positivity)
  have hblock := Erdos1016.Proof.ShortJoiningPaths.length_block_product_le_quadratic
    (BoundaryDecay.Cycle.length C) (BoundaryDecay.Cycle.length C') L D hD hL hL' hDL
  have hmain :
      ((G.directLabels (cycleRegion G _ hloop hsimple C)
        (cycleRegion G _ hloop hsimple C')).card : ℝ) + (S.card : ℝ) ≤
      (Fintype.card (Component G P) : ℝ) +
        (((G.cutEdges U).card / (t + 1) : ℕ) : ℝ) +
        ((smallCyclicPart G U P t S).card : ℝ) +
        2 * (((BoundaryDecay.Cycle.length C / (D / 8) + 1) *
          (BoundaryDecay.Cycle.length C' / (D / 8) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hn
  linarith

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
