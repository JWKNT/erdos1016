import Erdos1016.Cycles.Geometry.ActualCycleLinkBound
import Erdos1016.PolynomialBound.ParallelLinks

set_option autoImplicit false

/-!
# The link count of two retained cycles, without a forest excess

This is the link bound of the forest estimate with one change. The number of
small cyclic link components is bounded by `2 ^ (t + 1)`, from
`ParallelLinks.smallCyclicPart_card_le`. The hypothesis is only that the
forest probability exceeds one half. The earlier bound contained the term
`(t + 1) 2 ^ t / (2 ε)` for a forest excess `ε`.
-/

noncomputable section
namespace Erdos1016.PolynomialBound.LinkBound

open FiniteMultiGraph FiniteMultiGraph.InducedSimpleRealization
open FiniteMultiGraph.ExteriorComponents

local instance linkBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

/-- The actual link cardinal of two disjoint retained cycles of length at
most `L` is bounded by the marked components, the large cuts, `2 ^ (t + 1)`
small cyclic components, and the short joining paths. -/
theorem cycle_links_le
    (P : Finset G.Vertex) (F : Finset (Finset G.Vertex)) (D t L : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ∀ f ∈ G.internalEdges (P ∪ F.biUnion id)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (C C' : (graph G (P ∪ F.biUnion id)ᶜ hloop hsimple).CycleWord)
    (hdisjoint : Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C'))
    (hmax : ∀ v, G.degree v ≤ 3) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (hF : ∀ A ∈ F, G.ShortCyclicRegion P D A)
    (hhit : ∀ A, G.ShortCyclicRegion P D A → (F.biUnion id ∩ A).Nonempty)
    (hD : 8 ≤ D) (hDL : D ≤ L) (ht : 1 ≤ t)
    (hbudget : 2 * (t + 2 * (D / 8)) ≤ D)
    (hL : BoundaryDecay.Cycle.length C ≤ L) (hL' : BoundaryDecay.Cycle.length C' ≤ L)
    (hG : G.toSimpleGraph.Connected)
    (hforest : (1 / 2 : ℝ) < G.regionForestProbability Pᶜ) :
    (Nat.card (SeedPairCorrelation.Links G
      (cycleRegion G _ hloop hsimple C) (cycleRegion G _ hloop hsimple C')) : ℝ) ≤
      (Fintype.card (Component G P) : ℝ) + 2 * L / (t + 1) +
      (2 : ℝ) ^ (t + 1) + 578 * ((L : ℝ) / D) ^ 2 := by
  let A := cycleRegion G _ hloop hsimple C
  let B := cycleRegion G _ hloop hsimple C'
  let S := SeedPairCorrelation.exteriorLinks G A B
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    obtain ⟨u', hu', hu'v⟩ := Finset.mem_image.mp hv'
    have he : u = u' := vertex_injective G _ hloop hsimple (huv.trans hu'v.symm)
    exact Finset.disjoint_left.mp hdisjoint hu (he.symm ▸ hu')
  have ha (c) (hc : c ∈ S) : ∃ u ∈ A, ∃ x ∈ vertices G (A ∪ B)ᶜ c,
      G.toSimpleGraph.Adj u x := (Finset.mem_filter.mp hc).2.1
  have hb (c) (hc : c ∈ S) : ∃ v ∈ B, ∃ y ∈ vertices G (A ∪ B)ᶜ c,
      G.toSimpleGraph.Adj y v := by
    obtain ⟨v, hv, y, hy, hvy⟩ := (Finset.mem_filter.mp hc).2.2
    exact ⟨v, hv, y, hy, hvy.symm⟩
  have hq : 0 < D / 8 := by omega
  have hn := cycle_direct_and_exterior_links_le G P F D t (D / 8) hloop hsimple
    C C' hdisjoint S hmax hcubic hF hhit hq ht hbudget ha hb
  let U := (cycleRegion G _ hloop hsimple C ∪ cycleRegion G _ hloop hsimple C')ᶜ
  have hcyc : ((smallCyclicPart G U P t S).card : ℝ) ≤ (2 : ℝ) ^ (t + 1) := by
    have h := ParallelLinks.smallCyclicPart_card_le G A B hG
      (cycleRegion_connected G _ hloop hsimple C)
      (cycleRegion_connected G _ hloop hsimple C') P t S
      (fun c hc => (Finset.mem_filter.mp hc).2) hforest
    exact_mod_cast h
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
  have hlink := SeedPairCorrelation.links_card_le_direct_add_exterior G A B hd
  have hlinkreal : (Nat.card (SeedPairCorrelation.Links G A B) : ℝ) ≤
      ((G.directLabels A B).card : ℝ) + (S.card : ℝ) := by exact_mod_cast hlink
  linarith

end Erdos1016.PolynomialBound.LinkBound
