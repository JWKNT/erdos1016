import Erdos1016.Cycles.Geometry.RetainedCycleLinkBounds
import Erdos1016.Probability.Moments.PairLinkCount

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph.InducedSimpleRealization
open ExteriorComponents
local instance actualCycleLinkBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : FiniteMultiGraph)

/-- Injective vertex relabeling preserves disjointness of cycle supports. -/
theorem cycleRegion_disjoint_iff (R : Finset G.Vertex)
    (hloop : ∀ e ∈ G.internalEdges R, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges R, ∀ f ∈ G.internalEdges R,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (C C' : (graph G R hloop hsimple).CycleWord) :
    Disjoint (cycleRegion G R hloop hsimple C) (cycleRegion G R hloop hsimple C') ↔
      Disjoint (BoundaryDecay.Cycle.vertices C) (BoundaryDecay.Cycle.vertices C') := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact Finset.disjoint_left.mp h
      ((mem_cycleRegion_vertex G R hloop hsimple C v).mpr hv)
      ((mem_cycleRegion_vertex G R hloop hsimple C' v).mpr hv')
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    obtain ⟨u', hu', hu'v⟩ := Finset.mem_image.mp hv'
    have he : u = u' := vertex_injective G R hloop hsimple (huv.trans hu'v.symm)
    exact Finset.disjoint_left.mp h hu (he.symm ▸ hu')

/-- The actual link cardinal in the exact normalized cycle-pair law is
bounded by marked components, large cuts, small cyclic components, and the
constructed short joining paths. All geometry is derived from the packed
multigraph and its literal retained graph. -/
theorem actual_cycle_links_le
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
    (hG : G.toSimpleGraph.Connected) (ε : ℝ) (hε : 0 < ε)
    (hforest : (1 / 2 : ℝ) + ε < G.regionForestProbability Pᶜ) :
    (Nat.card (SeedPairCorrelation.Links G
      (cycleRegion G _ hloop hsimple C) (cycleRegion G _ hloop hsimple C')) : ℝ) ≤
      (Fintype.card (Component G P) : ℝ) + 2 * L / (t + 1) +
      ((t : ℝ) + 1) * (2 : ℝ) ^ t / (2 * ε) + 578 * ((L : ℝ) / D) ^ 2 := by
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
  have hgeometry := cycle_direct_and_exterior_links_real_le G P F D t L hloop hsimple
    C C' hdisjoint S hmax hcubic hF hhit hD hDL ht hbudget hL hL' hG ε hε hforest ha hb
  have hlink := SeedPairCorrelation.links_card_le_direct_add_exterior G A B hd
  have hlinkreal : (Nat.card (SeedPairCorrelation.Links G A B) : ℝ) ≤
      ((G.directLabels A B).card : ℝ) + (S.card : ℝ) := by exact_mod_cast hlink
  exact hlinkreal.trans hgeometry

end Erdos1016.FiniteMultiGraph.InducedSimpleRealization
