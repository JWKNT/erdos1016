import Erdos1016.Graph.Multigraph.InducedCycleSeeds
import Erdos1016.Cycles.Selection.ShortRegionPacking

set_option autoImplicit false
noncomputable section
namespace Erdos1016.FiniteMultiGraph
open InducedSimpleRealization
open BoundaryDecay
local instance retainedHighGirthDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Any sufficiently short actual cycle of the retained physical graph
would itself be an eligible short cyclic region in the original multigraph. -/
theorem retained_cycle_shortCyclicRegion (G : FiniteMultiGraph)
    (P S : Finset G.Vertex) (D : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (hmax : ∀ v, G.degree v ≤ 3)
    (C : (graph G (P ∪ S)ᶜ hloop hsimple).CycleWord)
    (hlen : BoundaryDecay.Cycle.length C ≤ D) :
    G.ShortCyclicRegion P D (cycleRegion G (P ∪ S)ᶜ hloop hsimple C) := by
  refine ⟨?_, ?_, cycleRegion_connected G _ hloop hsimple C,
    ⟨cycleSeed G _ hloop hsimple C, cycleSeed_nonzero G _ hloop hsimple C⟩, ?_⟩
  · intro v hv
    have h := cycleRegion_subset G _ hloop hsimple C hv
    simp only [Finset.mem_compl, Finset.mem_union, not_or] at h
    exact Finset.mem_compl.mpr h.1
  · rwa [cycleRegion_card]
  · apply le_trans (G.cutEdges_card_le_of_two_regular _ _
      (cycleSeed_degree G _ hloop hsimple C) (cycleSeed G _ hloop hsimple C).2
      (fun v _ => hmax v))
    rwa [cycleRegion_card]

/-- Maximal short-region packing forces the literal retained graph to have
no ordinary cycle of length at most D. The same packing already supplies
its looplessness and simplicity. -/
theorem retained_girth (G : FiniteMultiGraph)
    (P S : Finset G.Vertex) (D : ℕ)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hhit : ∀ U, G.ShortCyclicRegion P D U → (S ∩ U).Nonempty) :
    Erdos1016.Nonbacktracking.ShortWalks.GirthGreater
      (graph G (P ∪ S)ᶜ hloop hsimple).toSimpleGraph D := by
  intro u p hp
  by_contra hn
  have hlen : p.length ≤ D := by omega
  let C := Erdos1016.Nonbacktracking.cycleWordOfWalk _ p hp
  have hC : BoundaryDecay.Cycle.length C ≤ D := by
    simpa only [C, Erdos1016.Nonbacktracking.cycleWordOfWalk_length] using hlen
  obtain ⟨v, hv⟩ := hhit _ (G.retained_cycle_shortCyclicRegion P S D hloop hsimple hmax C hC)
  have h := Finset.mem_inter.mp hv
  have hr := cycleRegion_subset G _ hloop hsimple C h.2
  have hn : v ∉ P ∧ v ∉ S := by simpa only [Finset.mem_compl, Finset.mem_union, not_or] using hr
  have hs : v ∉ S := hn.2
  exact hs h.1

end Erdos1016.FiniteMultiGraph
