import Erdos1016.Graph.CutPacking
import Erdos1016.Nonbacktracking.Walks.CycleWords
import Erdos1016.CycleSpace.SupportedCycleKernel

set_option autoImplicit false

/-!
# A cycle in a cyclic induced region has internal physical support

The paper's “cyclic region” is defined by a cycle in the induced simple graph.
This module carries that cycle back to a cycle word on the original physical
edge labels, proving that every supporting physical edge is internal.
-/

noncomputable section

namespace Erdos1016.Proof.ManyRegionsCyclicSupport

open Erdos1016
open Erdos1016.Nonbacktracking
open Erdos1016.BoundaryDecay

local instance cyclicSupportDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Any region whose induced simple graph is cyclic contains a host
`CycleWord` supported on its internal physical edges. -/
theorem exists_cycleWord_supported_on_internalEdges
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hcyclic : ¬ (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsAcyclic) :
    ∃ C : G.CycleWord, ∀ e, C.1 e ≠ 0 →
      e ∈ Erdos1016.SafeCore.internalEdges G U := by
  classical
  let H := G.toSimpleGraph.induce (↑U : Set G.Vertex)
  have hcycle : ∃ v : (↑U : Set G.Vertex),
      ∃ p : H.Walk v v, p.IsCycle := by
    by_contra hn
    apply hcyclic
    intro v p hp
    exact hn ⟨v, p, hp⟩
  obtain ⟨v, p, hp⟩ := hcycle
  let incl : H →g G.toSimpleGraph :=
    { toFun := fun z => z.1
      map_rel' := by intro a b hab; exact hab }
  let q := p.map incl
  have hq : q.IsCycle :=
    (SimpleGraph.Walk.map_isCycle_iff_of_injective Subtype.val_injective).2 hp
  let C : G.CycleWord := cycleWordOfWalk G q hq
  have hvertices : G.usedVertices C.1 ⊆ U := by
    intro w hw
    have hvs : w ∈ q.support :=
      (used_walkWord_iff G q hq w).1 (by
        simpa [C, cycleWordOfWalk] using hw)
    have hvs' : ∃ a : U, a ∈ p.support ∧ incl a = w := by
      simpa only [q, SimpleGraph.Walk.support_map, List.mem_map] using hvs
    obtain ⟨a, _, ha⟩ := hvs'
    have : a.1 = w := ha
    simpa [← this] using a.2
  refine ⟨C, ?_⟩
  intro e he
  have hsrc : G.src e ∈ U := by
    apply hvertices
    exact src_mem_used_of_ne_zero C.1 e he
  have hdst : G.dst e ∈ U := by
    apply hvertices
    exact dst_mem_used_of_ne_zero C.1 e he
  simpa [Erdos1016.SafeCore.internalEdges] using And.intro hsrc hdst

/-- Project spelling of cyclic regions includes connectedness; the support
conclusion only needs the cyclicity conjunct. -/
theorem exists_cycleWord_supported_on_internalEdges_of_IsCyclicRegion
    (G : PhysicalGraph) (U : Finset G.Vertex)
    (hregion : G.IsCyclicRegion U) :
    ∃ C : G.CycleWord, ∀ e, C.1 e ≠ 0 →
      e ∈ Erdos1016.SafeCore.internalEdges G U :=
  exists_cycleWord_supported_on_internalEdges G U hregion.2







end Erdos1016.Proof.ManyRegionsCyclicSupport
