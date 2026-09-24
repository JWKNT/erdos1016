import Erdos1016.Extremal.SimpleGraphRealization
import Erdos1016.Nonbacktracking.Walks.CycleWords

set_option autoImplicit false

/-!
# Bridge the community pancyclic statement to the physical-graph formulation

The walk-to-cycle-word conversion is supplied by `CycleWalkAdapter`; this file
uses it to transfer pancyclicity, including the Hamiltonian cycle that ensures
the resulting physical graph is connected.
-/

noncomputable section
namespace Erdos1016.Problem1016

open Erdos1016

private def communityGraphToPhysicalGraphHom {n : ℕ}
    (G : SimpleGraph (Fin n)) : G →g (physicalOfSimpleGraph G).toSimpleGraph where
  toFun := id
  map_rel' := by
    intro u v huv
    simpa only [physicalOfSimpleGraph_toSimpleGraph] using huv

private theorem communityGraphToPhysicalGraphHom_injective {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    Function.Injective (communityGraphToPhysicalGraphHom G) := by
  intro u v h
  exact h

private theorem physicalGraph_connected_of_community_pancyclic
    {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 3 ≤ n)
    (hpan : IsPancyclic G) : (physicalOfSimpleGraph G).IsConnected := by
  let H := physicalOfSimpleGraph G
  obtain ⟨v, p, hp, hlen⟩ := hpan n hn (by simp)
  let pH : H.toSimpleGraph.Walk v v := p.map (communityGraphToPhysicalGraphHom G)
  have hpH : pH.IsCycle := by
    apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
      (communityGraphToPhysicalGraphHom_injective G)).2
    exact hp
  have hlenH : pH.length = n := by
    change (p.map (communityGraphToPhysicalGraphHom G)).length = n
    rw [SimpleGraph.Walk.length_map]
    exact hlen
  let C : H.CycleWord := Nonbacktracking.cycleWordOfWalk H pH hpH
  have hlenC : BoundaryDecay.Cycle.length C = n := by
    dsimp [C]
    rw [Nonbacktracking.cycleWordOfWalk_length]
    exact hlenH
  have hcard : (H.usedVertices C.1).card = Fintype.card H.Vertex := by
    calc
      (H.usedVertices C.1).card = BoundaryDecay.Cycle.length C := by
        symm
        exact BoundaryDecay.Cycle.length_eq_vertices_card C
      _ = Fintype.card H.Vertex := by
        simpa [H, physicalOfSimpleGraph] using hlenC
  have hfull : H.usedVertices C.1 = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp hcard
  rcases C.2 with ⟨_, _, hselInd, _⟩
  have hsel : (H.selectedGraph C.1).Connected := by
    rw [hfull] at hselInd
    rw [Finset.coe_univ] at hselInd
    exact (SimpleGraph.induceUnivIso _).connected_iff.mp hselInd
  have hsub : H.selectedGraph C.1 ≤ H.toSimpleGraph := by
    intro a b hab
    obtain ⟨e, he, hab⟩ := hab
    refine ⟨e, one_ne_zero, hab⟩
  change H.toSimpleGraph.Connected
  exact SimpleGraph.Connected.mono hsub hsel

/-- Every community-standard pancyclic graph on `Fin n` gives a pancyclic
physical graph with the same vertex/edge counts and corresponding cycle lengths.
The connectedness field of the physical formulation follows from the length-n
cycle in the community statement. -/
theorem final_isPancyclic_of_isPancyclic
    {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 3 ≤ n)
    (hpan : IsPancyclic G) : Extremal.IsPancyclic (physicalOfSimpleGraph G) := by
  let H := physicalOfSimpleGraph G
  have hcoverage : H.IsPancyclic := by
    change H.InitialCoverage H.vertexCount
    rw [physicalOfSimpleGraph_vertexCount]
    intro ℓ hℓ
    rcases Finset.mem_Icc.mp hℓ with ⟨hℓ3, hℓn⟩
    obtain ⟨v, p, hp, hlen⟩ := hpan ℓ hℓ3 (by simpa using hℓn)
    let pH : H.toSimpleGraph.Walk v v := p.map (communityGraphToPhysicalGraphHom G)
    have hpH : pH.IsCycle := by
      apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
        (communityGraphToPhysicalGraphHom_injective G)).2
      exact hp
    have hlenH : pH.length = ℓ := by
      change (p.map (communityGraphToPhysicalGraphHom G)).length = ℓ
      rw [SimpleGraph.Walk.length_map]
      exact hlen
    let C : H.CycleWord := Nonbacktracking.cycleWordOfWalk H pH hpH
    have hlenC : BoundaryDecay.Cycle.length C = ℓ := by
      dsimp [C]
      rw [Nonbacktracking.cycleWordOfWalk_length]
      exact hlenH
    change ℓ ∈ H.cycleLengths
    unfold PhysicalGraph.cycleLengths
    apply Finset.mem_image.mpr
    refine ⟨C, Finset.mem_univ C, ?_⟩
    simpa [BoundaryDecay.Cycle.length] using hlenC
  refine ⟨physicalGraph_connected_of_community_pancyclic G hn hpan, hn, ?_⟩
  simpa [H] using hcoverage

end Erdos1016.Problem1016
