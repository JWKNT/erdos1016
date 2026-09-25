import Erdos1016.Probability.Conditional.ActiveForestProduct
import Erdos1016.CycleSpace.Support.ComponentMinimumDegree
import Erdos1016.Cleanup.Support.VertexSupportedWitness
import Erdos1016.CycleSpace.Support.ComponentRanks
import Erdos1016.CycleSpace.EvenForestZero

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016
open Erdos1016.Proof.VertexSupportedWitness

/-- When a component has no witness-support edge, the outside edge set on
that component is the entire component edge set. -/
theorem componentPart_eq_all_of_no_support (G : PhysicalGraph)
    (E : Finset G.Edge) (c : ActiveComponent G)
    (hmiss : ∀ e ∈ componentEdges G c,
      (G.restrictedEdgeEquiv (activeEdges G) e).1 ∉ E) :
    componentPart G (activeComplementEdges G E) c = componentEdges G c := by
  classical
  ext e
  rw [mem_componentPart_iff, mem_componentEdges_iff]
  constructor
  · exact fun h => h.2
  · intro he
    constructor
    · have he' : e ∈ componentEdges G c := by
        rw [mem_componentEdges_iff]
        exact he
      simp [activeComplementEdges, hmiss e he']
    · exact he

/-- If the outside restriction is the entire edge set of a component, only
the zero component-cycle state can pass the forest event. -/
theorem componentOutsideForest_eq_zero_of_all_edges
    (G : PhysicalGraph) (E : Finset G.Edge) (c : ActiveComponent G)
    (hfull : componentPart G (activeComplementEdges G E) c = componentEdges G c)
    (y : (activeSubgraph G).RestrictedCycleSpace (componentEdges G c))
    (hy : activeComponentOutsideForest G E c y) : y = 0 := by
  classical
  let H := activeSubgraph G
  let S := componentEdges G c
  let Q := componentPart G (activeComplementEdges G E) c
  let w := componentOutsideWord G (activeComplementEdges G E) c y.1
  have hmem (e : (activeSubgraph G).Edge) : e ∈ Q ↔ e ∈ S := by
    change e ∈ componentPart G (activeComplementEdges G E) c ↔
      e ∈ componentEdges G c
    rw [hfull]
  have hgraph : H.restrictedSelectedGraph Q w = H.restrictedSelectedGraph S y.1 := by
    ext u v
    constructor
    · rintro ⟨e, hx, hend⟩
      refine ⟨⟨e.1, (hmem e.1).mp e.2⟩, ?_, hend⟩
      simpa [w, componentOutsideWord] using hx
    · rintro ⟨e, hx, hend⟩
      refine ⟨⟨e.1, (hmem e.1).mpr e.2⟩, ?_, hend⟩
      simpa [w, componentOutsideWord] using hx
  have hac : (H.restrictedSelectedGraph S y.1).IsAcyclic := by
    rw [← hgraph]
    exact hy.1
  have hzero := Erdos1016.Proof.CycleSpaceForestZero.restrictedWord_eq_zero_of_boundary_zero_of_acyclic
    H S y.1 y.2 hac
  exact Subtype.ext hzero

/-- A component forest event on the full component edge set has density at
most one half whenever its cycle space is nontrivial. -/
theorem componentOutsideForest_density_le_half_of_all_edges
    (G : PhysicalGraph) (E : Finset G.Edge) (c : ActiveComponent G)
    (hfull : componentPart G (activeComplementEdges G E) c = componentEdges G c)
    (hnontrivial : ∃ y : (activeSubgraph G).RestrictedCycleSpace (componentEdges G c),
      y ≠ 0) :
    Erdos1016.Proof.ActiveComponentProbability.density
      (activeComponentOutsideForest G E c) ≤ (1 / 2 : ℝ) := by
  classical
  let α := (activeSubgraph G).RestrictedCycleSpace (componentEdges G c)
  let P : α → Prop := activeComponentOutsideForest G E c
  let S := Finset.univ.filter P
  have hsubset : S ⊆ ({0} : Finset α) := by
    intro y hy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp [componentOutsideForest_eq_zero_of_all_edges G E c hfull y hy]
  have hnum : Fintype.card {y : α // P y} ≤ 1 := by
    let f : {y : α // P y} ≃ {y : α // y ∈ S} := {
      toFun := fun y => ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩⟩
      invFun := fun y => ⟨y.1, (Finset.mem_filter.mp y.2).2⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
    calc
      Fintype.card {y : α // P y} = Fintype.card {y : α // y ∈ S} :=
        Fintype.card_congr f
      _ = S.card := Fintype.card_coe S
      _ ≤ ({0} : Finset α).card := Finset.card_le_card hsubset
      _ = 1 := by simp
  obtain ⟨z, hz⟩ := hnontrivial
  have hdenNat : 2 ≤ Fintype.card α := by
    have hp : ({0, z} : Finset α).card = 2 := by
      have hz0 : (0 : α) ≠ z := Ne.symm hz
      simp [Finset.card_pair, hz0]
    calc
      2 = ({0, z} : Finset α).card := hp.symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card α := by simp
  have hnumR : (Fintype.card {y : α // P y} : ℝ) ≤ 1 := by exact_mod_cast hnum
  have hdenR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hdenNat
  have hdenpos : (0 : ℝ) < Fintype.card α := by positivity
  unfold Erdos1016.Proof.ActiveComponentProbability.density
  change (Fintype.card {y : α // P y} : ℝ) / Fintype.card α ≤ 1 / 2
  apply (div_le_iff₀ hdenpos).2
  nlinarith

theorem exists_nonzero_cycle_in_activeComponent (G : PhysicalGraph)
    (c : ActiveComponent G) (hne : (componentEdges G c).Nonempty) :
    ∃ y : (activeSubgraph G).RestrictedCycleSpace (componentEdges G c), y ≠ 0 := by
  classical
  obtain ⟨e, he⟩ := hne
  have hactive := ActiveComponentMinimumDegree.activeSubgraph_edge_active G e
  obtain ⟨x, hx⟩ := hactive
  let y := restrictedCycleSpaceProductEquiv G x c
  refine ⟨y, ?_⟩
  intro hy
  have hcomponent : edgeComponent G e = c :=
    (mem_componentEdges_iff G c e).1 he
  have hsigma :
      (edgeSigmaEquiv G).symm ⟨c, ⟨e, he⟩⟩ = e := by
    have hpair :
        (⟨c, ⟨e, he⟩⟩ : Σ d : ActiveComponent G,
          (activeSubgraph G).RestrictedEdge (componentEdges G d)) =
        edgeSigmaEquiv G e := by
      apply Sigma.ext
      · exact hcomponent.symm
      · cases hcomponent
        rfl
    rw [hpair]
    exact Equiv.symm_apply_apply (edgeSigmaEquiv G) e
  have hcoord : y.1 ⟨e, he⟩ = x.1 e := by
    change edgeWordProductEquiv G x.1 c ⟨e, he⟩ = x.1 e
    rw [edgeWordProductEquiv_apply, hsigma]
  have hzero : y.1 ⟨e, he⟩ = 0 := by
    rw [hy]
    rfl
  rw [hcoord] at hzero
  rw [hx] at hzero
  exact one_ne_zero hzero

/-- Under the paper's `> 1/2` outside-forest hypothesis, every edge-bearing
active component contains an edge whose original label lies in the witness set. -/
theorem every_nonempty_activeComponent_meets_witness
    (G : PhysicalGraph) (E : Finset G.Edge)
    (hprob : (1 / 2 : ℝ) < G.outsideLinearForestProbability E)
    (c : ActiveComponent G) (hne : (componentEdges G c).Nonempty) :
    ∃ e ∈ componentEdges G c,
      (G.restrictedEdgeEquiv (activeEdges G) e).1 ∈ E := by
  classical
  by_contra h
  have hmiss : ∀ e ∈ componentEdges G c,
      (G.restrictedEdgeEquiv (activeEdges G) e).1 ∉ E := by
    intro e he hin
    exact h ⟨e, he, hin⟩
  have hfull := componentPart_eq_all_of_no_support G E c hmiss
  have hle := componentOutsideForest_density_le_half_of_all_edges G E c hfull
    (exists_nonzero_cycle_in_activeComponent G c hne)
  have hgt := ActiveOutsideProbabilityBridge.componentDensity_gt_half_of_hostProbability_gt_half
    G E hprob c
  linarith











abbrev EdgeBearingActiveComponents (G : PhysicalGraph) :=
  {c : ActiveComponent G // (componentEdges G c).Nonempty}

noncomputable instance edgeBearingActiveComponentsFintype (G : PhysicalGraph) :
    Fintype (EdgeBearingActiveComponents G) := Fintype.ofFinite _

abbrev TrimmedWitnessComponents (G : PhysicalGraph) (F : Finset G.CycleWord) :=
  (trimmedWitnessGraph G F).toSimpleGraph.ConnectedComponent

noncomputable instance trimmedWitnessComponentsFintype (G : PhysicalGraph)
    (F : Finset G.CycleWord) : Fintype (TrimmedWitnessComponents G F) :=
  Fintype.ofFinite _





end Erdos1016.Proof.ActivePhysicalComponents

end
