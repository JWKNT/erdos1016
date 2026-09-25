import Erdos1016.CycleSpace.Support.ActiveComponents
import Erdos1016.Probability.Conditional.ComponentProductLaw

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ActivePhysicalComponents

open Erdos1016

/-- Active-subgraph edges outside a prescribed host edge set. -/
def activeComplementEdges (G : PhysicalGraph) (E : Finset G.Edge) :
    Finset (activeSubgraph G).Edge := by
  classical
  exact Finset.univ.filter fun e =>
    (G.restrictedEdgeEquiv (activeEdges G) e).1 ∉ E

/-- Restrict a component word further to its selected outside edges. -/
def componentOutsideWord (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (c : ActiveComponent G)
    (y : (activeSubgraph G).RestrictedWord (componentEdges G c)) :
    (activeSubgraph G).RestrictedWord (componentPart G F c) :=
  fun e => y ⟨e.1, (mem_componentEdges_iff G c e.1).2
    ((mem_componentPart_iff G F c e.1).1 e.2).2⟩

/-- The outside-linear-forest event on the active cycle space. -/
def activeOutsideForest (G : PhysicalGraph) (E : Finset G.Edge)
    (x : (activeSubgraph G).CycleSpace) : Prop :=
  (activeSubgraph G).IsRestrictedLinearForest (activeComplementEdges G E)
    ((activeSubgraph G).restrictWord (activeComplementEdges G E) x.1)

/-- The corresponding component event on its restricted cycle-space factor. -/
def activeComponentOutsideForest (G : PhysicalGraph) (E : Finset G.Edge)
    (c : ActiveComponent G)
    (y : (activeSubgraph G).RestrictedCycleSpace (componentEdges G c)) : Prop :=
  (activeSubgraph G).IsRestrictedLinearForest
    (componentPart G (activeComplementEdges G E) c)
    (componentOutsideWord G (activeComplementEdges G E) c y.1)

theorem componentOutsideWord_of_global (G : PhysicalGraph)
    (F : Finset (activeSubgraph G).Edge) (x : (activeSubgraph G).Word)
    (c : ActiveComponent G) :
    componentOutsideWord G F c (edgeWordProductEquiv G x c) =
      (activeSubgraph G).restrictWord (componentPart G F c) x := by
  funext e
  simp [componentOutsideWord, edgeWordProductEquiv_apply,
    edgeSigmaEquiv, PhysicalGraph.restrictWord]

theorem activeOutsideForest_iff_components (G : PhysicalGraph)
    (E : Finset G.Edge) (x : (activeSubgraph G).CycleSpace) :
    activeOutsideForest G E x ↔
      ∀ c : ActiveComponent G,
        activeComponentOutsideForest G E c
          (restrictedCycleSpaceProductEquiv G x c) := by
  unfold activeOutsideForest activeComponentOutsideForest
  rw [isRestrictedLinearForest_iff_components]
  constructor
  · intro h c
    have hc := h c
    simpa [componentOutsideWord_of_global] using hc
  · intro h c
    have hc := h c
    simpa [componentOutsideWord_of_global] using hc

theorem activeOutsideForest_density_eq_prod (G : PhysicalGraph)
    (E : Finset G.Edge) :
    Erdos1016.Proof.ActiveComponentProbability.density
        (activeOutsideForest G E) =
      ∏ c : ActiveComponent G,
        Erdos1016.Proof.ActiveComponentProbability.density
          (activeComponentOutsideForest G E c) := by
  classical
  exact Erdos1016.Proof.ActiveComponentProbability.density_eq_prod_of_equiv
    (α := fun c => (activeSubgraph G).RestrictedCycleSpace (componentEdges G c))
    (inst := fun c => inferInstance)
    (e := restrictedCycleSpaceProductEquiv G)
    (P := activeOutsideForest G E)
    (Q := activeComponentOutsideForest G E)
    (hP := activeOutsideForest_iff_components G E)

end Erdos1016.Proof.ActivePhysicalComponents

end
