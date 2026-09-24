import Erdos1016.Extremal.Capacity.WitnessSupport

set_option autoImplicit false

/-!
# Rank bounds for a finite short-cycle witness support

These statements use only a finite family containing a witness of each
required length. The competitive hypothesis needed for the paper's sharper
`rank < 5 R` screen is deliberately absent and not inferred here.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016
namespace PhysicalGraph

/-- A finite family contains a cycle word at each length in `[3,L]`. -/
def HasCycleWitnessFamily (G : PhysicalGraph) (F : Finset G.CycleWord)
    (L : ℕ) : Prop :=
  ∀ ℓ : ℕ, 3 ≤ ℓ → ℓ ≤ L →
    ∃ C : G.CycleWord, C ∈ F ∧ G.wordLength C.1 = ℓ

/-- The cycle rank of every physical graph is bounded by its number of edges.
This is the elementary subspace-dimension bound for the boundary kernel. -/
theorem cycleRank_le_edgeCount (G : PhysicalGraph) :
    G.cycleRank ≤ G.edgeCount := by
  let f : G.CycleSpace →ₗ[F₂] G.Word := Submodule.subtype G.CycleSpace
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext h
  have hdim : G.cycleRank ≤ Module.finrank F₂ G.Word := by
    exact LinearMap.finrank_le_finrank_of_injective hf
  have hword : Module.finrank F₂ G.Word = G.edgeCount := by
    change Module.finrank F₂ (G.Edge → F₂) = G.edgeCount
    simp [Fintype.card_fin]
  exact hdim.trans_eq hword





/-- The edge count of a literal union of witness supports is at most the sum
of the lengths of all cycles in the selected family. -/
theorem witnessSupport_edgeCount_le_sum_lengths (G : PhysicalGraph)
    (F : Finset G.CycleWord) :
    (witnessSupportGraph G F).edgeCount ≤
      ∑ C ∈ F, G.wordLength C.1 := by
  classical
  calc
    (witnessSupportGraph G F).edgeCount =
        (witnessSupportEdges G F).card := rfl
    _ ≤ ∑ C ∈ F, (G.edgeSupport C.1).card := Finset.card_biUnion_le
    _ = ∑ C ∈ F, G.wordLength C.1 := by simp [PhysicalGraph.wordLength]



end PhysicalGraph
end Erdos1016
