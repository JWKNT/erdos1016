import Erdos1016.Graph.ExteriorForestRegions
import Erdos1016.Cycles.Geometry.ExteriorTreePathCount

set_option autoImplicit false

/-! A disjoint exhaustive classification of actual exterior components.
Cyclicity is multigraph cyclicity, including loops and parallel pairs.
Marked and large-cut classes are bounded from graph data, leaving the
small cyclic family for the small-cut probability theorem and the small
forest family for the high-girth tree-path theorem. -/
noncomputable section
namespace Erdos1016.FiniteMultiGraph.ExteriorComponents
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (U P : Finset G.Vertex)

/-- A region is cyclic when its full internal labelled edge set is not a
multigraph forest. In particular loops and digons are classified as cyclic. -/
def Cyclic (c : Component G U) : Prop :=
  ¬G.IsForestWord (G.restrictEdges (G.internalEdges (vertices G U c)) (fun _ => 1))

def markedPart (S : Finset (Component G U)) : Finset (Component G U) :=
  S.filter (Touches G U P)

def largePart (t : ℕ) (S : Finset (Component G U)) : Finset (Component G U) :=
  S.filter (fun c => ¬Touches G U P c ∧ t < (G.cutEdges (vertices G U c)).card)

def smallCyclicPart (t : ℕ) (S : Finset (Component G U)) : Finset (Component G U) :=
  S.filter (fun c => ¬Touches G U P c ∧ (G.cutEdges (vertices G U c)).card ≤ t ∧ Cyclic G U c)

def smallForestPart (t : ℕ) (S : Finset (Component G U)) : Finset (Component G U) :=
  S.filter (fun c => ¬Touches G U P c ∧ (G.cutEdges (vertices G U c)).card ≤ t ∧ ¬Cyclic G U c)

/-- No exterior component is omitted or counted twice. -/
theorem card_partition (t : ℕ) (S : Finset (Component G U)) :
    S.card = (markedPart G U P S).card + (largePart G U P t S).card +
      (smallCyclicPart G U P t S).card + (smallForestPart G U P t S).card := by
  have h1 := Finset.filter_card_add_filter_neg_card_eq_card (s := S) (Touches G U P)
  have h2 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := S.filter (fun c => ¬Touches G U P c))
    (fun c => t < (G.cutEdges (vertices G U c)).card)
  have h3 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (S.filter (fun c => ¬Touches G U P c)).filter
      (fun c => ¬t < (G.cutEdges (vertices G U c)).card)) (Cyclic G U)
  simp only [Finset.filter_filter, not_lt] at h2 h3
  simp only [markedPart, largePart, smallCyclicPart, smallForestPart]
  simp only [and_assoc] at h3
  omega

/-- One marked induced component can enter only one exterior component. -/
theorem markedPart_card_le (hPU : P ⊆ U) (S : Finset (Component G U)) :
    (markedPart G U P S).card ≤ Fintype.card (Component G P) := by
  let f : markedPart G U P S → TouchedComponent G U P :=
    fun c => ⟨c.1, (Finset.mem_filter.mp c.2).2⟩
  have hinj : Function.Injective f := by
    intro c d h
    exact Subtype.ext (congrArg (fun x : TouchedComponent G U P => x.1) h)
  have hcard := Fintype.card_le_of_injective f hinj
  have hcard' : (markedPart G U P S).card ≤ Fintype.card (TouchedComponent G U P) := by
    simpa only [Fintype.card_coe] using hcard
  exact hcard'.trans (touched_component_card_le G U P hPU)

/-- Large components consume disjoint boundary-edge labels, giving the
finite integer version of the 2L/t bound. -/
theorem largePart_card_le (t : ℕ) (S : Finset (Component G U)) :
    (largePart G U P t S).card ≤ (G.cutEdges U).card / (t + 1) := by
  have hsub : largePart G U P t S ⊆ Finset.univ.filter
      (fun c : Component G U => t < (G.cutEdges (vertices G U c)).card) := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.2⟩
  apply (Nat.le_div_iff_mul_le (by omega : 0 < t + 1)).mpr
  exact (Nat.mul_le_mul_right (t + 1) (Finset.card_le_card hsub)).trans
    (large_cut_card_mul_le G U t)

/-- Deterministic link classification with the sole temporary cyclic-family
 bound K. The forest term is its actual finite family, ready for the
 constructed tree-path bound, not an abstract forest-count premise. -/
theorem card_le_marked_large_cyclic_forest (hPU : P ⊆ U)
    (t K : ℕ) (S : Finset (Component G U))
    (hcyclic : (smallCyclicPart G U P t S).card ≤ K) :
    S.card ≤ Fintype.card (Component G P) + (G.cutEdges U).card / (t + 1) + K +
      (smallForestPart G U P t S).card := by
  rw [card_partition G U P t S]
  have := markedPart_card_le G U P hPU S
  have := largePart_card_le G U P t S
  omega

/-- The forest class is an actual induced tree in the underlying graph.
Its connectedness comes from the component construction. -/
theorem smallForestPart_induced_tree (t : ℕ) (S : Finset (Component G U))
    (c : Component G U) (hc : c ∈ smallForestPart G U P t S) :
    (G.toSimpleGraph.induce (↑(vertices G U c) : Set G.Vertex)).IsTree := by
  have hforest : G.IsForestWord
      (G.restrictEdges (G.internalEdges (vertices G U c)) (fun _ => 1)) := by
    exact not_not.mp (Finset.mem_filter.mp hc).2.2.2
  exact ⟨vertices_connected G U c, internal_forest_induced_acyclic G _ hforest⟩

theorem smallForestPart_disjoint_marked (t : ℕ) (S : Finset (Component G U))
    (c : Component G U) (hc : c ∈ smallForestPart G U P t S) :
    Disjoint (vertices G U c) P := by
  apply Finset.disjoint_left.mpr
  intro x hxC hxP
  exact (Finset.mem_filter.mp hc).2.1 ⟨x, hxP, hxC⟩

/-- The deterministic exterior-link estimate after interpreting the forest
 regions in the actual high-girth graph J. The agreement hypothesis records
 the concrete deletion/embedding step; the tree count is proved internally
 by constructing paths and blocks. Only the small cyclic count K is supplied. -/
theorem card_le_marked_large_cyclic_blocks
    (hPU : P ⊆ U) (t K : ℕ) (S : Finset (Component G U))
    (hcyclic : (smallCyclicPart G U P t S).card ≤ K)
    (J : SimpleGraph G.Vertex) {a b : G.Vertex}
    (C : J.Walk a a) (C' : J.Walk b b) (hC : C.IsCycle)
    (hdisjoint : Disjoint {x | x ∈ C.support} {x | x ∈ C'.support})
    (hdegree : ∀ v ∈ C.support, J.degree v ≤ 3)
    (hUC : ∀ v ∈ U, v ∉ C.support) (hUC' : ∀ v ∈ U, v ∉ C'.support)
    (D q : ℕ) (hq : 0 < q) (hg : Nonbacktracking.ShortWalks.GirthGreater J D)
    (hbudget : 2 * (t + 2 * q) ≤ D)
    (hagree : ∀ c ∈ smallForestPart G U P t S,
      J.induce (↑(vertices G U c) : Set G.Vertex) =
        G.toSimpleGraph.induce (↑(vertices G U c) : Set G.Vertex))
    (hcubic : ∀ c ∈ smallForestPart G U P t S, ∀ v ∈ vertices G U c, J.degree v = 3)
    (hcut : ∀ c ∈ smallForestPart G U P t S,
      (∑ v ∈ vertices G U c, (J.neighborFinset v \ vertices G U c).card) ≤ t)
    (hattachC : ∀ c ∈ smallForestPart G U P t S,
      ∃ u ∈ C.support, ∃ x ∈ vertices G U c, J.Adj u x)
    (hattachC' : ∀ c ∈ smallForestPart G U P t S,
      ∃ v ∈ C'.support, ∃ y ∈ vertices G U c, J.Adj y v) :
    S.card ≤ Fintype.card (Component G P) + (G.cutEdges U).card / (t + 1) + K +
      (C.length / q + 1) * (C'.length / q + 1) := by
  let I := {c // c ∈ smallForestPart G U P t S}
  have hFdisjoint : Pairwise (fun i j : I =>
      Disjoint (vertices G U i.1) (vertices G U j.1)) := by
    intro i j hne
    exact vertices_disjoint G U (fun heq => hne (Subtype.ext heq))
  have htree (i : I) : (J.induce (↑(vertices G U i.1) : Set G.Vertex)).IsTree := by
    rw [hagree i.1 i.2]
    exact smallForestPart_induced_tree G U P t S i.1 i.2
  have hforestCount := Erdos1016.Proof.ExteriorTreePathCount.card_exterior_trees_le_length_blocks
    C C' hC hdisjoint hdegree (fun i : I => vertices G U i.1) hFdisjoint
    (fun i v hv => hUC v (vertices_subset G U i.1 hv))
    (fun i v hv => hUC' v (vertices_subset G U i.1 hv))
    htree (fun i => hcubic i.1 i.2) D t q hq hg hbudget
    (fun i => hcut i.1 i.2) (fun i => hattachC i.1 i.2) (fun i => hattachC' i.1 i.2)
  have hforestCount' : (smallForestPart G U P t S).card ≤
      (C.length / q + 1) * (C'.length / q + 1) := by
    simpa only [I, Fintype.card_coe] using hforestCount
  have hcount := card_le_marked_large_cyclic_forest G U P hPU t K S hcyclic
  omega

end Erdos1016.FiniteMultiGraph.ExteriorComponents
