import Erdos1016.Probability.Moments.PairQuotientGeometry
import Erdos1016.Graph.Multigraph.DirectRegionEdges

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Actual quotient links inject into original direct edges and exterior components. -/

noncomputable section
namespace Erdos1016.FiniteMultiGraph.SeedPairCorrelation

open ConnectedContraction ExceptionalPartners
local instance pairLinkCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (U V : Finset G.Vertex)

/-- An original exterior component with a physical attachment to each region. -/
def BothAttached (c : ExteriorComponents.Component G (U ∪ V)ᶜ) : Prop :=
  (∃ u ∈ U, ∃ x ∈ ExteriorComponents.vertices G (U ∪ V)ᶜ c, G.toSimpleGraph.Adj u x) ∧
  (∃ v ∈ V, ∃ y ∈ ExteriorComponents.vertices G (U ∪ V)ᶜ c, G.toSimpleGraph.Adj v y)

def exteriorLinks : Finset (ExteriorComponents.Component G (U ∪ V)ᶜ) :=
  Finset.univ.filter (BothAttached G U V)

abbrev DirectLink := {e : CutIncidence (pairQuotient G U V) (firstVertex G U V) //
  otherEndpoint (pairQuotient G U V) (firstVertex G U V) e = secondVertex G U V}

abbrev ComponentLink := TerminalBranch (deleted (pairQuotient G U V).toSimpleGraph
  (firstVertex G U V))
  (attachmentVertices (otherEndpoint (pairQuotient G U V) (firstVertex G U V)))
  (secondVertex G U V)

def directLinkOriginal (hUV : Disjoint U V) (e : DirectLink G U V) :
    {f : G.Edge // f ∈ G.directLabels U V} := by
  let f := ((edgeEquiv G (pairLabel G U V)).symm e.1.1).1
  refine ⟨f, (G.mem_directLabels U V f).mpr ?_⟩
  have he := (otherEndpoint_eq_iff (pairQuotient G U V) (firstVertex G U V)
    e.1 (secondVertex G U V)).mp (congrArg Subtype.val e.2)
  have hlabel (b : Bool) (w : G.Vertex) :
      pairLabel G U V w = Sum.inl b ↔ w ∈ regions G U V b :=
    DisjointRegionCuts.label_eq_inl_iff G (regions G U V) (pair_regions_disjoint G U V hUV) w b
  rcases he with h | h
  · exact Or.inl ⟨(hlabel false _).mp (vertexEquiv.injective h.1),
      (hlabel true _).mp (vertexEquiv.injective h.2)⟩
  · exact Or.inr ⟨(hlabel true _).mp (vertexEquiv.injective h.2),
      (hlabel false _).mp (vertexEquiv.injective h.1)⟩

lemma directLinkOriginal_injective (hUV : Disjoint U V) :
    Function.Injective (directLinkOriginal G U V hUV) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply (edgeEquiv G (pairLabel G U V)).symm.injective
  apply Subtype.ext
  exact congrArg (fun z : {f : G.Edge // f ∈ G.directLabels U V} => z.1) h

def componentOriginal (c : (doubleDeletedGraph G U V).ConnectedComponent) :
    ExteriorComponents.Component G (U ∪ V)ᶜ :=
  (exteriorGraphIso G U V).symm.connectedComponentEquiv c

lemma mem_componentOriginal (q : DoubleDeletedVertex G U V)
    (c : (doubleDeletedGraph G U V).ConnectedComponent)
    (hc : (doubleDeletedGraph G U V).connectedComponentMk q = c) :
    ((exteriorGraphIso G U V).symm q).1 ∈
      ExteriorComponents.vertices G (U ∪ V)ᶜ (componentOriginal G U V c) := by
  apply (ExteriorComponents.mem_vertices G (U ∪ V)ᶜ _ _).mpr
  refine ⟨((exteriorGraphIso G U V).symm q).2, ?_⟩
  exact congrArg (exteriorGraphIso G U V).symm.connectedComponentEquiv hc

lemma componentLink_bothAttached (hUV : Disjoint U V) (c : ComponentLink G U V) :
    BothAttached G U V (componentOriginal G U V c.1) := by
  have hcond := (terminalBranch_condition_iff
    (deleted (pairQuotient G U V).toSimpleGraph (firstVertex G U V))
    (attachmentVertices (otherEndpoint (pairQuotient G U V) (firstVertex G U V)))
    (secondVertex G U V) c.1).mp c.2
  obtain ⟨⟨t, ht, htc⟩, ⟨v, hv, hvc⟩⟩ := hcond
  have hout (q : DoubleDeletedVertex G U V) :
      exteriorVertex G U V ((exteriorGraphIso G U V).symm q) = q :=
    (exteriorGraphIso G U V).apply_symm_apply q
  have hta : (pairQuotient G U V).toSimpleGraph.Adj (firstVertex G U V) t.1.1 := by
    simp only [attachmentVertices, Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨e, he⟩ := ht
    have he' := (otherEndpoint_eq_iff (pairQuotient G U V) (firstVertex G U V)
      e t.1).mp (congrArg Subtype.val he)
    refine ⟨t.1.2.symm, e.1, ?_⟩
    exact he'.elim Or.inl (fun h => Or.inr ⟨h.2, h.1⟩)
  have hfirst : ∃ u ∈ U,
      G.toSimpleGraph.Adj u ((exteriorGraphIso G U V).symm t).1 := by
    apply (adj_region_exterior_iff G U V hUV false _).mp
    rw [hout]
    exact hta
  have hsecond : ∃ u ∈ V,
      G.toSimpleGraph.Adj u ((exteriorGraphIso G U V).symm v).1 := by
    apply (adj_region_exterior_iff G U V hUV true _).mp
    rw [hout]
    exact hv
  obtain ⟨u, hu, hut⟩ := hfirst
  obtain ⟨w, hw, hwv⟩ := hsecond
  exact ⟨⟨u, hu, _, mem_componentOriginal G U V t c.1 htc, hut⟩,
    ⟨w, hw, _, mem_componentOriginal G U V v c.1 hvc, hwv⟩⟩

def componentLinkOriginal (hUV : Disjoint U V) (c : ComponentLink G U V) :
    {d // d ∈ exteriorLinks G U V} :=
  ⟨componentOriginal G U V c.1,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, componentLink_bothAttached G U V hUV c⟩⟩

lemma componentLinkOriginal_injective (hUV : Disjoint U V) :
    Function.Injective (componentLinkOriginal G U V hUV) := by
  intro c d h
  apply Subtype.ext
  exact (exteriorGraphIso G U V).symm.connectedComponentEquiv.injective (congrArg Subtype.val h)

/-- The correlation's quotient count is bounded by literal original
physical labels and doubly attached original exterior components. -/
theorem links_card_le_direct_add_exterior (hUV : Disjoint U V) :
    Nat.card (Links G U V) ≤ (G.directLabels U V).card + (exteriorLinks G U V).card := by
  have h := Fintype.card_le_of_injective
    (Sum.map (directLinkOriginal G U V hUV) (componentLinkOriginal G U V hUV))
    ((directLinkOriginal_injective G U V hUV).sumMap
      (componentLinkOriginal_injective G U V hUV))
  change Nat.card (DirectLink G U V ⊕ ComponentLink G U V) ≤ _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe] using h

end Erdos1016.FiniteMultiGraph.SeedPairCorrelation
