import Erdos1016.Decomposition.Regions.Cuts

set_option autoImplicit false

/-! # Low original deficit really gives a cyclic physical region -/
noncomputable section
namespace Erdos1016.SafeCore
local instance instSafeCoreCyclicityPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

def CyclicRegion (U : Finset G.Vertex) : Prop :=
  ConnectedRegion G U ∧
    ¬ (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsAcyclic

/-- Count individually labelled internal physical edges by the induced
simple graph's actual edge set. Simplicity is used for injectivity. -/
theorem internalEdges_card_eq_natCard (U : Finset G.Vertex) :
    (internalEdges G U).card =
      Nat.card (G.toSimpleGraph.induce (↑U : Set G.Vertex)).edgeSet := by
  let H := G.toSimpleGraph.induce (↑U : Set G.Vertex)
  let f : {e // e ∈ internalEdges G U} → H.edgeSet := fun e =>
    ⟨s(⟨G.src e.1, ((Finset.mem_filter.1 e.2).2).1⟩,
       ⟨G.dst e.1, ((Finset.mem_filter.1 e.2).2).2⟩), by
      change G.toSimpleGraph.Adj (G.src e.1) (G.dst e.1)
      exact ⟨e.1, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e d hed
      apply Subtype.ext
      apply G.simple
      have hsym := congrArg Subtype.val hed
      rcases Sym2.eq_iff.1 hsym with h | h
      · exact Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
      · exact Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
    · rintro ⟨a, ha⟩
      revert ha
      refine Sym2.inductionOn a ?_
      intro u v huv
      change G.toSimpleGraph.Adj u.1 v.1 at huv
      rcases huv with ⟨e, _, h | h⟩
      · have he : e ∈ internalEdges G U := Finset.mem_filter.2
          ⟨Finset.mem_univ _, h.1.symm ▸ u.2, h.2.symm ▸ v.2⟩
        refine ⟨⟨e, he⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_iff.2 (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
      · have he : e ∈ internalEdges G U := Finset.mem_filter.2
          ⟨Finset.mem_univ _, h.1.symm ▸ v.2, h.2.symm ▸ u.2⟩
        refine ⟨⟨e, he⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_iff.2 (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    Nat.card_congr (Equiv.ofBijective f hf)

theorem tree_edge_identity {U : Finset G.Vertex}
    (hU : ConnectedRegion G U)
    (ha : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsAcyclic) :
    (internalEdges G U).card + 1 = U.card := by
  have ht : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsTree :=
    ⟨(connectedRegion_iff_induce_connected G U).1 hU, ha⟩
  have h := (SimpleGraph.isTree_iff_connected_and_card).1 ht
  rw [← internalEdges_card_eq_natCard G U] at h
  have hcard : Nat.card {v : G.Vertex // v ∈ (↑U : Set G.Vertex)} = U.card := by
    classical
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {v : G.Vertex // v ∈ U} = U.card
    exact Fintype.card_coe U
  rw [hcard] at h
  exact h.2

theorem cubic_tree_cut {U : Finset G.Vertex}
    (hc : ∀ v ∈ U, G.degree v = 3) (hU : ConnectedRegion G U)
    (ha : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).IsAcyclic) :
    cutSize G U = U.card + 2 := by
  have hdeg := cubic_cut_identity G U hc
  have hed := tree_edge_identity G hU ha
  omega

theorem cyclic_of_cut_lt_order {U : Finset G.Vertex}
    (hc : ∀ v ∈ U, G.degree v = 3) (hU : ConnectedRegion G U)
    (hcut : cutSize G U < U.card) : CyclicRegion G U := by
  refine ⟨hU, ?_⟩
  intro htree
  have := cubic_tree_cut G hc hU htree
  omega

/-- No isolated vertex or induced tree can be treated as a low-potential leaf. -/
theorem low_cut_is_cyclic {U : Finset G.Vertex} {B p : ℝ}
    (hc : ∀ v ∈ U, G.degree v = 3) (hU : ConnectedRegion G U)
    (hB0 : 0 ≤ B) (hB1 : B < 1) (hp : p ≤ 1)
    (hcut : (cutSize G U : ℝ) ≤ B * (U.card : ℝ) ^ p) : CyclicRegion G U := by
  have hn : 1 ≤ (U.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hU.1
  have hpow : (U.card : ℝ) ^ p ≤ U.card := Real.rpow_le_self_of_one_le hn hp
  have hsmall : (cutSize G U : ℝ) < U.card := by
    calc
      (cutSize G U : ℝ) ≤ B * (U.card : ℝ) ^ p := hcut
      _ ≤ B * (U.card : ℝ) := mul_le_mul_of_nonneg_left hpow hB0
      _ < (U.card : ℝ) := by nlinarith
  apply cyclic_of_cut_lt_order G hc hU
  exact_mod_cast hsmall

end Erdos1016.SafeCore
