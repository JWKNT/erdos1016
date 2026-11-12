import Erdos1016.ExactMaximumSupport.LargeGirth.GoodRow

set_option autoImplicit false

/-!
# A separator witness for an actual good pair

Two quotient links and no direct edge force two exterior components.
One avoids the anchor. Its attachment to the first cycle is separated from
the anchor by the second cycle after the first cycle has been deleted.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open FiniteMultiGraph FiniteMultiGraph.ExteriorComponents
open FiniteMultiGraph.SeedPairCorrelation
open PolynomialBound.Separation PolynomialBound.ParallelLinks
open PolynomialBound.TwoLinkMoment

local instance separatorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem mem_cutOutsideVertices_of_adj (G : FiniteMultiGraph) (A : Finset G.Vertex)
    {a u : G.Vertex} (ha : a ∈ A) (hu : u ∉ A) (hadj : G.toSimpleGraph.Adj a u) :
    u ∈ cutOutsideVertices G A := by
  obtain ⟨_, e, he⟩ := hadj
  apply Finset.mem_image.mpr
  refine ⟨e, ?_, ?_⟩
  · rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · simp [cutEdges, hs, ht, ha, hu]
    · simp [cutEdges, hs, ht, ha, hu]
  · rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simp [hs, ht, ha, hu]

/-- Two actual links with no direct label include an exterior component
that avoids any prescribed anchor vertex. -/
theorem exists_link_component_avoiding (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (p : G.Vertex) (hd : Disjoint A B) (htwo : 2 ≤ Nat.card (Links G A B))
    (hnodirect : ¬ (G.directLabels A B).Nonempty) :
    ∃ c ∈ exteriorLinks G A B, p ∉ vertices G (A ∪ B)ᶜ c := by
  have hbound := links_card_le_direct_add_exterior G A B hd
  rw [Finset.not_nonempty_iff_eq_empty.mp hnodirect, Finset.card_empty, zero_add] at hbound
  obtain ⟨c, hc, d, hdS, hcd⟩ := Finset.one_lt_card.mp (show 1 < (exteriorLinks G A B).card by omega)
  by_cases hp : p ∈ vertices G (A ∪ B)ᶜ c
  · refine ⟨d, hdS, ?_⟩
    exact fun hpd => Finset.disjoint_left.mp (vertices_disjoint G (A ∪ B)ᶜ hcd) hp hpd
  · exact ⟨c, hc, hp⟩

/-- A link component avoiding the anchor produces a literal separator
witness. Connectivity and disconnection use the ambient vertex labels. -/
theorem link_component_separator (G : FiniteMultiGraph) (A B : Finset G.Vertex)
    (p : G.Vertex) (hd : Disjoint A B)
    (hB : (G.toSimpleGraph.induce (↑B : Set G.Vertex)).Connected)
    (hnear : ¬ Disjoint (↑B : Set G.Vertex) (side G.toSimpleGraph (↑A) p))
    (c : Component G (A ∪ B)ᶜ) (hc : BothAttached G A B c)
    (hpc : p ∉ vertices G (A ∪ B)ᶜ c) :
    ∃ u ∈ cutOutsideVertices G A, u ∉ B ∧
      AvoidReach G.toSimpleGraph (↑A) u p ∧
      ¬ AvoidReach G.toSimpleGraph (↑(A ∪ B)) u p := by
  obtain ⟨a, ha, u, hu, hau⟩ := hc.1
  obtain ⟨b, hb, v, hv, hbv⟩ := hc.2
  have hout (w : G.Vertex) (hw : w ∈ vertices G (A ∪ B)ᶜ c) : w ∉ A ∧ w ∉ B := by
    simpa only [Finset.mem_compl, Finset.mem_union, not_or] using
      vertices_subset G (A ∪ B)ᶜ c hw
  have hmeet : ∃ w ∈ B, AvoidReach G.toSimpleGraph (↑A) p w := by
    by_contra hn
    push_neg at hn
    exact hnear (Set.disjoint_left.mpr hn)
  obtain ⟨w, hw, hpw⟩ := hmeet
  have hBset := isConnectedSet_of_induce hB
  have hBA : Disjoint (↑B : Set G.Vertex) (↑A) := by exact_mod_cast hd.symm
  have hpb : AvoidReach G.toSimpleGraph (↑A) p b :=
    hpw.trans (hBset.avoidReach hBA hw hb)
  have hpv : AvoidReach G.toSimpleGraph (↑A) p v := hpb.step hbv (hout v hv).1
  have hYset := isConnectedSet_of_induce (vertices_connected G (A ∪ B)ᶜ c)
  have hYA : Disjoint (↑(vertices G (A ∪ B)ᶜ c) : Set G.Vertex) (↑A) :=
    Set.disjoint_left.mpr fun y hy hyA => (hout y hy).1 hyA
  have hpu : AvoidReach G.toSimpleGraph (↑A) p u :=
    hpv.trans (hYset.avoidReach hYA hv hu)
  refine ⟨u, mem_cutOutsideVertices_of_adj G A ha (hout u hu).1 hau,
    (hout u hu).2, hpu.symm, ?_⟩
  rintro ⟨q, hq⟩
  have hstay := walk_stays G (A ∪ B)ᶜ c q hu (fun y hy => Finset.mem_compl.mpr (hq y hy))
  exact hpc (hstay p q.end_mem_support)

/-- Every actual good pair supplies an attachment separated from the
anchor when its second support is removed from the first complement. -/
theorem goodTwoLink_separator {ι : Type*} (G : FiniteMultiGraph)
    (U : ι → Finset G.Vertex) (p : G.Vertex) (i j : ι)
    (hB : (G.toSimpleGraph.induce (↑(U j) : Set G.Vertex)).Connected)
    (hgood : goodTwoLink G U p i j = 1) :
    ∃ u ∈ cutOutsideVertices G (U i), u ∉ U j ∧
      AvoidReach G.toSimpleGraph (↑(U i)) u p ∧
      ¬ AvoidReach G.toSimpleGraph (↑(U i ∪ U j)) u p := by
  have hs : twoLink G U i j = 1 ∧
      ¬ Disjoint (↑(U j) : Set G.Vertex) (side G.toSimpleGraph (↑(U i)) p) ∧
      ¬ (G.directLabels (U i) (U j)).Nonempty := by
    unfold goodTwoLink at hgood
    split_ifs at hgood with h
    · exact h
    · norm_num at hgood
  have ht := (twoLink_eq_one_iff G U i j).mp hs.1
  obtain ⟨c, hc, hpc⟩ := exists_link_component_avoiding G (U i) (U j) p ht.2.1
    ht.2.2.ge hs.2.2
  exact link_component_separator G (U i) (U j) p ht.2.1 hB hs.2.1 c
    (Finset.mem_filter.mp hc).2 hpc

end Erdos1016.ExactMaximumSupport.LargeGirth
