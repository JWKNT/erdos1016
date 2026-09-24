import Erdos1016.Decomposition.Regions.ComponentPartition

set_option autoImplicit false

/-!
# Expansion bounds the entire small complement, not one component

Manuscript Lemma 3.3. The ambient owner may have high-degree vertices outside
removed cycle supports. All component cuts are measured in that owner.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplySmallComponentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

@[simp] theorem relativeCut_univ (A : Finset G.Vertex) :
    relativeCutSize G Finset.univ A = cutSize G A := by
  simp only [relativeCutSize, relativeCut, cutSize, ownerCut]
  rw [← Finset.compl_eq_univ_sdiff A]

theorem card_compl_add (A : Finset G.Vertex) :
    A.card + Aᶜ.card = G.vertexCount := by
  simpa only [Fintype.card_fin] using Finset.card_add_card_compl A

theorem small_region_expansion (κ : ℝ) (hExp : HasExpansion G Finset.univ κ)
    (A : Finset G.Vertex) (hsmall : (A.card : ℝ) ≤ (G.vertexCount : ℝ) / 2) :
    κ * (A.card : ℝ) ≤ cutSize G A := by
  have hs := card_compl_add G A
  have hhalf : A.card ≤ Aᶜ.card := by
    have hs' : (A.card : ℝ) + (Aᶜ.card : ℝ) = G.vertexCount := by exact_mod_cast hs
    have hr : (A.card : ℝ) ≤ Aᶜ.card := by linarith
    exact_mod_cast hr
  have h := hExp A (Finset.subset_univ _)
  rw [relativeCut_univ, ← Finset.compl_eq_univ_sdiff A,
    min_eq_left hhalf] at h
  exact h

/-- Any collection of small complementary components uses at most the
original boundary budget, in total. -/
theorem small_component_family_bound (κ : ℝ) (hκ : 0 < κ)
    (hExp : HasExpansion G Finset.univ κ) (S : Finset G.Vertex)
    (F : Finset (Finset G.Vertex)) (hF : F ⊆ components G Sᶜ)
    (hsmall : ∀ C ∈ F, (C.card : ℝ) ≤ (G.vertexCount : ℝ) / 2) :
    (((F.biUnion id).card : ℕ) : ℝ) ≤ (cutSize G S : ℝ) / κ := by
  apply (le_div_iff₀ hκ).2
  have hsum : κ * (∑ C ∈ F, (C.card : ℝ)) ≤ ∑ C ∈ F, (cutSize G C : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun C hC => small_region_expansion G κ hExp C (hsmall C hC)
  have hcut : (∑ C ∈ F, (cutSize G C : ℝ)) ≤ cutSize G S := by
    exact_mod_cast component_subfamily_cut_sum_le G S F hF
  have hcard : (((F.biUnion id).card : ℕ) : ℝ) = ∑ C ∈ F, (C.card : ℝ) := by
    exact_mod_cast component_subfamily_card_sum G Sᶜ F hF
  rw [hcard, mul_comm]
  exact hsum.trans hcut

/-- Strict half-order prevents two disjoint giant components. -/
theorem at_most_one_giant (U : Finset G.Vertex) {C D : Finset G.Vertex}
    (hC : C ∈ components G U) (hD : D ∈ components G U)
    (hc : (G.vertexCount : ℝ) / 2 < (C.card : ℝ))
    (hd : (G.vertexCount : ℝ) / 2 < (D.card : ℝ)) : C = D := by
  by_contra hn
  have hcard : C.card + D.card ≤ G.vertexCount := by
    rw [← Finset.card_union_of_disjoint (components_disjoint G hC hD hn)]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (C ∪ D)
  have hcard' : (C.card : ℝ) + (D.card : ℝ) ≤ G.vertexCount := by exact_mod_cast hcard
  linarith

theorem nongiant_is_small (U : Finset G.Vertex) {C K : Finset G.Vertex}
    (hC : C ∈ components G U) (hK : K ∈ components G U) (hne : C ≠ K)
    (hbig : (G.vertexCount : ℝ) / 2 < (K.card : ℝ)) :
    (C.card : ℝ) ≤ (G.vertexCount : ℝ) / 2 := by
  by_contra hn
  exact hne (at_most_one_giant G U hC hK (lt_of_not_ge hn) hbig)

/-- Exact form of the giant-component statement. The order hypothesis has
no natural-number subtraction and includes every removed vertex. -/
theorem giant_and_total_small_bound (κ : ℝ) (hκ : 0 < κ)
    (hExp : HasExpansion G Finset.univ κ) (S : Finset G.Vertex)
    (hroom : (S.card : ℝ) + (cutSize G S : ℝ) / κ < G.vertexCount) :
    ∃ K ∈ components G Sᶜ,
      (G.vertexCount : ℝ) / 2 < (K.card : ℝ) ∧
      (((((components G Sᶜ).erase K).biUnion id).card : ℕ) : ℝ) ≤
        (cutSize G S : ℝ) / κ := by
  have hex : ∃ K ∈ components G Sᶜ, (G.vertexCount : ℝ) / 2 < (K.card : ℝ) := by
    by_contra hn
    push_neg at hn
    have hbound := small_component_family_bound G κ hκ hExp S
      (components G Sᶜ) (Finset.Subset.refl _) hn
    rw [components_union] at hbound
    have hs : (S.card : ℝ) + (Sᶜ.card : ℝ) = G.vertexCount := by
      exact_mod_cast card_compl_add G S
    linarith
  obtain ⟨K, hK, hbig⟩ := hex
  refine ⟨K, hK, hbig, ?_⟩
  apply small_component_family_bound G κ hκ hExp S ((components G Sᶜ).erase K)
    (Finset.erase_subset _ _)
  intro C hC
  obtain ⟨hne, hC⟩ := Finset.mem_erase.1 hC
  exact nongiant_is_small G Sᶜ hC hK hne hbig

/-- A connected protector larger than the entire small-component budget
must lie in the giant, with no degree assumption on the protector. -/
theorem root_small_complement_bound (κ : ℝ) (hκ : 0 < κ)
    (hExp : HasExpansion G Finset.univ κ) (S W : Finset G.Vertex)
    (hroom : (S.card : ℝ) + (cutSize G S : ℝ) / κ < G.vertexCount)
    (hW : ConnectedRegion G W) (hWS : W ⊆ Sᶜ)
    (hlarge : (cutSize G S : ℝ) / κ < W.card)
    (w : G.Vertex) (hw : w ∈ W) :
    (G.vertexCount : ℝ) / 2 < ((reachSet G Sᶜ w).card : ℝ) ∧
      ((offRootVertices G Sᶜ w).card : ℝ) ≤ (cutSize G S : ℝ) / κ := by
  obtain ⟨K, hK, hbig, hsmall⟩ := giant_and_total_small_bound G κ hκ hExp S hroom
  obtain ⟨C, hC, hWC⟩ := connected_subset_some_component G hW hWS
  have heq : C = K := by
    by_contra hn
    have hmem : C ∈ (components G Sᶜ).erase K := Finset.mem_erase.2 ⟨hn, hC⟩
    have hsub : W ⊆ ((components G Sᶜ).erase K).biUnion id := by
      intro v hv
      exact Finset.mem_biUnion.2 ⟨C, hmem, hWC hv⟩
    have hcard : (W.card : ℝ) ≤ ((((components G Sᶜ).erase K).biUnion id).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    linarith
  have hwK : w ∈ K := heq ▸ hWC hw
  have hr : K = reachSet G Sᶜ w := component_eq_reachSet G ((mem_components G Sᶜ K).1 hK) hwK
  refine ⟨by simpa only [← hr] using hbig, ?_⟩
  unfold offRootVertices
  rw [offRootComponents_eq_erase G (hWS hw), ← hr]
  exact hsmall

/-- Budgeted version used for a single cycle or the union of two cycles. -/
theorem root_small_bound_of_budget (κ : ℝ) (hκ : 0 < κ)
    (hExp : HasExpansion G Finset.univ κ) (S W : Finset G.Vertex)
    (d : ℕ) (horder : S.card ≤ d) (hcut : cutSize G S ≤ d)
    (hroom : (d : ℝ) + (d : ℝ) / κ < G.vertexCount)
    (hW : ConnectedRegion G W) (hWS : W ⊆ Sᶜ)
    (hlarge : (d : ℝ) / κ < W.card)
    (w : G.Vertex) (hw : w ∈ W) :
    ((offRootVertices G Sᶜ w).card : ℝ) ≤ (d : ℝ) / κ := by
  have hd : (cutSize G S : ℝ) / κ ≤ (d : ℝ) / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le
    exact_mod_cast hcut
  have ho : (S.card : ℝ) ≤ d := by exact_mod_cast horder
  exact (root_small_complement_bound G κ hκ hExp S W (by linarith)
    hW hWS (hd.trans_lt hlarge) w hw).2.trans hd

/-- Whole owner connectivity of a literal cycle support. -/
theorem cycle_vertices_connected (C : G.CycleWord) : ConnectedRegion G (Cycle.vertices C) := by
  apply (connectedRegion_iff_induce_connected G (Cycle.vertices C)).2
  exact SimpleGraph.Connected.mono (by
    intro u v huv
    rcases huv with ⟨e, _, h⟩
    exact ⟨e, one_ne_zero, h⟩) C.2.2.2.1

/-- Cubic support vertices leave at most one boundary edge per cycle vertex;
chords only reduce that boundary. -/
theorem cycle_cut_le_length (C : G.CycleWord)
    (hc : ∀ v ∈ Cycle.vertices C, G.degree v = 3) :
    cutSize G (Cycle.vertices C) ≤ BoundaryDecay.Cycle.length C := by
  have hdeg := cubic_cut_identity G (Cycle.vertices C) hc
  have hin := Cycle.vertices_card_le_internal C
  rw [BoundaryDecay.Cycle.length_eq_vertices_card]
  omega

theorem two_cycle_cut_le {C D : G.CycleWord}
    (hdis : Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hC : ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (hD : ∀ v ∈ Cycle.vertices D, G.degree v = 3) :
    cutSize G (Cycle.vertices C ∪ Cycle.vertices D) ≤
      BoundaryDecay.Cycle.length C + BoundaryDecay.Cycle.length D := by
  have hid := cutSize_union G (Cycle.vertices C) (Cycle.vertices D) hdis
  have hc := cycle_cut_le_length G C hC
  have hd := cycle_cut_le_length G D hD
  omega

end Erdos1016.CycleSupply
