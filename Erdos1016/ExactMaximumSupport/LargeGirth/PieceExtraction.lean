import Erdos1016.ExactMaximumSupport.LargeGirth.PieceCore
import Erdos1016.Graph.ExteriorComponents
import Erdos1016.Graph.ConnectedRegionBoundary

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# A large-rank component in an actual cubic region

The component regions partition the original vertex set, and their physical
boundaries are disjoint. The connected cubic order identity therefore forces
a large-rank component in a large region with a small boundary.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PieceExtraction
open FiniteMultiGraph
open ExteriorComponents
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

theorem sum_component_card : (∑ c : Component G X, (vertices G X c).card) = X.card := by
  have hp : (↑(Finset.univ : Finset (Component G X)) : Set (Component G X)).PairwiseDisjoint
      (vertices G X) := by
    intro c _ d _ hne
    exact vertices_disjoint G X hne
  rw [← Finset.card_biUnion hp]
  congr 1
  ext v
  constructor
  · intro hv
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hv
    exact vertices_subset G X c hc
  · intro hv
    exact Finset.mem_biUnion.mpr ⟨(graph G X).connectedComponentMk ⟨v, hv⟩,
      Finset.mem_univ _, (mem_vertices G X _ v).mpr ⟨hv, rfl⟩⟩

theorem component_nonempty (c : Component G X) : (vertices G X c).Nonempty := by
  obtain ⟨v⟩ := (vertices_connected G X c).nonempty
  exact ⟨v.1, v.2⟩

/-- Every component of a proper region has a physical boundary edge. -/
theorem component_cut_pos (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (c : Component G X) : 0 < (G.cutEdges (vertices G X c)).card := by
  have hn : (↑(vertices G X c) : Set G.Vertex).Nonempty := component_nonempty G X c
  have hp : (↑(vertices G X c) : Set G.Vertex) ≠ Set.univ := by
    intro heq
    apply hproper
    apply Finset.eq_univ_of_forall
    intro v
    apply vertices_subset G X c
    have hv : v ∈ (↑(vertices G X c) : Set G.Vertex) := by rw [heq]; trivial
    exact hv
  obtain ⟨a, b, ha, hb, _, e, he⟩ :=
    Proof.ConnectedRegionBoundary.Connected.exists_adj_boundary hG hn hp
  apply Finset.card_pos.mpr
  refine ⟨e, ?_⟩
  rcases he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · simpa only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht] using
      (Or.inl ⟨ha, hb⟩ : (a ∈ vertices G X c ∧ b ∉ vertices G X c) ∨
        (a ∉ vertices G X c ∧ b ∈ vertices G X c))
  · simpa only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, hs, ht] using
      (Or.inr ⟨hb, ha⟩ : (b ∈ vertices G X c ∧ a ∉ vertices G X c) ∨
        (b ∉ vertices G X c ∧ a ∈ vertices G X c))

/-- A component of rank below Λ has order at most twice Λ times its cut. -/
theorem component_order_bound (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (hcubic : ∀ v ∈ X, G.degree v = 3) (Λ : ℕ)
    (c : Component G X) (hr : (PieceCore.Induced.graph G (vertices G X c)).cycleRank < Λ) :
    (vertices G X c).card ≤ 2*Λ*(G.cutEdges (vertices G X c)).card := by
  have he := PieceCore.Induced.order_rank_cut G (vertices G X c)
    (vertices_connected G X c) (fun v hv => hcubic v (vertices_subset G X c hv))
  have hd := component_cut_pos G X hG hproper c
  have hm : (2*Λ - 1)*1 ≤ (2*Λ - 1)*(G.cutEdges (vertices G X c)).card :=
    Nat.mul_le_mul_left _ hd
  nlinarith

/-- The component is extracted from the actual induced region, not supplied
as a certificate. The stronger intermediate order bound is 4Λ². -/
theorem exists_component_rank (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (hcubic : ∀ v ∈ X, G.degree v = 3) (Λ : ℕ) (hΛ : 1 ≤ Λ)
    (hsize : 8*Λ^2 ≤ X.card) (hcut : (G.cutEdges X).card ≤ 2*Λ) :
    ∃ c : Component G X, Λ ≤ (PieceCore.Induced.graph G (vertices G X c)).cycleRank := by
  by_contra h
  push_neg at h
  have hb : X.card ≤ 2*Λ*(G.cutEdges X).card := by
    rw [← sum_component_card G X]
    calc
      _ ≤ ∑ c : Component G X, 2*Λ*(G.cutEdges (vertices G X c)).card :=
        Finset.sum_le_sum (fun c _ => component_order_bound G X hG hproper hcubic Λ c (h c))
      _ = 2*Λ*(∑ c : Component G X, (G.cutEdges (vertices G X c)).card) := by rw [Finset.mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left _ (sum_cut_card_le G X)
  have hm := Nat.mul_le_mul_left (2*Λ) hcut
  nlinarith

/-- The paper's parameter Λ may be real. No rounding loss is needed in
the component ledger. -/
theorem exists_component_rank_real (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (hcubic : ∀ v ∈ X, G.degree v = 3) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hsize : 8*Λ^2 ≤ (X.card : ℝ)) (hcut : ((G.cutEdges X).card : ℝ) ≤ 2*Λ) :
    ∃ c : Component G X, Λ ≤ ((PieceCore.Induced.graph G (vertices G X c)).cycleRank : ℝ) := by
  by_contra h
  push_neg at h
  have hb (c : Component G X) : ((vertices G X c).card : ℝ) ≤
      2*Λ*((G.cutEdges (vertices G X c)).card : ℝ) := by
    have he : ((vertices G X c).card : ℝ)+2 =
        2*((PieceCore.Induced.graph G (vertices G X c)).cycleRank : ℝ)+
          (G.cutEdges (vertices G X c)).card := by
      exact_mod_cast PieceCore.Induced.order_rank_cut G (vertices G X c)
        (vertices_connected G X c) (fun v hv => hcubic v (vertices_subset G X c hv))
    have hd : (1 : ℝ) ≤ (G.cutEdges (vertices G X c)).card := by
      exact_mod_cast Nat.succ_le_of_lt (component_cut_pos G X hG hproper c)
    have hm : 0 ≤ (2*Λ-1)*(((G.cutEdges (vertices G X c)).card : ℝ)-1) :=
      mul_nonneg (by linarith) (by linarith)
    have hr := h c
    nlinarith
  have hs : (X.card : ℝ) ≤ 2*Λ*((G.cutEdges X).card : ℝ) := by
    calc
      _ = ∑ c : Component G X, ((vertices G X c).card : ℝ) := by
        exact_mod_cast (sum_component_card G X).symm
      _ ≤ ∑ c : Component G X, 2*Λ*((G.cutEdges (vertices G X c)).card : ℝ) :=
        Finset.sum_le_sum (fun c _ => hb c)
      _ = 2*Λ*(∑ c : Component G X, ((G.cutEdges (vertices G X c)).card : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast sum_cut_card_le G X) (by linarith)
  nlinarith

/-- A large piece contains an actual induced degree-two/three pole whose
rank is at least Λ and whose ports use at most the piece's cut budget. -/
theorem exists_induced_core_real_of_ne_univ
    (hG : G.toSimpleGraph.Connected) (hproper : X ≠ Finset.univ)
    (hcubic : ∀ v ∈ X, G.degree v = 3) (Λ : ℝ) (hΛ : 4 ≤ Λ)
    (hsize : 8*Λ^2 ≤ (X.card : ℝ)) (hcut : ((G.cutEdges X).card : ℝ) ≤ 2*Λ)
    (g : ℕ) (hg : 3 ≤ g) (hshort : ¬ (PieceCore.Induced.graph G X).HasCycleShorterThan g) :
    ∃ U : Finset G.Vertex, U ⊆ X ∧
      (PieceCore.Induced.graph G U).toSimpleGraph.Connected ∧
      Λ ≤ ((PieceCore.Induced.graph G U).cycleRank : ℝ) ∧
      (∀ v, 2 ≤ (PieceCore.Induced.graph G U).degree v ∧
        (PieceCore.Induced.graph G U).degree v ≤ 3) ∧
      ¬ (PieceCore.Induced.graph G U).HasCycleShorterThan g ∧
      ((PieceCore.Induced.graph G U).cubicDeficit : ℝ) ≤ 2*Λ := by
  obtain ⟨c, hr⟩ := exists_component_rank_real G X hG hproper hcubic Λ (by linarith) hsize hcut
  have hr' : 2 ≤ (PieceCore.Induced.graph G (vertices G X c)).cycleRank := by
    have hh : (2 : ℝ) ≤ (PieceCore.Induced.graph G (vertices G X c)).cycleRank := by linarith
    exact_mod_cast hh
  obtain ⟨U, hU, hUc, hUr, hUd, hUg, hUb⟩ := PieceCore.exists_induced_core G (vertices G X c)
    (vertices_connected G X c) (fun v hv => hcubic v (vertices_subset G X c hv)) hr' g hg
    (PieceCore.Induced.no_short_mono G X (vertices G X c) (vertices_subset G X c) g hg hshort)
  refine ⟨U, hU.trans (vertices_subset G X c), hUc, ?_, hUd, hUg, ?_⟩
  · rwa [hUr]
  · have hb := hUb.trans (Finset.card_le_card (cut_subset G X c))
    exact (show ((PieceCore.Induced.graph G U).cubicDeficit : ℝ) ≤ (G.cutEdges X).card by
      exact_mod_cast hb).trans hcut

/-- Clean-core extraction also covers a piece equal to the whole graph. -/
theorem exists_induced_core_real
    (hG : G.toSimpleGraph.Connected)
    (hcubic : ∀ v ∈ X, G.degree v = 3) (Λ : ℝ) (hΛ : 4 ≤ Λ)
    (hsize : 8*Λ^2 ≤ (X.card : ℝ)) (hcut : ((G.cutEdges X).card : ℝ) ≤ 2*Λ)
    (g : ℕ) (hg : 3 ≤ g) (hshort : ¬ (PieceCore.Induced.graph G X).HasCycleShorterThan g) :
    ∃ U : Finset G.Vertex, U ⊆ X ∧
      (PieceCore.Induced.graph G U).toSimpleGraph.Connected ∧
      Λ ≤ ((PieceCore.Induced.graph G U).cycleRank : ℝ) ∧
      (∀ v, 2 ≤ (PieceCore.Induced.graph G U).degree v ∧
        (PieceCore.Induced.graph G U).degree v ≤ 3) ∧
      ¬ (PieceCore.Induced.graph G U).HasCycleShorterThan g ∧
      ((PieceCore.Induced.graph G U).cubicDeficit : ℝ) ≤ 2*Λ := by
  by_cases hproper : X ≠ Finset.univ
  · exact exists_induced_core_real_of_ne_univ G X hG hproper hcubic Λ hΛ hsize hcut g hg hshort
  · have hX : X = Finset.univ := not_ne_iff.mp hproper
    have hc : (G.toSimpleGraph.induce (↑X : Set G.Vertex)).Connected := by
      rw [hX, Finset.coe_univ]
      exact G.toSimpleGraph.induceUnivIso.connected_iff.mpr hG
    have hzero : (G.cutEdges X).card = 0 := by simp [hX, cutEdges]
    have he : (X.card : ℝ)+2 = 2*((PieceCore.Induced.graph G X).cycleRank : ℝ) := by
      have he := PieceCore.Induced.order_rank_cut G X hc hcubic
      rw [hzero, add_zero] at he
      exact_mod_cast he
    have hr : Λ ≤ ((PieceCore.Induced.graph G X).cycleRank : ℝ) := by nlinarith
    have hr' : 2 ≤ (PieceCore.Induced.graph G X).cycleRank := by
      have hh : (2 : ℝ) ≤ (PieceCore.Induced.graph G X).cycleRank := by linarith
      exact_mod_cast hh
    obtain ⟨U, hU, hUc, hUr, hUd, hUg, hUb⟩ :=
      PieceCore.exists_induced_core G X hc hcubic hr' g hg hshort
    refine ⟨U, hU, hUc, ?_, hUd, hUg, ?_⟩
    · rwa [hUr]
    · exact (show ((PieceCore.Induced.graph G U).cubicDeficit : ℝ) ≤ (G.cutEdges X).card by
        exact_mod_cast hUb).trans hcut

end Erdos1016.ExactMaximumSupport.LargeGirth.PieceExtraction
