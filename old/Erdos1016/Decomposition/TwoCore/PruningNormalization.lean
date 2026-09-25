import Erdos1016.Decomposition.TwoCore.LeafPruning

set_option autoImplicit false

/-!
# Full two-core normalization in the unchanged cubic owner

A real deletion sequence is constructed by strict cardinal induction. The
maximality field proves this is the FULL two-core, not a chosen min-two
subgraph. The integer cut/order ledger and every exterior comparison remain
in the original owner.
-/
noncomputable section
namespace Erdos1016.SafeCore
local instance instSafeCoreTwoCorePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

structure PrunedCore (U : Finset G.Vertex) (h : ℝ) where
  vertices : Finset G.Vertex
  subset : vertices ⊆ U
  connected : ConnectedRegion G vertices
  minTwo : MinTwo G vertices
  maximal : ∀ A ⊆ U, MinTwo G A → A ⊆ vertices
  ledger : vertices.card + cutSize G U = U.card + cutSize G vertices
  cut_le : cutSize G vertices ≤ cutSize G U
  exterior_le : exteriorCount G vertices ≤ exteriorCount G U
  expansion : HasExpansion G vertices h

/-- Full finite pruning. The strict cut/order invariant excludes any need to
delete isolated vertices; every actual deletion is a degree-one leaf. -/
theorem exists_prunedCore {U : Finset G.Vertex} {h : ℝ}
    (hc : ∀ v ∈ U, G.degree v = 3)
    (hU : ConnectedRegion G U) (hcut : cutSize G U < U.card)
    (hh : 0 ≤ h) (hexp : HasExpansion G U h) :
    Nonempty (PrunedCore G U h) := by
  have aux : ∀ n : ℕ, ∀ U : Finset G.Vertex, U.card = n →
      (∀ v ∈ U, G.degree v = 3) → ConnectedRegion G U →
      cutSize G U < U.card → HasExpansion G U h → Nonempty (PrunedCore G U h) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hn hc hU hcut hexp
      by_cases hm : MinTwo G U
      · exact ⟨⟨U, Finset.Subset.refl _, hU, hm,
          fun _ hsub _ => hsub, rfl, le_rfl, le_rfl, hexp⟩⟩
      · obtain ⟨l⟩ := exists_leaf_of_not_minTwo G hc hU hcut hm
        have hcard := l.remainder_card
        have hboundary := l.cut_remainder (hc _ l.vertex_mem)
        have hsmall : l.remainder.card < n := by omega
        have hlow : cutSize G l.remainder < l.remainder.card := by omega
        obtain ⟨K⟩ := ih l.remainder.card hsmall l.remainder rfl
          (fun v hv => hc v (l.remainder_subset hv)) (l.connected_remainder hU)
          hlow (l.expansion_remainder hh hexp)
        refine ⟨{
          vertices := K.vertices
          subset := K.subset.trans l.remainder_subset
          connected := K.connected
          minTwo := K.minTwo
          maximal := ?_
          ledger := ?_
          cut_le := ?_
          exterior_le := K.exterior_le.trans (l.exterior_remainder hU (hc _ l.vertex_mem))
          expansion := K.expansion }⟩
        · intro A hAU hA
          exact K.maximal A (minTwo_avoids_leaf G l hA hAU) hA
        · have := K.ledger
          omega
        · have := K.cut_le
          omega
  exact aux U.card U rfl hc hU hcut hexp



theorem low_implies_cut_lt_card (P : CutParameters) {U : Finset G.Vertex}
    (hU : U.Nonempty) (hlow : Low G P U) : cutSize G U < U.card := by
  have hn : 1 ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hU
  have hr := Real.rpow_le_self_of_one_le hn P.p_lt_one.le
  have hb : (cutSize G U : ℝ) < U.card := by
    calc
      (cutSize G U : ℝ) ≤ P.B * (U.card : ℝ) ^ P.p := hlow
      _ ≤ P.B * (U.card : ℝ) := mul_le_mul_of_nonneg_left hr P.B_pos.le
      _ < (U.card : ℝ) := by nlinarith [P.B_lt_one]
  exact_mod_cast hb

/-- Source Lemma 16.1, before rescaling the numerical expansion constant. -/
theorem low_region_full_twoCore (P : CutParameters) {U : Finset G.Vertex}
    (hc : ∀ v ∈ U, G.degree v = 3) (hU : ConnectedRegion G U)
    (hlow : Low G P U) (hexp : Expanded G P U) :
    ∃ K : PrunedCore G U (P.epsilon * (U.card : ℝ) ^ (P.p - 1)),
      (1 - P.B) * (U.card : ℝ) ≤ K.vertices.card ∧
      (∀ v ∈ K.vertices, G.traceInsideDegree K.vertices v ≤ 3) := by
  obtain ⟨K⟩ := exists_prunedCore G hc hU (low_implies_cut_lt_card G P hU.1 hlow)
    (mul_nonneg P.epsilon_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hexp
  refine ⟨K, ?_, ?_⟩
  · have hn : 1 ≤ (U.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hU.1
    have hp := Real.rpow_le_self_of_one_le hn P.p_lt_one.le
    have hb : (cutSize G U : ℝ) ≤ P.B * (U.card : ℝ) :=
      hlow.trans (mul_le_mul_of_nonneg_left hp P.B_pos.le)
    have hledger : (K.vertices.card : ℝ) + cutSize G U =
        U.card + (cutSize G K.vertices : ℝ) := by exact_mod_cast K.ledger
    have hnonnegative : (0 : ℝ) ≤ cutSize G K.vertices := Nat.cast_nonneg _
    nlinarith
  · intro v hv
    have hdeg := G.trace_degree_split K.vertices v hv
    rw [hc v (K.subset hv)] at hdeg
    omega

end Erdos1016.SafeCore
