import Erdos1016.Cycles.Selection.EvenTraceCutoffs
import Erdos1016.Decomposition.TwoCore.DeletionDeficit
import Erdos1016.Cycles.Selection.ApexGirthPacking
import Erdos1016.Decomposition.TwoCore.PhysicalCore

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The actual unsuppressed core in the few-short-cycles branch

This constructs the core as an induced physical graph, retains its original
edges, and proves the order, defect, degree and girth facts used in Section 6.
The connected protector comes from the existing finite ball-growth and
maximal-packing construction.
-/

noncomputable section
namespace Erdos1016.Proof.FewBranchCoreRealization
open Erdos1016.Nonbacktracking Erdos1016.CycleSupply Erdos1016.SafeCore
open Erdos1016.BoundaryDecay Erdos1016.Nonbacktracking.FiniteTwoCore Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def coreVertices (H : PhysicalGraph) (W : Finset H.Vertex) : Finset H.Vertex :=
  vertices H.toSimpleGraph Wᶜ

def coreGraph (H : PhysicalGraph) (W : Finset H.Vertex) : PhysicalGraph :=
  inducedPhysical H (coreVertices H W)

theorem core_order_eq (H : PhysicalGraph) (W : Finset H.Vertex) :
    (coreGraph H W).vertexCount = (coreVertices H W).card :=
  inducedPhysical_vertexCount_eq_card H _

theorem core_order_le (H : PhysicalGraph) (W : Finset H.Vertex) :
    (coreGraph H W).vertexCount ≤ H.vertexCount := by
  rw [core_order_eq]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem core_min_degree (H : PhysicalGraph) (W : Finset H.Vertex) :
    ∀ v, 2 ≤ (coreGraph H W).degree v := by
  intro w
  let e := Fintype.equivFin (Network.Shore.InsideVertex (coreVertices H W))
  let v := e.symm w
  have hd := inducedPhysical_degree_eq H (coreVertices H W) v
  have hm := vertices_minTwo H.toSimpleGraph Wᶜ v.1 v.2
  change 2 ≤ degreeWithin H.toSimpleGraph (coreVertices H W) v.1 at hm
  rw [← hd] at hm
  simpa [coreGraph, e, v] using hm

theorem core_max_degree (H : PhysicalGraph) (W : Finset H.Vertex)
    (hmax : ∀ v, H.degree v ≤ 3) : ∀ v, (coreGraph H W).degree v ≤ 3 := by
  intro w
  let e := Fintype.equivFin (Network.Shore.InsideVertex (coreVertices H W))
  let v := e.symm w
  have hd := inducedPhysical_degree_eq H (coreVertices H W) v
  have hm : degreeWithin H.toSimpleGraph (coreVertices H W) v.1 ≤ 3 := by
    calc
      _ ≤ H.toSimpleGraph.degree v.1 := degreeWithin_le_degree _ _ _
      _ = H.degree v.1 := (original_degree_eq_graph_degree H _).symm
      _ ≤ 3 := hmax _
  rw [← hd] at hm
  simpa [coreGraph, e, v] using hm

theorem core_girth (H : PhysicalGraph) (W : Finset H.Vertex) (D : ℕ)
    (hno : NoShortCycles H Wᶜ D) :
    ShortWalks.GirthGreater (coreGraph H W).toSimpleGraph D := by
  have hnoC : NoShortCycles H (coreVertices H W) D := by
    intro C hC
    exact hno C (hC.trans (vertices_subset H.toSimpleGraph Wᶜ))
  have hg := girthGreater_induce_of_noShortCycles H (coreVertices H W) D hnoC
  apply girthGreater_graphIso (inducedPhysicalGraphIso H (coreVertices H W)) D
  change ShortWalks.GirthGreater (Network.Shore.inside H.traceNetwork _).graph D
  rwa [Network.Shore.inside_graph_eq_induce, H.traceNetwork_graph]

/-- Both inequalities in the manuscript's unsuppressed-core ledger, now on
the actual induced physical core. -/
theorem core_ledger (H : PhysicalGraph) (W : Finset H.Vertex)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3) :
    (Nonbacktracking.degreeTwoCount (coreGraph H W) : ℝ) ≤
      Nonbacktracking.degreeTwoCount H + 3 * (W.card : ℝ) ∧
    (H.vertexCount : ℝ) - Nonbacktracking.degreeTwoCount H - 4 * (W.card : ℝ) ≤
      (coreGraph H W).vertexCount := by
  have hming : ∀ v, 2 ≤ H.toSimpleGraph.degree v := by
    intro v
    rw [← original_degree_eq_graph_degree]
    exact hmin v
  have hmaxg : ∀ v, H.toSimpleGraph.degree v ≤ 3 := by
    intro v
    rw [← original_degree_eq_graph_degree]
    exact hmax v
  have hb : FiniteTwoCore.degreeTwoCount H.toSimpleGraph Finset.univ =
      Nonbacktracking.degreeTwoCount H := by
    unfold FiniteTwoCore.degreeTwoCount Nonbacktracking.degreeTwoCount
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [FewDeletedCoreBudget.degreeWithin_univ_eq_degree,
      ← original_degree_eq_graph_degree]
  have hledger := FewDeletedCoreBudget.complement_twoCore_ledger H.toSimpleGraph hmaxg W
  rw [FewDeletedCoreBudget.cubicDeficit_univ_eq_degreeTwoCount
    H.toSimpleGraph hming hmaxg, hb] at hledger
  have hcore : Nonbacktracking.degreeTwoCount (coreGraph H W) =
      FiniteTwoCore.degreeTwoCount H.toSimpleGraph (coreVertices H W) :=
    inducedPhysical_degreeTwoCount_eq H _
  rw [hcore, core_order_eq]
  constructor
  · exact_mod_cast hledger.1
  · have hcard : Fintype.card H.Vertex = H.vertexCount := Fintype.card_fin _
    rw [hcard] at hledger
    exact_mod_cast hledger.2

/-- The two elementary budget inequalities that the asymptotic protector
estimate must meet imply all the core's order/defect requirements. -/
theorem core_supply_conditions (H : PhysicalGraph) (W : Finset H.Vertex) (L : ℕ)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (hn : 0 < H.vertexCount)
    (hsmall : (Nonbacktracking.degreeTwoCount H : ℝ) + 4 * (W.card : ℝ) ≤
      (H.vertexCount : ℝ) / 2)
    (hweighted : ((Nonbacktracking.degreeTwoCount H : ℝ) + 3 * (W.card : ℝ)) *
      (L : ℝ) ≤ (H.vertexCount : ℝ) / 2) :
    0 < (coreGraph H W).vertexCount ∧
      (Nonbacktracking.degreeTwoCount (coreGraph H W) : ℝ) * (L : ℝ) /
        (coreGraph H W).vertexCount ≤ 1 := by
  have hl := core_ledger H W hmin hmax
  have hnR : (0 : ℝ) < H.vertexCount := by exact_mod_cast hn
  have hcoreR : (0 : ℝ) < (coreGraph H W).vertexCount := by linarith [hl.2]
  refine ⟨by exact_mod_cast hcoreR, (div_le_one hcoreR).mpr ?_⟩
  have hm := mul_le_mul_of_nonneg_right hl.1 (Nat.cast_nonneg L)
  linarith [hl.2]

/-- Construct a connected ordinary protector containing a port and at least
`a` anchors, using only expansion and the available graph order. -/
theorem exists_initial_protector (H : PhysicalGraph) (h : ℝ) (hh : 0 < h)
    (hExp : HasExpansion H Finset.univ h) (hmax : ∀ v, H.degree v ≤ 3)
    (p₀ : CorePin H) (a : ℕ) (ha : a ≤ H.vertexCount) :
    ∃ W₀ : Finset H.Vertex, ConnectedRegion H W₀ ∧ p₀.1 ∈ W₀ ∧
      a ≤ W₀.card ∧ W₀.card ≤ 1 + a * (2 * connectorRadius H h + 1) := by
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq
    (show a ≤ (Finset.univ : Finset H.Vertex).card by simpa using ha)
  obtain ⟨W₀, hW₀, hp, hAW, hsize⟩ := connected_enlargement_logarithmic
    H h hh hExp hmax {p₀.1} (connectedRegion_singleton H p₀.1) A
  refine ⟨W₀, hW₀, hp (Finset.mem_singleton_self _), ?_, ?_⟩
  · rw [← hAc]
    exact Finset.card_le_card hAW
  · simpa [hAc] using hsize

/-- Worst-case number of deleted ordinary vertices after connecting the
initial anchors and a maximal short-cycle packing. -/
def protectorBudget (a D K R : ℕ) : ℕ := 1 + (a + D * (K - 1)) * (2 * R + 1)

/-- The actual finite few/many alternative, starting from graph expansion.
In the few case it constructs a connected protector and its physical core,
with all trace-supply hypotheses proved from the scalar deletion budget. -/
theorem many_or_few_core (H : PhysicalGraph) (h : ℝ) (hh : 0 < h)
    (hExp : HasExpansion H Finset.univ h)
    (hmin : ∀ v, 2 ≤ H.degree v) (hmax : ∀ v, H.degree v ≤ 3)
    (p₀ : CorePin H) (a D K L : ℕ) (ha : a ≤ H.vertexCount) (hK : 0 < K)
    (hsmall : (Nonbacktracking.degreeTwoCount H : ℝ) +
        4 * (protectorBudget a D K (connectorRadius H h) : ℝ) ≤ H.vertexCount / 2)
    (hweighted : ((Nonbacktracking.degreeTwoCount H : ℝ) +
        3 * (protectorBudget a D K (connectorRadius H h) : ℝ)) * (L : ℝ) ≤
      H.vertexCount / 2) :
    ∃ W₀ : Finset H.Vertex,
      ConnectedRegion H W₀ ∧ p₀.1 ∈ W₀ ∧ a ≤ W₀.card ∧
      W₀.card ≤ 1 + a * (2 * connectorRadius H h + 1) ∧
      ((∃ F ⊆ shortCycles H W₀ᶜ D, IsCyclePacking H F ∧ K ≤ F.card) ∨
        ∃ W : Finset H.Vertex, ConnectedRegion H W ∧ W₀ ⊆ W ∧
          W.card ≤ protectorBudget a D K (connectorRadius H h) ∧
          NoShortCycles H Wᶜ D ∧
          0 < (coreGraph H W).vertexCount ∧
          (Nonbacktracking.degreeTwoCount (coreGraph H W) : ℝ) * L /
            (coreGraph H W).vertexCount ≤ 1 ∧
          ShortWalks.GirthGreater (coreGraph H W).toSimpleGraph D) := by
  obtain ⟨W₀, hW₀, hp₀, haW, hsize₀⟩ := exists_initial_protector H h hh hExp hmax p₀ a ha
  refine ⟨W₀, hW₀, hp₀, haW, hsize₀, ?_⟩
  rcases short_cycle_dichotomy_connected H h hh hExp hmax W₀ hW₀ D K hK with
    hmany | ⟨W, hW, hW₀W, hsize, hno⟩
  · exact Or.inl hmany
  · right
    have hbudget : W.card ≤ protectorBudget a D K (connectorRadius H h) := by
      dsimp [protectorBudget]
      nlinarith
    have hbudgetR : (W.card : ℝ) ≤ protectorBudget a D K (connectorRadius H h) := by
      exact_mod_cast hbudget
    have hn : 0 < H.vertexCount := Fin.pos p₀.1
    have hcore := core_supply_conditions H W L hmin hmax hn
      (by linarith) (by
        have hm := mul_le_mul_of_nonneg_right (show
          (Nonbacktracking.degreeTwoCount H : ℝ) + 3 * (W.card : ℝ) ≤
            Nonbacktracking.degreeTwoCount H +
              3 * (protectorBudget a D K (connectorRadius H h) : ℝ) by linarith)
          (Nat.cast_nonneg L)
        exact hm.trans hweighted)
    exact ⟨W, hW, hW₀W, hbudget, hno, hcore.1, hcore.2, core_girth H W D hno⟩

end Erdos1016.Proof.FewBranchCoreRealization
