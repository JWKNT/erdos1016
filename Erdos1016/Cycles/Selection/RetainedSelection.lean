import Erdos1016.Probability.Avoidance.PackingRate
import Erdos1016.Cycles.Geometry.InducedCycleEmbedding

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter
open scoped Topology
namespace Erdos1016.Proof.FewBranchSelectedCycles
open Nonbacktracking CycleSupply SafeCore BoundaryDecay
open FewBranchCoreRealization EvenTraceParameters CutoffAvoidance
open ProtectorParameterBounds ProtectorCoreDichotomy PhysicalCycleEmbedding
open CutoffLimits
open ConnectorCutoffLimits
open RejectedCycleEncoding ExternalReturnFilter

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Concrete output of the few branch. Its existence below is proved from
the original expansion and degree hypotheses. -/
structure Selection (H : PhysicalGraph) (p₀ : CorePin H) (c σ n : ℝ) where
  W : Finset H.Vertex
  connected : ConnectedRegion H W
  port_mem : p₀.1 ∈ W
  large : ((momentK σ (Real.logb 2 n) : ℝ) * cutoffL σ (Real.logb 2 n)) /
    ((c * n ^ (-(1 / 8 : ℝ))) / 2) < W.card
  room : ((momentK σ (Real.logb 2 n) : ℝ) * cutoffL σ (Real.logb 2 n)) +
    ((momentK σ (Real.logb 2 n) : ℝ) * cutoffL σ (Real.logb 2 n)) /
      ((c * n ^ (-(1 / 8 : ℝ))) / 2) < H.vertexCount + 1
  size : W.card ≤ protectorBudget (anchorCount c σ n) (logarithmicGirthCutoff n)
    (polynomialPackingCutoff n) (logarithmicConnectorRadius c n)
  no_short : NoShortCycles H Wᶜ (cutoffD (Real.logb 2 n))
  coreCycles : Finset (coreGraph H W).CycleWord
  retained : coreCycles ⊆ acceptedShortReturnCycles (coreGraph H W) Finset.univ
    (shortCycleWords (coreGraph H W) (cutoffL σ (Real.logb 2 n))) (cutoffQ σ (Real.logb 2 n))
  core_induced : ∀ C ∈ coreCycles, Cycle.IsInduced C
  mean_lower : evenTraceTarget σ (Real.logb 2 n) ≤ cycleWeightSum coreCycles
  mean_upper : cycleWeightSum coreCycles ≤ evenTraceTarget σ (Real.logb 2 n) +
    1 / (2 : ℝ) ^ (cutoffD (Real.logb 2 n) + 1)

variable {H : PhysicalGraph} {p₀ : CorePin H} {c σ n : ℝ}

def Selection.embedding (S : Selection H p₀ c σ n) : Embedding (coreGraph H S.W) (coreApexGraph H) :=
  (induced H (coreVertices H S.W)).comp (apex H)

def Selection.cycles (S : Selection H p₀ c σ n) : Finset (coreApexGraph H).CycleWord :=
  S.embedding.liftFamily S.coreCycles

theorem Selection.mean_bounds (S : Selection H p₀ c σ n) :
    evenTraceTarget σ (Real.logb 2 n) ≤ cycleWeightSum S.cycles ∧
      cycleWeightSum S.cycles ≤ evenTraceTarget σ (Real.logb 2 n) +
        1 / (2 : ℝ) ^ (cutoffD (Real.logb 2 n) + 1) := by
  unfold Selection.cycles
  rw [S.embedding.liftFamily_weight]
  exact ⟨S.mean_lower, S.mean_upper⟩

theorem Selection.cycle_length_bounds (S : Selection H p₀ c σ n)
    (C : (coreApexGraph H).CycleWord) (hC : C ∈ S.cycles) :
    cutoffD (Real.logb 2 n) < BoundaryDecay.Cycle.length C ∧
      BoundaryDecay.Cycle.length C ≤ cutoffL σ (Real.logb 2 n) := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
  rw [S.embedding.liftCycle_length]
  constructor
  · exact QuantitativeRetainedSupply.cycle_length_gt_of_girth _ _ (core_girth H S.W _ S.no_short) A
  · have hret := (mem_acceptedShortReturnCycles _ _ _ _ A).mp (S.retained hA)
    exact (Finset.mem_filter.mp hret.1).2

theorem Selection.protector_connected (S : Selection H p₀ c σ n) :
    ConnectedRegion (coreApexGraph H) (apexProtector H S.W) :=
  apexProtector_connected H S.connected p₀ S.port_mem

theorem Selection.cycle_avoids_protector (S : Selection H p₀ c σ n)
    (C : (coreApexGraph H).CycleWord) (hC : C ∈ S.cycles) :
    Cycle.vertices C ⊆ (apexProtector H S.W)ᶜ := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
  rw [S.embedding.liftCycle_vertices]
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  have hcore : (induced H (coreVertices H S.W)).vertex u ∈ coreVertices H S.W :=
    induced_vertex_mem H _ u
  have hout : (induced H (coreVertices H S.W)).vertex u ∈ S.Wᶜ :=
    FiniteTwoCore.vertices_subset H.toSimpleGraph S.Wᶜ hcore
  apply Finset.mem_compl.mpr
  intro hin
  change coreVertexLift H ((induced H (coreVertices H S.W)).vertex u) ∈
    insert (coreApexVertex H) (liftCoreRegion H S.W) at hin
  rcases Finset.mem_insert.mp hin with hz | hin
  · exact coreVertex_ne_apex H _ hz
  · obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hin
    have hw' := coreVertexLift_injective H heq
    exact (Finset.mem_compl.mp hout) (hw' ▸ hw)

/-- Both physical embeddings reflect adjacency, so the chord rejection in
the actual retained core family survives in the one-apex owner. -/
theorem Selection.cycle_induced (S : Selection H p₀ c σ n)
    (C : (coreApexGraph H).CycleWord) (hC : C ∈ S.cycles) : Cycle.IsInduced C := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC
  apply S.embedding.liftCycle_induced _ A (S.core_induced A hA)
  intro u v huv
  apply (induced_adj_iff H (coreVertices H S.W) u v).mpr
  apply apex_adj_reflect H
  exact huv

/-- Uniform original graph hypotheses now yield either the required decay
itself, or a concrete selected cycle family in the actual apex owner. -/
theorem eventually_decay_or_selection
    (c B σ : ℝ) (hc : 0 < c) (hB : 0 < B) (hσ : 0 < σ) (hσ20 : σ < 1 / 20)
    (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) (hnge : ∀ j, 1 ≤ n j) :
    ∀ᶠ j in atTop, ∀ (H : PhysicalGraph) (p₀ : CorePin H),
      (H.vertexCount : ℝ) = n j → H.IsConnected →
      (∀ v, 2 ≤ H.degree v) → (∀ v, H.degree v ≤ 3) →
      HasExpansion H Finset.univ (c * (n j) ^ (-(1 / 8 : ℝ))) →
      (Nonbacktracking.degreeTwoCount H : ℝ) ≤ B * (n j) ^ (7 / 8 : ℝ) →
      coreBoundaryAverage H ≤ (2 : ℝ) ^ (-(σ / 128) * Real.sqrt (Real.logb 2 (n j))) ∨
        Nonempty (Selection H p₀ c σ (n j)) := by
  filter_upwards [eventually_many_bound_or_selected_core c B σ hc hB hσ hσ20 n hn hnge,
    ManyCycleRate.manyBound_le_stretched_eventually c (σ / 128) hc (by positivity) n hn]
    with j hj hr
  intro H p₀ hnH hH hmin hmax hExp hb
  obtain ⟨W₀, hW₀, hp, hlarge, hroom, hm | ⟨W, hW, hsub, hno, hsize, F, hF, hlo, hhi⟩⟩ :=
    hj H p₀ hnH hH hmin hmax hExp hb
  · exact Or.inl (hm.trans hr)
  · right
    have hcW : (W₀.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_le_card hsub
    exact ⟨{
      W := W
      connected := hW
      port_mem := hsub hp
      large := hlarge.trans_le hcW
      room := hroom
      size := hsize
      no_short := hno
      coreCycles := F
      retained := fun C hC => (Finset.mem_filter.mp (hF hC)).1
      core_induced := fun C hC => (Finset.mem_filter.mp (hF hC)).2
      mean_lower := hlo
      mean_upper := hhi }⟩

end Erdos1016.Proof.FewBranchSelectedCycles
