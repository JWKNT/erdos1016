import Erdos1016.Cleanup.Support.WitnessInputData
import Erdos1016.Cleanup.Support.LargeActiveComponent
import Erdos1016.Cleanup.Support.TrimmedWitnessComponentEquivalence
import Erdos1016.Extremal.Capacity.HighCycleOutsideRank

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.CanonicalWitnessInput

open Erdos1016
open Erdos1016.Extremal
open Erdos1016.Proof.Capacity
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.WitnessInputData
open Erdos1016.Proof.VertexSupportedWitness

private theorem scale_le_exp (R C : ℕ) (hR : 6 ≤ R) (hC : 8 ≤ C) :
    8 * R + 1 ≤ C * R ^ 4 := by
  have hRpos : 1 ≤ R := by omega
  have hR4 : R ≤ R ^ 4 := by
    calc R = R ^ 1 := by simp
      _ ≤ R ^ 4 := Nat.pow_le_pow_right hRpos (by omega)
  have hR4gap : R + 1 ≤ R ^ 4 := by
    have hpow : R ^ 2 ≤ R ^ 4 := Nat.pow_le_pow_right hRpos (by omega)
    nlinarith
  have h1 : 8 * R ≤ 8 * R ^ 4 := Nat.mul_le_mul_left 8 hR4
  have h2 : 8 * R ^ 4 ≤ C * R ^ 4 := Nat.mul_le_mul_right (R ^ 4) hC
  have hgap : 8 * R + 1 ≤ 8 * R ^ 4 := by omega
  omega

private theorem rank_large_of_scale (R C s r : ℕ) (hR : 6 ≤ R)
    (hC : 8 ≤ C) (hscale : 2 ^ (C * R ^ 4) ≤ s)
    (hnear : s ≤ r + (R + 1)) : 2 ^ (8 * R) ≤ r := by
  have hexp := scale_le_exp R C hR hC
  have hp : 2 ^ (8 * R + 1) ≤ 2 ^ (C * R ^ 4) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hp' : 2 ^ (8 * R + 1) ≤ s := hp.trans hscale
  have hsucc : 8 * R + 1 ≤ 2 ^ (8 * R) := succ_le_two_pow (8 * R)
  have hlin : R + 1 ≤ 2 ^ (8 * R) := by omega
  have hsum : 2 ^ (8 * R) + (R + 1) ≤ 2 ^ (8 * R + 1) := by
    rw [pow_succ]
    omega
  omega

/-- Construct the canonical short-cycle witness data before connecting the
ambient graph. The high-cycle count and scale hypotheses supply the actual
large-rank field, and the fixed canonical witness is retained verbatim. -/
theorem canonical_cleanupWitnessData
    (G : PhysicalGraph) (R C s : ℕ)
    (hR : 6 ≤ R) (hC : 8 ≤ C)
    (hscale : 2 ^ (C * R ^ 4) ≤ s)
    (_hrankUpper : G.cycleRank ≤ s)
    (hcov : G.InitialCoverage (2 ^ (2 * R) + 1))
    (hcount : tailCapacity R / 2 ≤
      (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ s)
    (hprob : (1 / 2 : ℝ) + 1 / (R : ℝ) <
      G.outsideLinearForestProbability
        (witnessSupportEdges G
          (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov))) :
    ∃ I : WitnessData G, I.R = R ∧ I.r = G.cycleRank ∧
      I.witnessEdges = witnessSupportEdges G
        (canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov) := by
  classical
  let F := canonicalCycleWitnesses G (2 ^ (2 * R) + 1) hcov
  let W := witnessSupportEdges G F
  let V := witnessSupportVertices G F
  have hnear := HighCycleOutsideRank.rank_ge_of_high_cycle_count G R s (by omega) hcount
  have hrank : 2 ^ (8 * R) ≤ G.cycleRank :=
    rank_large_of_scale R C s G.cycleRank hR hC hscale hnear
  have hbudget := canonicalWitnessSupport_add_one_le_power G R (by omega) hcov
  have hscreenCount :
      tailCapacity R / 2 ≤ (G.cycleLengths.card : ℝ) / (2 : ℝ) ^ G.cycleRank := by
    have hpow : (2 : ℝ) ^ G.cycleRank ≤ (2 : ℝ) ^ s := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) _hrankUpper
    exact hcount.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)
  have h5R : 5 * R + 2 ≤ 2 ^ (8 * R) := by
    have ht := succ_le_two_pow (8 * R)
    omega
  have hscreen := LargeActiveComponent.canonical_trimmed_component_screen
    G R hR (by omega : 5 * R + 2 ≤ G.cycleRank) hcov hscreenCount
  have hvertices : V.card ≤ W.card := by
    have ht := trimmed_vertexCount_le_edgeCount G F
    simpa [V, W, trimmedWitnessGraph_vertexCount, trimmedWitnessGraph_edgeCount] using ht
  have hnonempty : W.Nonempty := by
    have h3L : 3 ≤ 2 ^ (2 * R) + 1 := by
      have hp : 2 ≤ 2 ^ (2 * R) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨C3, hC3, hlen⟩ := canonicalCycleWitnesses_has_all_lengths G
      (2 ^ (2 * R) + 1) hcov 3 (by omega) h3L
    have hword : ∃ e, C3.1 e ≠ 0 := by
      classical
      have hn := C3.2.1
      by_contra hx
      apply hn
      funext e
      have he := not_exists.mp hx e
      exact not_ne_iff.mp he
    obtain ⟨e, he⟩ := hword
    have hem : e ∈ G.edgeSupport C3.1 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    exact ⟨e, witnessSupport_edge_mem G F hC3 hem⟩
  have hendpoints : ∀ e ∈ W, G.src e ∈ V ∧ G.dst e ∈ V := by
    intro e he
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, Or.inl rfl⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, Or.inr rfl⟩⟩
  have hexact : ∀ v, v ∈ V ↔ ∃ e ∈ W, G.src e = v ∨ G.dst e = v := by
    intro v
    simp [V, W, witnessSupportVertices, PhysicalGraph.incident]
  have hactive : ∀ e ∈ W, ActiveEdge G e := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨C, hC, heC⟩
    refine ⟨⟨C.1, ?_⟩, (Finset.mem_filter.mp heC).2⟩
    change G.boundary C.1 = 0
    exact C.2.2.1
  have hcomponent : witnessComponentCount G V W < 5 * R := by
    rw [TrimmedWitnessComponentEquivalence.witnessComponentCount_eq_trimmed]
    simpa [F] using hscreen
  refine ⟨{
    R := R, r := G.cycleRank, witnessEdges := W, witnessVertices := V,
    rank_large := hrank,
    graph_rank := rfl,
    witness_nonempty := hnonempty,
    witness_endpoints := hendpoints,
    witness_vertices_exact := hexact,
    witness_edges_active := hactive,
    vertices_le_edges := hvertices,
    witness_edges_budget := ?_,
    witness_components := hcomponent,
    outside_probability := ?_ }, ?_, ?_, rfl⟩
  · simpa [W, F, witnessSupportGraph, witnessSupportEdges] using hbudget
  · simpa [W, F] using hprob
  · rfl
  · rfl



end Erdos1016.Proof.CanonicalWitnessInput

end
