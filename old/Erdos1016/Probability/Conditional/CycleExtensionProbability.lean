import Erdos1016.Probability.Moments.CycleEvents

set_option autoImplicit false

/-!
# Conditional probability of a new cycle after a fixed cycle tuple

This isolates the exact finite probability calculation behind the Section 7
conditional-cycle estimate.  The graph-specific estimate of the residual
rank drop is deliberately a separate premise.
-/

noncomputable section
namespace Erdos1016.Proof.CycleExtensionProbability

open Erdos1016.BoundaryDecay
open Erdos1016.BoundaryTrace
open Erdos1016.SafeCore

local instance conditionalNeighborDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance conditionalNeighborCycleWordDecidableEq (G : PhysicalGraph) :
    DecidableEq G.CycleWord := Classical.decEq _
local instance conditionalNeighborOutsideVertexFintype (G : PhysicalGraph)
    (S : Finset G.Vertex) : Fintype (Network.Shore.OutsideVertex S) :=
  Network.Shore.outsideVertexFintype G.traceNetwork S
local instance conditionalNeighborOutsideEdgeFintype (G : PhysicalGraph)
    (S : Finset G.Vertex) : Fintype (Network.Shore.OutsideEdge G.traceNetwork S) :=
  Network.Shore.outsideEdgeFintype G.traceNetwork S

variable {G : PhysicalGraph}

def tupleVertices (F : Finset G.CycleWord) : Finset G.Vertex :=
  F.biUnion Cycle.vertices

def tupleSeed (F : Finset G.CycleWord) : G.CycleSpace :=
  ∑ C ∈ F, Cycle.seed C

def tupleEvent (F : Finset G.CycleWord) (x : G.CycleSpace) : Prop :=
  ∀ C ∈ F, Cycle.Event C x

def conditionalDensity {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) : ℝ :=
  Finite.density (fun x => P x ∧ Q x) / Finite.density P

private theorem density_congr {Ω : Type*} [Fintype Ω]
    (P Q : Ω → Prop) (hPQ : ∀ x, P x ↔ Q x) :
    Finite.density P = Finite.density Q := by
  unfold Finite.density Finite.count
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp [hPQ x]

private theorem tupleEvent_iff_forcedRegion
    (F : Finset G.CycleWord) (x : G.CycleSpace)
    (hdisj : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      Disjoint (Cycle.vertices C) (Cycle.vertices D)) :
    tupleEvent F x ↔
      ForcedRegion G.traceNetwork (tupleVertices F)
        (tupleSeed F).1 x.1 := by
  constructor
  · intro hx e he
    rcases he with hs | hd
    · obtain ⟨C, hC, hsC⟩ := Finset.mem_biUnion.mp hs
      have hsum : (∑ D ∈ F, (Cycle.seed D).1 e) = (Cycle.seed C).1 e := by
        rw [Finset.sum_eq_single C]
        · intro D hD hDC
          exact Cycle.word_zero_at_disjoint_incidence C D
            (hdisj C hC D hD hDC.symm) e (Or.inl hsC)
        · intro hnot
          exact (hnot hC).elim
      have hword : (tupleSeed F).1 e = ∑ D ∈ F, (Cycle.seed D).1 e := by
        simp [tupleSeed]
      rw [hword, hsum]
      exact hx C hC e (Or.inl hsC)
    · obtain ⟨C, hC, hdC⟩ := Finset.mem_biUnion.mp hd
      have hsum : (∑ D ∈ F, (Cycle.seed D).1 e) = (Cycle.seed C).1 e := by
        rw [Finset.sum_eq_single C]
        · intro D hD hDC
          exact Cycle.word_zero_at_disjoint_incidence C D
            (hdisj C hC D hD hDC.symm) e (Or.inr hdC)
        · intro hnot
          exact (hnot hC).elim
      have hword : (tupleSeed F).1 e = ∑ D ∈ F, (Cycle.seed D).1 e := by
        simp [tupleSeed]
      rw [hword, hsum]
      exact hx C hC e (Or.inr hdC)
  · intro hx C hC e he
    have hsum : (∑ D ∈ F, (Cycle.seed D).1 e) = (Cycle.seed C).1 e := by
      rw [Finset.sum_eq_single C]
      · intro D hD hDC
        exact Cycle.word_zero_at_disjoint_incidence C D
          (hdisj C hC D hD hDC.symm) e he
      · intro hnot
        exact (hnot hC).elim
    have hword : (tupleSeed F).1 e = ∑ D ∈ F, (Cycle.seed D).1 e := by
      simp [tupleSeed]
    have h := hx e (by
      rcases he with hs | hd
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨C, hC, hs⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨C, hC, hd⟩))
    rw [hword, hsum] at h
    exact h

private theorem tupleEvent_insert_iff
    (F : Finset G.CycleWord) (D : G.CycleWord) (x : G.CycleSpace) :
    tupleEvent (insert D F) x ↔ tupleEvent F x ∧ Cycle.Event D x := by
  simp [tupleEvent, and_comm]

/-- Exact conditional event probability after fixing a vertex-disjoint tuple.
The rank terms are the cycle-space dimensions of the two residual exterior
networks.  This is the smallest exposed-port interface: to obtain the paper's
`2^{-t_U(D)}` upper bound, it remains to prove a rank drop of at least the
number of effective degree-three ports in the residual two-core. -/
theorem conditional_cycle_probability_eq_residual_rank_ratio
    (F : Finset G.CycleWord) (D : G.CycleWord)
    (hFdisj : ∀ C : G.CycleWord, C ∈ F → ∀ E : G.CycleWord, E ∈ F → C ≠ E →
      Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hFDdisj : ∀ C : G.CycleWord, C ∈ F →
      Disjoint (Cycle.vertices C) (Cycle.vertices D)) :
    conditionalDensity (tupleEvent F) (Cycle.Event D) =
      dyadic (((networkRank (Network.Shore.outside G.traceNetwork
          (tupleVertices (insert D F))) : ℕ) : ℤ) -
        ((networkRank (Network.Shore.outside G.traceNetwork
          (tupleVertices F)) : ℕ) : ℤ)) := by
  classical
  have hdisjInsert : ∀ C ∈ insert D F, ∀ E ∈ insert D F, C ≠ E →
      Disjoint (Cycle.vertices C) (Cycle.vertices E) := by
    intro C hC E hE hCE
    rcases Finset.mem_insert.mp hC with rfl | hCF
    · rcases Finset.mem_insert.mp hE with rfl | hEF
      · exact (hCE rfl).elim
      · exact (hFDdisj E hEF).symm
    · rcases Finset.mem_insert.mp hE with rfl | hEF
      · exact hFDdisj C hCF
      · exact hFdisj C hCF E hEF hCE
  have hden : 0 < forcedProbability G (tupleVertices F) (tupleSeed F) := by
    rw [forcedProbability_eq_network, forced_region_probability_dyadic]
    exact dyadic_pos _
  have hnumEvent :
      (fun x : G.CycleSpace => tupleEvent F x ∧ Cycle.Event D x) =
        tupleEvent (insert D F) := by
    funext x
    exact propext (tupleEvent_insert_iff F D x).symm
  have hdenEvent :
      Finite.density (tupleEvent F) =
        forcedProbability G (tupleVertices F) (tupleSeed F) := by
    unfold forcedProbability
    exact density_congr _ _ (tupleEvent_iff_forcedRegion F · hFdisj)
  have hnumEventProb :
      Finite.density (fun x : G.CycleSpace =>
        tupleEvent F x ∧ Cycle.Event D x) =
        forcedProbability G (tupleVertices (insert D F))
          (tupleSeed (insert D F)) := by
    rw [hnumEvent]
    unfold forcedProbability
    exact density_congr _ _
      (tupleEvent_iff_forcedRegion (insert D F) · hdisjInsert)
  have hdenRank : forcedProbability G (tupleVertices F) (tupleSeed F) =
      dyadic (((networkRank (Network.Shore.outside G.traceNetwork
        (tupleVertices F)) : ℕ) : ℤ) - (networkRank G.traceNetwork : ℤ)) := by
    rw [forcedProbability_eq_network, forced_region_probability_dyadic]
  have hnumRank : forcedProbability G (tupleVertices (insert D F))
      (tupleSeed (insert D F)) =
      dyadic (((networkRank (Network.Shore.outside G.traceNetwork
        (tupleVertices (insert D F))) : ℕ) : ℤ) -
        (networkRank G.traceNetwork : ℤ)) := by
    rw [forcedProbability_eq_network, forced_region_probability_dyadic]
  unfold conditionalDensity
  rw [hnumEventProb, hdenEvent, hnumRank, hdenRank]
  rw [← dyadic_sub]
  congr 1
  omega

/-- Rank drop on exposing the candidate cycle gives the paper's conditional
probability bound.  The graph-theoretic input is deliberately isolated as the
rank-drop hypothesis. -/
theorem conditional_cycle_probability_le_of_residual_rank_drop
    (F : Finset G.CycleWord) (D : G.CycleWord) (t : ℕ)
    (hFdisj : ∀ C : G.CycleWord, C ∈ F → ∀ E : G.CycleWord, E ∈ F → C ≠ E →
      Disjoint (Cycle.vertices C) (Cycle.vertices E))
    (hFDdisj : ∀ C : G.CycleWord, C ∈ F →
      Disjoint (Cycle.vertices C) (Cycle.vertices D))
    (hrank : ((networkRank (Network.Shore.outside G.traceNetwork
        (tupleVertices (insert D F))) : ℕ) : ℤ) + t ≤
      ((networkRank (Network.Shore.outside G.traceNetwork
        (tupleVertices F)) : ℕ) : ℤ)) :
    conditionalDensity (tupleEvent F) (Cycle.Event D) ≤
      1 / (2 : ℝ) ^ t := by
  rw [conditional_cycle_probability_eq_residual_rank_ratio F D hFdisj hFDdisj]
  rw [← dyadic_neg_nat]
  apply dyadic_mono
  omega

end Erdos1016.Proof.CycleExtensionProbability

end
