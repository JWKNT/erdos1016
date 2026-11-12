import Erdos1016.Cycles.Counting.LowDegreeTraceCycles
import Erdos1016.Graph.Multigraph.InducedDeletionBounds

set_option autoImplicit false

/-!
# Finite cycle supply after vertex deletion

The fixed-probability argument needs cycle weight above thirty.
The earlier retained-supply theorem assumes forest probability above one half.
This file instead uses explicit finite deficit, trace, and collision budgets.
Its conclusions concern the actual retained graph, without a forest-probability hypothesis.

The packing construction and its asymptotic budget checks remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.CycleSupply

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.SimpleRunWeight
open Erdos1016.Proof.LowDegreeTraceCycles

/-- Small deficit and spectral errors give a trace coefficient near one quarter. -/
theorem traceMass_ge_reciprocal_sum (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount)
    (M K : ℕ) (hM : 0 < M)
    (hmain : degreeDeficit G * (K : ℝ) / G.vertexCount ≤ 1 / 200)
    (herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 200) :
    (99 / 400 : ℝ) * (∑ k ∈ Finset.Icc M K, (1 : ℝ) / k) ≤
      nonbacktrackingTraceMass (G := G) (2 * K) := by
  have hnR : (0 : ℝ) < G.vertexCount := by exact_mod_cast hn
  have hd0 := degreeDeficit_nonneg G hmax
  have hδ : degreeDeficit G / (2 * G.vertexCount) < 1 / 2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * G.vertexCount)).mpr
    nlinarith
  apply le_trans ?_ (normalized_even_terms_le_traceMass G M K hM)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkpos : 0 < k := hM.trans_le (Finset.mem_Icc.mp hk).1
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hMk : M ≤ k := (Finset.mem_Icc.mp hk).1
  have hbern := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ -(degreeDeficit G / (2 * G.vertexCount)) by linarith) (2 * k)
  have hbudget : degreeDeficit G * (k : ℝ) / G.vertexCount ≤ 1 / 200 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkK hd0) hnR.le).trans hmain
  have hlead : (199 / 200 : ℝ) ≤
      (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) := by
    push_cast at hbern
    have heq : 1 + (2 * (k : ℝ)) * -(degreeDeficit G / (2 * G.vertexCount)) =
        1 - degreeDeficit G * (k : ℝ) / G.vertexCount := by ring
    rw [heq] at hbern
    change _ ≤ (1 - degreeDeficit G / (2 * G.vertexCount)) ^ (2 * k) at hbern
    linarith
  have herrk : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ k ≤ 1 / 200 := by
    apply le_trans ?_ herr
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hMk
  have htrace := DeficitTrace.normalized_even_trace_lower G hmax hn hd k hkpos
  have hnormalized : (99 / 100 : ℝ) ≤
      Matrix.trace ((matrix G : Matrix _ _ ℝ) ^ (2 * k)) / (2 : ℝ) ^ (2 * k) := by
    linarith
  calc
    (99 / 400 : ℝ) * (1 / (k : ℝ)) = (99 / 100 : ℝ) / (4 * k) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hnormalized (by positivity)

/-- The trace bound and collision estimate give actual simple-cycle mass. -/
theorem cycleWordMass_ge_log_ratio (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount)
    (M K s D : ℕ) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hmain : degreeDeficit G * (K : ℝ) / G.vertexCount ≤ 1 / 200)
    (herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 200)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (hcollision : (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 100) :
    (9801 / 40000 : ℝ) * Real.log ((K + 1 : ℕ) / (M : ℝ)) ≤
      ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength G ell := by
  have hlog := log_ratio_le_reciprocal_sum M K hM hMK
  have htrace := traceMass_ge_reciprocal_sum G hmax hn hd M K hM hmain herr
  have hcycle := Erdos1016.Proof.TraceCycleMass.cycleWordMass_sum_ge_one_sub_collisionError_of_max_degree
    G (2 * K) s D hmax hg hshort hs
  have hmass0 : 0 ≤ nonbacktrackingTraceMass (G := G) (2 * K) := by
    unfold nonbacktrackingTraceMass
    positivity
  have hnear : (99 / 100 : ℝ) * nonbacktrackingTraceMass (G := G) (2 * K) ≤
      ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength G ell := by
    have h := mul_le_mul_of_nonneg_right
      (show (99 / 100 : ℝ) ≤ 1 - (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ s by linarith) hmass0
    exact h.trans hcycle
  linarith

/-- A fixed logarithmic interval suffices for the good-row mass requirement. -/
theorem cycleWordMass_gt_thirty (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount)
    (M K s D : ℕ) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hmain : degreeDeficit G * (K : ℝ) / G.vertexCount ≤ 1 / 200)
    (herr : 3 * (G.vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 200)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (hcollision : (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 100)
    (hlog : 123 ≤ Real.log ((K + 1 : ℕ) / (M : ℝ))) :
    30 < ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength G ell := by
  have h := cycleWordMass_ge_log_ratio G hmax hn hd M K s D hM hMK
    hmain herr hg hshort hs hcollision
  linarith

/-- This adapter supplies mass in the actual graph left after deleting `P ∪ S`.
The two deleted sets may overlap. The retained graph may be disconnected. -/
theorem retained_cycleWordMass_gt_thirty
    (G : FiniteMultiGraph) (P S : Finset G.Vertex)
    (hloop : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ, G.src e ≠ G.dst e)
    (hsimple : ∀ e ∈ G.internalEdges (P ∪ S)ᶜ,
      ∀ f ∈ G.internalEdges (P ∪ S)ᶜ,
      ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
        (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (M K s D : ℕ) (hM : 0 < M) (hMK : M ≤ K + 1)
    (hn : 0 < (FiniteMultiGraph.InducedSimpleRealization.graph
      G (P ∪ S)ᶜ hloop hsimple).vertexCount)
    (hd : 3 * ((P ∪ S).card : ℝ) < (FiniteMultiGraph.InducedSimpleRealization.graph
      G (P ∪ S)ᶜ hloop hsimple).vertexCount)
    (hmain : 3 * ((P ∪ S).card : ℝ) * (K : ℝ) /
      (FiniteMultiGraph.InducedSimpleRealization.graph G (P ∪ S)ᶜ hloop hsimple).vertexCount ≤
        1 / 200)
    (herr : 3 * ((FiniteMultiGraph.InducedSimpleRealization.graph
      G (P ∪ S)ᶜ hloop hsimple).vertexCount : ℝ) / (2 : ℝ) ^ M ≤ 1 / 200)
    (hg : ShortWalks.GirthGreater (FiniteMultiGraph.InducedSimpleRealization.graph
      G (P ∪ S)ᶜ hloop hsimple).toSimpleGraph D)
    (hshort : 2 * s ≤ D) (hs : 0 < s)
    (hcollision : (9 / 4 : ℝ) * ((2 * K : ℕ) : ℝ) ^ 2 *
      (1 / 2 : ℝ) ^ s ≤ 1 / 100)
    (hlog : 123 ≤ Real.log ((K + 1 : ℕ) / (M : ℝ))) :
    30 < ∑ ell ∈ Finset.Icc 1 (2 * K), cycleWordMassAtLength
      (FiniteMultiGraph.InducedSimpleRealization.graph G (P ∪ S)ᶜ hloop hsimple) ell := by
  classical
  let J := FiniteMultiGraph.InducedSimpleRealization.graph G (P ∪ S)ᶜ hloop hsimple
  have hJmax := FiniteMultiGraph.InducedSimpleRealization.max_degree_three
    G (P ∪ S)ᶜ hloop hsimple hmax
  have hdle := FiniteMultiGraph.InducedSimpleRealization.degreeDeficit_le_deleted
    G (P ∪ S)ᶜ hloop hsimple hmax (fun v hv => hcubic v (by
      have hv' := Finset.mem_compl.mp hv
      exact fun hp => hv' (Finset.mem_union_left S hp)))
  simp only [compl_compl] at hdle
  have hdJ : degreeDeficit J < J.vertexCount := hdle.trans_lt hd
  have hmainJ : degreeDeficit J * (K : ℝ) / J.vertexCount ≤ 1 / 200 := by
    apply le_trans ?_ hmain
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hdle (by positivity)
  exact cycleWordMass_gt_thirty J hJmax hn hdJ M K s D hM hMK
    hmainJ herr hg hshort hs hcollision hlog

end Erdos1016.ExactMaximumSupport.LargeGirth.CycleSupply
