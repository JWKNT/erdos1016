import Erdos1016.Cleanup.Root.CutBudgetExtractionProfile
import Erdos1016.Cleanup.Root.OutsideComponentRoot
import Erdos1016.Cleanup.Protection.ActiveComponentSurvival

set_option autoImplicit false

/-!
# Root extraction retaining the original graph's rank scale

The selected active component need carry only `r/(5R)` rank. Its rank need
not satisfy the original graph's exponential lower bound. Accounting for
this loss before component averaging preserves the required bound in terms
of the original `r`.
-/

noncomputable section

namespace Erdos1016.Proof.ActiveRankExtraction

open Erdos1016
open CleanupSpecification ComponentExtraction
open ProtectedDeletionRankLedger OutsideComponentPartitions
open CutBudgetExtractionProfile
open OutsideComponentRoot
open ActiveComponentSurvival
open ProtectedExteriorComponents

/-- The active rank share and a half-share deletion budget leave `r/(10R)`
rank in the actual components outside the protected vertices. -/
theorem outside_rank_sum_lower_of_active_share
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (r R : ℕ) (hR : 0 < R)
    (hshare : r ≤ 5 * R * Γ.cycleRank)
    (hbudget : 10 * R * (protectedIncidentEdges Γ P).card ≤ r) :
    (r : ℝ) / (10 * R) ≤
      ∑ c : OutsideComponent Γ P, (outsideComponentRank Γ P c : ℝ) := by
  classical
  letI : Fintype (OutsideComponent Γ P) := SetLike.instFintype
  have hvertices := sum_outside_component_vertex_card Γ P
  have hedges :
      (∑ c : OutsideComponent Γ P,
        (internalEdges Γ (outsideComponentVertices Γ P c)).card) =
          (unprotectedEdges Γ P).card := by
    rw [sum_outside_component_internal_edge_card]
    congr 1
    ext e
    simp [unprotectedEdges, internalEdges, Finset.mem_compl]
  have hsum := outside_rank_sum_lower_of_partition
    (fun c => componentInternalGraph_connected Γ P c) hconn hP hvertices hedges
  have hshare' : r ≤ 5 * R *
      ((∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) +
        (protectedIncidentEdges Γ P).card) :=
    hshare.trans (Nat.mul_le_mul_left (5 * R) hsum)
  have hmain : r ≤ 10 * R *
      (∑ c : OutsideComponent Γ P, outsideComponentRank Γ P c) := by
    nlinarith
  have hmain' : (r : ℝ) ≤ (10 * R : ℝ) *
      (∑ c : OutsideComponent Γ P, (outsideComponentRank Γ P c : ℝ)) := by
    exact_mod_cast hmain
  have hden : (0 : ℝ) < 10 * R := by positivity
  exact (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hmain')

/-- Choose the actual simple cubic root using the original global rank.
Existence of a surviving component is derived from the same deletion budget.
No assumption that the selected component itself has rank at least `2^(8R)`
is needed. -/
theorem exists_cleanup_root_of_active_share
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (R r A B₃ m₂ Cext n : ℕ)
    (hcubic : ∀ v, v ∉ P → ambientDegree Γ v = 3)
    (hshare : r ≤ 5 * R * Γ.cycleRank)
    (hbudget : 10 * R * (protectedIncidentEdges Γ P).card ≤ r)
    (hcutP : (cutEdges Γ P).card ≤ A)
    (hnoLoop : ∀ e : Γ.Edge, Γ.src e ∉ P → Γ.dst e ∉ P →
      Γ.src e ≠ Γ.dst e)
    (hnoParallel : ∀ e f : Γ.Edge,
      Γ.src e ∉ P → Γ.dst e ∉ P → Γ.src f ∉ P → Γ.dst f ∉ P →
      (((Γ.src e = Γ.src f ∧ Γ.dst e = Γ.dst f) ∨
        (Γ.src e = Γ.dst f ∧ Γ.dst e = Γ.src f))) → e = f)
    (hRpos : 0 < R) (hApos : 0 < A)
    (hr : 2 ^ (8 * R) ≤ r)
    (hscale : 10 * R * A ≤ 2 ^ (8 * R))
    (hAbound : A ≤ 2 ^ (5 * R))
    (K : SimpleGraph Γ.Vertex) (Aset B C : Finset Γ.Vertex)
    (hAset : Aset ⊆ P) (hPcover : P ⊆ Aset ∪ B ∪ C)
    (hAdj : ∀ u v, K.Adj u v → Γ.toSimpleGraph.Adj u v)
    (hcore : Fintype.card (K.induce (↑Aset : Set Γ.Vertex)).ConnectedComponent ≤ n)
    (hn : n < 5 * R) (hB : B.card < B₃ * R)
    (hC : C.card < 2 * m₂ * R ^ 2) (hR : 1 ≤ R)
    (hconst : 5 + B₃ + 2 * m₂ ≤ Cext) :
    ∃ c : OutsideComponent Γ P,
      0 < outsideComponentRank Γ P c ∧
      IsCleanupRoot Γ (outsideComponentVertices Γ P c) ∧
      (outsideComponentVertices Γ P c).card < Γ.vertexCount ∧
      (∀ v ∈ outsideComponentVertices Γ P c, ambientDegree Γ v = 3) ∧
      r ≤ (outsideComponentVertices Γ P c).card * 2 ^ (8 * R) ∧
      (cutEdges Γ (outsideComponentVertices Γ P c)).card ≤ 2 ^ (5 * R) ∧
      exteriorComponentCount Γ (outsideComponentVertices Γ P c) ≤ Cext * R ^ 2 := by
  have hrpos : 0 < r := (Nat.two_pow_pos _).trans_le hr
  have hstrict : (protectedIncidentEdges Γ P).card < Γ.cycleRank := by
    nlinarith
  obtain ⟨c₀, hc₀⟩ := exists_positive_rank_outsideComponent_of_strict_rank_budget
    Γ P hconn hP hstrict
  have hnonempty : Nonempty (OutsideComponent Γ P) := ⟨c₀⟩
  let profile := profileOfProtectedCutBudget Γ P r R A hconn hP hcubic
    (outside_rank_sum_lower_of_active_share Γ P hconn hP r R hRpos hshare hbudget) hcutP
  obtain ⟨c, hpositive, hproper, horder, hcut, hexterior⟩ :=
    exists_cleanup_component Γ P hconn hP R r A B₃ m₂ Cext n profile
      hRpos hApos hnonempty hr hscale hAbound K Aset B C hAset hPcover
      hAdj hcore hn hB hC hR hconst
  refine ⟨c, hpositive, outsideComponent_isCleanupRoot Γ P c hnoLoop hnoParallel,
    hproper, ?_, horder, hcut, hexterior⟩
  intro v hv
  exact hcubic v ((Finset.disjoint_left.mp
    (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hv)

end Erdos1016.Proof.ActiveRankExtraction

end
