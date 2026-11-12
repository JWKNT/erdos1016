import Erdos1016.ExactMaximumSupport.CubicReduction.CubicCore
import Erdos1016.Graph.Suppression.MarkedCorridors

set_option autoImplicit false

/-!
# The exact edge-length ledger for corridor suppression

The supports of the actual routes partition all physical edge labels.
Their cardinalities therefore sum to the original number of edges.
The cubic core order and size follow from incidence degree and cycle rank.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.LargeGirth.CorridorLedger

open FiniteMultiGraph ShortProof Proof.CompressedRouteDecomposition

theorem sum_support_card (A P : FiniteMultiGraph) (R : EdgeDisjointRouteSystem A P)
    (hcover : ∀ p : P.Edge, ∃ e, p ∈ R.support e) :
    (∑ e, (R.support e).card) = P.edgeCount := by
  classical
  let f : (Σ e : A.Edge, {p // p ∈ R.support e}) → P.Edge := fun z => z.2.1
  have hi : Function.Injective f := by
    rintro ⟨e, p⟩ ⟨e', p'⟩ hh
    have hp : p.1 = p'.1 := hh
    have he : e = e' := by
      by_contra hne
      exact Finset.disjoint_left.mp (R.disjoint hne) p.2 (hp.symm ▸ p'.2)
    subst e'
    have hpp : p = p' := Subtype.ext hp
    cases hpp
    rfl
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨e, he⟩ := hcover p
    exact ⟨⟨e, ⟨p, he⟩⟩, rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hi, hs⟩)
  simpa only [Fintype.card_sigma, Fintype.card_coe, Fintype.card_fin] using hc

theorem cubic_order_size (M : FiniteMultiGraph) (hconn : M.toSimpleGraph.Connected)
    (hcub : M.IsCubic) :
    M.vertexCount + 2 = 2 * M.cycleRank ∧ M.edgeCount + 3 = 3 * M.cycleRank := by
  have he := M.connected_euler hconn
  have hd := M.sum_degree
  have hsum : (∑ v : M.Vertex, M.degree v) = 3 * M.vertexCount := by
    calc
      (∑ v : M.Vertex, M.degree v) = ∑ _ : M.Vertex, 3 :=
        Finset.sum_congr rfl (fun v _ => hcub v)
      _ = 3 * M.vertexCount := by simp [Nat.mul_comm]
  rw [hsum] at hd
  omega

variable (G : PhysicalGraph) (P : Finset G.Vertex)
  (hconn : G.IsConnected) (hP : P.Nonempty)
  (hdegree : ∀ v, v ∉ P → G.degree v = 2 ∨ G.degree v = 3)

theorem marked_route_length_sum :
    (∑ e, ((MarkedCorridors.routes G P hconn hP hdegree).support e).card) = G.edgeCount := by
  apply sum_support_card
  exact (compressedCorridorDecomposition
    (MarkedCorridors.partition G P hconn hP hdegree)
    (MarkedCorridors.partition_nonempty G P hconn hP hdegree)
    (MarkedCorridors.partition_endpoints G P hconn hP hdegree)).physical_edge_coverage

end Erdos1016.ExactMaximumSupport.LargeGirth.CorridorLedger
