import Erdos1016.Graph.Multigraph.Forest

set_option autoImplicit false

/-! Incidence handshaking within a vertex region, including loops and parallel labels. -/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph

local instance regionDegreeDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem selectedDegree_eq_sum_endpoints (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) :
    G.selectedDegree x v = ∑ e, if x e ≠ 0 then
      (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) else 0 := by
  unfold selectedDegree
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hx : x e = 0 <;> by_cases hs : G.src e = v <;> by_cases ht : G.dst e = v <;>
    simp [hx, hs, ht]

/-- Each internal selected label contributes two incidences, and each
selected crossing label contributes one. -/
theorem sum_region_selectedDegree (G : FiniteMultiGraph) (x : G.EdgeWord) (U : Finset G.Vertex) :
    (∑ v ∈ U, G.selectedDegree x v) =
      2 * ((G.internalEdges U).filter fun e => x e ≠ 0).card +
        ((G.cutEdges U).filter fun e => x e ≠ 0).card := by
  classical
  simp_rw [G.selectedDegree_eq_sum_endpoints]
  rw [Finset.sum_comm]
  have hpoint (e : G.Edge) :
      (∑ v ∈ U, if x e ≠ 0 then
        (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) else 0) =
      (if e ∈ G.internalEdges U ∧ x e ≠ 0 then (2 : ℕ) else 0) +
        (if e ∈ G.cutEdges U ∧ x e ≠ 0 then 1 else 0) := by
    by_cases hx : x e = 0
    · simp [hx]
    · simp only [hx, ne_eq, not_false_eq_true, ↓reduceIte, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.sum_const_zero]
      by_cases hs : G.src e ∈ U <;> by_cases ht : G.dst e ∈ U <;>
        simp [internalEdges, cutEdges, hs, ht, hx]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  have hint : (∑ e : G.Edge, if e ∈ G.internalEdges U ∧ x e ≠ 0 then (2 : ℕ) else 0) =
      2 * ((G.internalEdges U).filter fun e => x e ≠ 0).card := by
    have hf : Finset.univ.filter (fun e : G.Edge => e ∈ G.internalEdges U ∧ x e ≠ 0) =
        (G.internalEdges U).filter fun e => x e ≠ 0 := by ext e; simp
    rw [← Finset.sum_filter, hf]
    simp [Nat.mul_comm]
  have hcut : (∑ e : G.Edge, if e ∈ G.cutEdges U ∧ x e ≠ 0 then (1 : ℕ) else 0) =
      ((G.cutEdges U).filter fun e => x e ≠ 0).card := by
    have hf : Finset.univ.filter (fun e : G.Edge => e ∈ G.cutEdges U ∧ x e ≠ 0) =
        (G.cutEdges U).filter fun e => x e ≠ 0 := by ext e; simp
    rw [← Finset.sum_filter, hf]
    simp
  rw [hint, hcut]

/-- The region degree ledger counts ambient loops twice and retains physical
parallel-edge multiplicity. -/
theorem sum_region_degree (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    (∑ v ∈ U, G.degree v) = 2 * (G.internalEdges U).card + (G.cutEdges U).card := by
  simpa [degree] using
    G.sum_region_selectedDegree (fun _ => 1) U

/-- A region containing a two-regular spanning seed has at least as many
internal physical edges as vertices. -/
theorem selected_internal_card_eq_of_two_regular (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.EdgeWord) (hx : ∀ v ∈ U, G.selectedDegree x v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges U → x e = 0) :
    ((G.internalEdges U).filter fun e => x e ≠ 0).card = U.card := by
  have hzero : ((G.cutEdges U).filter fun e => x e ≠ 0) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    have hcut := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    have hne := (Finset.mem_filter.mp he).2
    apply hne (hsupport e ?_)
    simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsum := G.sum_region_selectedDegree x U
  rw [hzero, Finset.card_empty, add_zero] at hsum
  have hleft : (∑ v ∈ U, G.selectedDegree x v) = 2 * U.card := by
    rw [Finset.sum_congr rfl (fun v hv => hx v hv)]
    simp [Nat.mul_comm]
  rw [hleft] at hsum
  omega

/-- The number of selected physical edges equals the number of region
vertices, including length-one and length-two multigraph cycles. -/
theorem support_card_eq_of_two_regular (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.EdgeWord) (hx : ∀ v ∈ U, G.selectedDegree x v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges U → x e = 0) :
    (Finset.univ.filter fun e => x e ≠ 0).card = U.card := by
  have hset : (G.internalEdges U).filter (fun e => x e ≠ 0) =
      Finset.univ.filter (fun e => x e ≠ 0) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro he
      exact ⟨Classical.byContradiction (fun hn => he (hsupport e hn)), he⟩
  rw [← hset]
  exact G.selected_internal_card_eq_of_two_regular U x hx hsupport

theorem internalEdges_card_ge_of_two_regular (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.EdgeWord) (hx : ∀ v ∈ U, G.selectedDegree x v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges U → x e = 0) :
    U.card ≤ (G.internalEdges U).card := by
  rw [← G.selected_internal_card_eq_of_two_regular U x hx hsupport]
  exact Finset.card_filter_le _ _

/-- A two-regular region in a subcubic ambient graph has cut at most its
vertex count. No induced-cycle assumption is needed. -/
theorem cutEdges_card_le_of_two_regular (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.EdgeWord) (hx : ∀ v ∈ U, G.selectedDegree x v = 2)
    (hsupport : ∀ e, e ∉ G.internalEdges U → x e = 0)
    (hdegree : ∀ v ∈ U, G.degree v ≤ 3) : (G.cutEdges U).card ≤ U.card := by
  have hin := G.internalEdges_card_ge_of_two_regular U x hx hsupport
  have hsum := G.sum_region_degree U
  have hbound : (∑ v ∈ U, G.degree v) ≤ 3 * U.card := by
    calc
      _ ≤ ∑ _v ∈ U, 3 := Finset.sum_le_sum hdegree
      _ = _ := by simp [Nat.mul_comm]
  omega

end Erdos1016.FiniteMultiGraph
