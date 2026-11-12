import Erdos1016.ExactMaximumSupport.LargeGirth.PackingLocalSpacesProbability
import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProductWords

set_option autoImplicit false

/-!
# Rank loss under vertex deletion

All ranks refer to the actual labelled multigraph. Parallel edges remain distinct.
Connectivity is not required. The loopless hypothesis supplies one parity equation
at each deleted vertex. Thus a deleted vertex of degree at most three costs at
most two cycle-space dimensions.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.VertexRankDeletion
open FiniteMultiGraph LargeGirth LargeGirth.PackingLocalSpaces

local instance deletionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Observing all incident edge labels leaves precisely the exterior internal cycle space. -/
theorem ker_observe_touched (G : FiniteMultiGraph) (X : Finset G.Vertex) :
    LinearMap.ker (G.observeEdges (touchedEdges G X)) = G.internalCycleSpace Xᶜ := by
  ext x
  change G.observeEdges (touchedEdges G X) x = 0 ↔
    ∀ e, e ∉ G.internalEdges Xᶜ → x.1 e = 0
  constructor
  · intro h e he
    have ht : e ∈ touchedEdges G X := by
      simpa only [touchedEdges, internalEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_compl, not_and_or, not_not] using he
    exact congrFun h ⟨e, ht⟩
  · intro h
    ext e
    exact h e.1 (by
      simpa only [touchedEdges, internalEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_compl, not_and_or, not_not] using e.2)

/-- Exact rank-nullity for deletion, with the lost rank expressed by actual local dual spaces. -/
theorem rank_eq_exterior_add_marked (G : FiniteMultiGraph) (X : Finset G.Vertex) :
    G.cycleRank = (PieceCore.Induced.graph G Xᶜ).cycleRank +
      Module.finrank F₂ (markedSpace G X) := by
  have h := (G.observeEdges (touchedEdges G X)).finrank_range_add_finrank_ker
  rw [ker_observe_touched, ← coordinateSpace_finrank] at h
  have he := (PoleProduct.cycleEquiv G Xᶜ).finrank_eq
  change (PieceCore.Induced.graph G Xᶜ).cycleRank =
    Module.finrank F₂ (G.internalCycleSpace Xᶜ) at he
  change G.cycleRank = _
  simpa only [← he, Nat.add_comm] using h.symm

/-- The finite supremum of local spaces has at most the sum of their dimensions. -/
theorem markedSpace_finrank_le_sum (G : FiniteMultiGraph) (X : Finset G.Vertex) :
    Module.finrank F₂ (markedSpace G X) ≤
      ∑ v ∈ X, Module.finrank F₂ (localSpace G v) := by
  rw [markedSpace_eq_sup]
  induction X using Finset.induction_on with
  | empty => simp
  | @insert v X hv ih =>
    rw [Finset.sup_insert, Finset.sum_insert hv]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (Nat.add_le_add_left ih _)

/-- Degree minus one bounds the rank lost at each deleted vertex. Isolated vertices cost zero. -/
theorem markedSpace_finrank_le_degree_sum (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (hloop : ∀ e, G.src e ≠ G.dst e) :
    Module.finrank F₂ (markedSpace G X) ≤ ∑ v ∈ X, (G.degree v - 1) := by
  exact (markedSpace_finrank_le_sum G X).trans
    (Finset.sum_le_sum fun v _ => localSpace_finrank_le G v hloop)

/-- Deleting vertices of degree at most three loses at most twice their number of cycle dimensions. -/
theorem rank_le_exterior_add_twice_card (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (hloop : ∀ e, G.src e ≠ G.dst e) (hdegree : ∀ v ∈ X, G.degree v ≤ 3) :
    G.cycleRank ≤ (PieceCore.Induced.graph G Xᶜ).cycleRank + 2 * X.card := by
  rw [rank_eq_exterior_add_marked G X]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ v ∈ X, (G.degree v - 1) := markedSpace_finrank_le_degree_sum G X hloop
    _ ≤ ∑ _v ∈ X, 2 := Finset.sum_le_sum fun v hv => by have := hdegree v hv; omega
    _ = 2 * X.card := by simp [Nat.mul_comm]

/-- The internal spaces intersect exactly as the actual vertex regions do. -/
theorem internalCycleSpace_inter (G : FiniteMultiGraph) (R S : Finset G.Vertex) :
    G.internalCycleSpace R ⊓ G.internalCycleSpace S = G.internalCycleSpace (R ∩ S) := by
  have he : G.internalEdges (R ∩ S) = G.internalEdges R ∩ G.internalEdges S := by
    ext e
    simp only [internalEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    tauto
  ext x
  change ((∀ e, e ∉ G.internalEdges R → x.1 e = 0) ∧
    (∀ e, e ∉ G.internalEdges S → x.1 e = 0)) ↔
    ∀ e, e ∉ G.internalEdges (R ∩ S) → x.1 e = 0
  rw [he]
  constructor
  · rintro ⟨hR, hS⟩ e he
    by_cases hr : e ∈ G.internalEdges R
    · exact hS e (fun hs => he (Finset.mem_inter.mpr ⟨hr, hs⟩))
    · exact hR e hr
  · intro h
    exact ⟨fun e he => h e (fun hi => he (Finset.mem_inter.mp hi).1),
      fun e he => h e (fun hi => he (Finset.mem_inter.mp hi).2)⟩

/-- Region-local deletion uses the same physical labels and the flat region `R \ X`. -/
theorem rank_region_le_diff_add_marked (G : FiniteMultiGraph) (R X : Finset G.Vertex) :
    (PieceCore.Induced.graph G R).cycleRank ≤
      (PieceCore.Induced.graph G (R \ X)).cycleRank + Module.finrank F₂ (markedSpace G X) := by
  have hdim := (G.internalCycleSpace R).finrank_sup_add_finrank_inf_eq
    (G.internalCycleSpace Xᶜ)
  have hle := Submodule.finrank_le (G.internalCycleSpace R ⊔ G.internalCycleSpace Xᶜ)
  rw [internalCycleSpace_inter, ← Finset.sdiff_eq_inter_compl] at hdim
  have hR := (PoleProduct.cycleEquiv G R).finrank_eq
  have hX := (PoleProduct.cycleEquiv G Xᶜ).finrank_eq
  have hdiff := (PoleProduct.cycleEquiv G (R \ X)).finrank_eq
  have htotal := rank_eq_exterior_add_marked G X
  unfold FiniteMultiGraph.cycleRank at htotal ⊢
  omega

/-- Deletion inside an induced region loses at most two ranks per deleted vertex. -/
theorem rank_region_le_diff_add_twice_card (G : FiniteMultiGraph) (R X : Finset G.Vertex)
    (hloop : ∀ e, G.src e ≠ G.dst e) (hdegree : ∀ v ∈ X, G.degree v ≤ 3) :
    (PieceCore.Induced.graph G R).cycleRank ≤
      (PieceCore.Induced.graph G (R \ X)).cycleRank + 2 * X.card := by
  apply (rank_region_le_diff_add_marked G R X).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ v ∈ X, (G.degree v - 1) := markedSpace_finrank_le_degree_sum G X hloop
    _ ≤ ∑ _v ∈ X, 2 := Finset.sum_le_sum fun v hv => by have := hdegree v hv; omega
    _ = 2 * X.card := by simp [Nat.mul_comm]

/-- Actual labelled foresthood forces the internal cycle space to be zero. -/
theorem internalCycleSpace_eq_bot_of_forest (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hforest : G.IsForestWord (G.restrictEdges (G.internalEdges R) (fun _ => 1))) :
    G.internalCycleSpace R = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply Subtype.ext
  apply (G.isForestWord_iff_no_even_support _).mp hforest x
  intro e he
  have hi : e ∈ G.internalEdges R := by by_contra h; exact he (hx e h)
  simp [restrictEdges, hi]

/-- Foresthood, rather than an assumed rank certificate, gives zero induced rank. -/
theorem induced_rank_eq_zero_of_forest (G : FiniteMultiGraph) (R : Finset G.Vertex)
    (hforest : G.IsForestWord (G.restrictEdges (G.internalEdges R) (fun _ => 1))) :
    (PieceCore.Induced.graph G R).cycleRank = 0 := by
  change Module.finrank F₂ (PieceCore.Induced.graph G R).CycleSpace = 0
  rw [(PoleProduct.cycleEquiv G R).finrank_eq, internalCycleSpace_eq_bot_of_forest G R hforest]
  simp

/-- A vertex set whose removal leaves a labelled forest has size at least half the cycle rank. -/
theorem rank_le_twice_card_of_exterior_forest (G : FiniteMultiGraph) (X : Finset G.Vertex)
    (hloop : ∀ e, G.src e ≠ G.dst e) (hdegree : ∀ v ∈ X, G.degree v ≤ 3)
    (hforest : G.IsForestWord (G.restrictEdges (G.internalEdges Xᶜ) (fun _ => 1))) :
    G.cycleRank ≤ 2 * X.card := by
  simpa only [induced_rank_eq_zero_of_forest G Xᶜ hforest, zero_add] using
    rank_le_exterior_add_twice_card G X hloop hdegree

/-- The same forest-deletion bound holds inside any induced region. -/
theorem rank_region_le_twice_card_of_diff_forest (G : FiniteMultiGraph) (R X : Finset G.Vertex)
    (hloop : ∀ e, G.src e ≠ G.dst e) (hdegree : ∀ v ∈ X, G.degree v ≤ 3)
    (hforest : G.IsForestWord (G.restrictEdges (G.internalEdges (R \ X)) (fun _ => 1))) :
    (PieceCore.Induced.graph G R).cycleRank ≤ 2 * X.card := by
  simpa only [induced_rank_eq_zero_of_forest G (R \ X) hforest, zero_add] using
    rank_region_le_diff_add_twice_card G R X hloop hdegree

end Erdos1016.ExactMaximumSupport.VertexRankDeletion
