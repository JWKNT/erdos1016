import Erdos1016.ExactMaximum.Cycles
import Erdos1016.Probability.Cylinders.RegionCycleEvents

set_option autoImplicit false

/-!
# Actual vertex regions of physical cycles

The region consists of vertices incident with selected physical labels.
The cycle supplies a connected region and a nonzero internal even word.
Its vertex count equals its physical length. In subcubic graphs its cut is no larger.
Loops and parallel edge labels remain distinct throughout.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.CycleRegions
open FiniteMultiGraph

local instance cycleRegionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The literal vertex support of a physical edge word. -/
def region (G : FiniteMultiGraph) (x : G.EdgeWord) : Finset G.Vertex :=
  Finset.univ.filter fun v => 0 < G.selectedDegree x v

@[simp] theorem mem_region (G : FiniteMultiGraph) (x : G.EdgeWord) (v : G.Vertex) :
    v ∈ region G x ↔ 0 < G.selectedDegree x v := by simp [region]

/-- Every selected physical label lies inside its vertex support. -/
theorem supported_region (G : FiniteMultiGraph) (x : G.EdgeWord) :
    ∀ e, e ∉ G.internalEdges (region G x) → x e = 0 := by
  intro e he
  by_contra hne
  apply he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (mem_region G x _).mpr (G.selectedDegree_src_pos hne),
    (mem_region G x _).mpr (G.selectedDegree_dst_pos hne)⟩

theorem cycle_degree (G : FiniteMultiGraph) (x : G.EdgeWord) (hx : G.IsCycleWord x) :
    ∀ v ∈ region G x, G.selectedDegree x v = 2 := by
  intro v hv
  have hp := (mem_region G x v).mp hv
  rcases hx.2.1 v with hz | ht
  · omega
  · exact ht

/-- A cycle has equally many selected physical labels and incident vertices. -/
theorem cycle_region_card (G : FiniteMultiGraph) (x : G.EdgeWord) (hx : G.IsCycleWord x) :
    (region G x).card = G.wordLength x :=
  (G.support_card_eq_of_two_regular _ x (cycle_degree G x hx) (supported_region G x)).symm

private theorem reachable_region (G : FiniteMultiGraph) (x : G.EdgeWord)
    {u v : G.Vertex} (p : (G.selectedGraph x).Walk u v)
    (hu : u ∈ region G x) (hv : v ∈ region G x) :
    (G.toSimpleGraph.induce (↑(region G x) : Set G.Vertex)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u w v huw p ih =>
    have hw : w ∈ region G x := by
      obtain ⟨_, e, he, h | h⟩ := huw
      · exact (mem_region G x w).mpr (h.2 ▸ G.selectedDegree_dst_pos he)
      · exact (mem_region G x w).mpr (h.1 ▸ G.selectedDegree_src_pos he)
    obtain ⟨q⟩ := ih hw hv
    have ha : (G.toSimpleGraph.induce (↑(region G x) : Set G.Vertex)).Adj
        ⟨u, hu⟩ ⟨w, hw⟩ := by
      obtain ⟨hne, e, _, hend⟩ := huw
      exact ⟨hne, e, hend⟩
    exact ⟨q.cons ha⟩

/-- The induced cycle region is connected even when the ambient graph has parallel labels. -/
theorem cycle_region_connected (G : FiniteMultiGraph) (x : G.EdgeWord)
    (hx : G.IsCycleWord x) :
    (G.toSimpleGraph.induce (↑(region G x) : Set G.Vertex)).Connected := by
  obtain ⟨e, he⟩ : ∃ e, x e ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx.1 (funext h)
  refine { nonempty := ⟨⟨G.src e, (mem_region G x _).mpr (G.selectedDegree_src_pos he)⟩⟩, preconnected := ?_ }
  intro u v
  obtain ⟨p⟩ := hx.2.2 u.1 v.1 ((mem_region G x _).mp u.2) ((mem_region G x _).mp v.2)
  exact reachable_region G x p u.2 v.2

/-- The cycle itself supplies a nonzero internal even word. -/
theorem cycle_region_cyclic (G : FiniteMultiGraph) (x : G.EdgeWord) (hx : G.IsCycleWord x) :
    ∃ z : G.internalCycleSpace (region G x), z ≠ 0 := by
  refine ⟨⟨⟨x, hx.boundary_eq_zero⟩, supported_region G x⟩, ?_⟩
  intro h
  exact hx.1 (congrArg (fun z : G.internalCycleSpace (region G x) => z.1.1) h)

/-- A subcubic cycle region has at most its length in crossing physical labels. -/
theorem cycle_cut_le_length (G : FiniteMultiGraph) (x : G.EdgeWord) (hx : G.IsCycleWord x)
    (hdegree : ∀ v, G.degree v ≤ 3) : (G.cutEdges (region G x)).card ≤ G.wordLength x := by
  rw [← cycle_region_card G x hx]
  exact G.cutEdges_card_le_of_two_regular _ x (cycle_degree G x hx)
    (supported_region G x) (fun v _ => hdegree v)

end Erdos1016.ExactMaximumSupport.CycleRegions
