import Erdos1016.ExactMaximumSupport.CubicReduction.PhysicalCycles
import Erdos1016.Extremal.Capacity.CycleLengthComposition

set_option autoImplicit false

/-!
# Minimal even supports and connected cycles

A physical cycle has no proper nonzero even subword. Conversely, in a
subcubic multigraph, a minimal nonzero even word is a connected cycle.
The converse includes loops and parallel edges.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.CubicReduction

theorem physical_even_subword_eq (G : PhysicalGraph) (C : G.CycleWord)
    (y : G.CycleSpace) (hy : y.1 ≠ 0)
    (hsub : ∀ e, y.1 e ≠ 0 → C.1 e ≠ 0) : y.1 = C.1 := by
  classical
  let E := G.edgeSupport y.1
  have hword : G.extendWord E (G.restrictWord E C.1) = y.1 := by
    funext e
    by_cases he : y.1 e = 0
    · simp [PhysicalGraph.extendWord, PhysicalGraph.restrictWord, E,
        PhysicalGraph.edgeSupport, he]
    · have hc := hsub e he
      have hy1 : y.1 e = 1 := (FiniteMultiGraph.f2_eq_zero_or_one (y.1 e)).resolve_left he
      have hc1 : C.1 e = 1 := (FiniteMultiGraph.f2_eq_zero_or_one (C.1 e)).resolve_left hc
      simp [PhysicalGraph.extendWord, PhysicalGraph.restrictWord, E,
        PhysicalGraph.edgeSupport, he, hy1, hc1]
  have hin : ∃ e, e ∈ E ∧ C.1 e ≠ 0 := by
    have he : ∃ e, y.1 e ≠ 0 := Function.ne_iff.mp hy
    obtain ⟨e, he⟩ := he
    exact ⟨e, by simp [E, PhysicalGraph.edgeSupport, he], hsub e he⟩
  have hall : ∀ e, C.1 e ≠ 0 → e ∈ E := by
    intro e he
    by_contra hout
    apply G.restrictCycle_boundary_ne_zero C E hin ⟨e, hout, he⟩
    rw [← G.restrictedBoundary_eq_hostBoundary_extend, hword]
    exact y.2
  funext e
  by_cases he : C.1 e = 0
  · have hy0 : y.1 e = 0 := by
      by_contra hy0
      exact hsub e hy0 he
    exact hy0.trans he.symm
  · have hy0 : y.1 e ≠ 0 := by
      simpa [E, PhysicalGraph.edgeSupport] using hall e he
    rw [(FiniteMultiGraph.f2_eq_zero_or_one (y.1 e)).resolve_left hy0,
      (FiniteMultiGraph.f2_eq_zero_or_one (C.1 e)).resolve_left he]

private theorem selected_end_components (M : FiniteMultiGraph) (x : M.EdgeWord)
    (e : M.Edge) (he : x e ≠ 0) :
    (M.selectedGraph x).connectedComponentMk (M.src e) =
      (M.selectedGraph x).connectedComponentMk (M.dst e) := by
  by_cases h : M.src e = M.dst e
  · rw [h]
  · exact SimpleGraph.ConnectedComponent.sound
      (SimpleGraph.Adj.reachable ⟨h, e, he, Or.inl ⟨rfl, rfl⟩⟩)

theorem subcubic_isCycleWord_of_minimal (M : FiniteMultiGraph)
    (hmax : ∀ v, M.degree v ≤ 3) (x : M.CycleSpace) (hx : x.1 ≠ 0)
    (hmin : ∀ y : M.CycleSpace, y.1 ≠ 0 →
      (∀ e, y.1 e ≠ 0 → x.1 e ≠ 0) → y.1 = x.1) :
    M.IsCycleWord x.1 := by
  classical
  refine ⟨hx, ?_, ?_⟩
  · intro v
    have hle : M.selectedDegree x.1 v ≤ M.degree v := by
      unfold FiniteMultiGraph.degree FiniteMultiGraph.selectedDegree
      apply Nat.add_le_add <;> apply Finset.card_le_card <;>
        intro e he <;> simp_all only [Finset.mem_filter, Finset.mem_univ,
          true_and, ne_eq, one_ne_zero, not_false_eq_true]
    have heven : 2 ∣ M.selectedDegree x.1 v := by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp
      rw [← M.boundary_apply_eq_selectedDegree]
      exact congrFun x.2 v
    have hupper := hmax v
    omega
  · intro u v hu hv
    let c := (M.selectedGraph x.1).connectedComponentMk u
    let z : M.EdgeWord := fun e =>
      if (M.selectedGraph x.1).connectedComponentMk (M.src e) = c then x.1 e else 0
    have hzboundary : M.boundary z = 0 := by
      funext w
      have hterm (e : M.Edge) :
          (if M.src e = w then z e else 0) + (if M.dst e = w then z e else 0) =
          if (M.selectedGraph x.1).connectedComponentMk w = c then
            ((if M.src e = w then x.1 e else 0) +
              (if M.dst e = w then x.1 e else 0)) else 0 := by
        by_cases he : x.1 e = 0
        · simp [z, he]
        · have hcomp := selected_end_components M x.1 e he
          by_cases hs : M.src e = w
          · by_cases hw : (M.selectedGraph x.1).connectedComponentMk w = c <;>
              simp [z, hs, hw]
          · by_cases ht : M.dst e = w
            · rw [ht] at hcomp
              simp [z, hs, ht, hcomp]
            · simp [z, hs, ht]
      change (∑ e, ((if M.src e = w then z e else 0) +
        (if M.dst e = w then z e else 0))) = 0
      simp_rw [hterm]
      by_cases hw : (M.selectedGraph x.1).connectedComponentMk w = c
      · simp only [hw, if_true]
        exact congrFun x.2 w
      · simp [hw]
    have hzsub : ∀ e, z e ≠ 0 → x.1 e ≠ 0 := by
      intro e he
      intro he0
      exact he (by simp only [z, he0, ite_self])
    have hzcomp (e : M.Edge) (he : z e ≠ 0) :
        (M.selectedGraph x.1).connectedComponentMk (M.src e) = c := by
      by_cases hc : (M.selectedGraph x.1).connectedComponentMk (M.src e) = c
      · exact hc
      · exact False.elim (he (by simp only [z, hc, if_false]))
    have hz : z ≠ 0 := by
      obtain ⟨e, he, hs | ht⟩ := FiniteMultiGraph.exists_edge_of_selectedDegree_pos hu
      · intro hzero
        have h := congrFun hzero e
        have hc : (M.selectedGraph x.1).connectedComponentMk (M.src e) = c := by
          simp only [c, hs]
        exact he (by simpa only [z, hc, if_true, Pi.zero_apply] using h)
      · intro hzero
        have h := congrFun hzero e
        have hc := selected_end_components M x.1 e he
        rw [ht] at hc
        change (M.selectedGraph x.1).connectedComponentMk (M.src e) = c at hc
        exact he (by simpa only [z, hc, if_true, Pi.zero_apply] using h)
    have heq : z = x.1 := hmin ⟨z, hzboundary⟩ hz hzsub
    obtain ⟨e, he, hs | ht⟩ := FiniteMultiGraph.exists_edge_of_selectedDegree_pos hv
    all_goals
      have hze : z e ≠ 0 := by rw [heq]; exact he
      have hc := hzcomp e hze
    · apply SimpleGraph.ConnectedComponent.exact
      simpa only [c, hs] using hc.symm
    · apply SimpleGraph.ConnectedComponent.exact
      have hc' := selected_end_components M x.1 e he
      simpa only [c, ht] using hc.symm.trans hc'

end Erdos1016.ExactMaximumSupport.CubicReduction
