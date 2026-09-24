import Erdos1016.Cleanup.Root.ProtectedComponentGrowth
import Erdos1016.Graph.Multigraph.BoundaryImage
import Erdos1016.Cleanup.Root.ProperRootBoundary
import Erdos1016.Cleanup.Compression.AssembledCorridorCompression

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ComponentExtraction

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.ProtectedExteriorComponents
open Erdos1016.Proof.ProtectedComponentGrowth

abbrev OutsideComponent (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) :=
  (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent

/-- The vertices of one connected component outside the protected set. -/
noncomputable abbrev outsideComponentVertices
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent) :
    Finset Γ.Vertex :=
  componentVertexSet Γ.toSimpleGraph P c

/-- Every component outside a nonempty protected set has a nonempty ambient
boundary when the whole auxiliary graph is connected. -/
theorem outsideComponent_cut_nonempty
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (c : OutsideComponent Γ P) :
    (cutEdges Γ (outsideComponentVertices Γ P c)).Nonempty := by
  classical
  let H := outsideComponentVertices Γ P c
  have hHne : H.Nonempty := by
    obtain ⟨v, hv⟩ := c.nonempty_supp
    refine ⟨v.1, ?_⟩
    change v.1 ∈ Finset.univ.filter _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, rfl⟩
  have hdisj := componentVertexSet_disjoint Γ.toSimpleGraph P c
  have hproper : H.card < Γ.vertexCount := by
    obtain ⟨p, hp⟩ := hP
    have hpnot : p ∉ H := (Finset.disjoint_right.mp hdisj) hp
    have hlt : H.card < Fintype.card Γ.Vertex := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
        intro heq
        have : p ∈ H := by rw [heq]; exact Finset.mem_univ _
        exact hpnot this⟩)
    simpa using hlt
  exact ProperRootBoundary.cutEdges_nonempty_of_connected
    Γ hconn H hHne hproper

/-- The labelled multigraph induced on one unprotected component. We keep the
edge labels, so parallel edges remain distinct and loops (if present in the
ambient model) retain their cycle-space contribution. -/
noncomputable def componentInternalGraph
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (c : OutsideComponent Γ P) : FiniteMultiGraph := by
  classical
  let H := outsideComponentVertices Γ P c
  let V := {v : Γ.Vertex // v ∈ H}
  let E := {e : Γ.Edge // e ∈ internalEdges Γ H}
  let ve : V ≃ Fin H.card := Finset.equivFin H
  let ee : E ≃ Fin (internalEdges Γ H).card := Finset.equivFin (internalEdges Γ H)
  exact {
    vertexCount := H.card
    edgeCount := (internalEdges Γ H).card
    src := fun i => ve ⟨Γ.src (ee.symm i).1,
      (Finset.mem_filter.mp (ee.symm i).2).2.1⟩
    dst := fun i => ve ⟨Γ.dst (ee.symm i).1,
      (Finset.mem_filter.mp (ee.symm i).2).2.2⟩ }

@[simp] theorem componentInternalGraph_vertexCount
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P) :
    (componentInternalGraph Γ P c).vertexCount =
      (outsideComponentVertices Γ P c).card := rfl

@[simp] theorem componentInternalGraph_edgeCount
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P) :
    (componentInternalGraph Γ P c).edgeCount =
      (internalEdges Γ (outsideComponentVertices Γ P c)).card := rfl

/-- The actual cycle rank of the labelled multigraph induced on a component. -/
noncomputable def outsideComponentRank
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P) : ℕ :=
  (componentInternalGraph Γ P c).cycleRank

private theorem support_vertex_mem_componentSet
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P)
    (x : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)}) (hx : x ∈ c.supp) :
    x.1 ∈ outsideComponentVertices Γ P c := by
  classical
  change x.1 ∈ Finset.univ.filter _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hx, rfl⟩

private noncomputable def componentSupportVertexMap
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P) :
    {x : {v : Γ.Vertex // v ∈ (↑(Pᶜ) : Set Γ.Vertex)} // x ∈ c.supp} →
      (componentInternalGraph Γ P c).Vertex := by
  classical
  intro x
  exact (Finset.equivFin (outsideComponentVertices Γ P c))
    ⟨x.1.1, support_vertex_mem_componentSet Γ P c x.1 x.2⟩

/-- The labelled multigraph on one component's vertices is connected. Every
support vertex maps to its canonical finite index, and every edge of the
component-induced simple graph lifts to its ambient edge label. -/
theorem componentInternalGraph_connected
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P) :
    (componentInternalGraph Γ P c).toSimpleGraph.Connected := by
  classical
  let Q := Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)
  let J := Q.induce c.supp
  let D := componentInternalGraph Γ P c
  let f := componentSupportVertexMap Γ P c
  have hJ : J.Connected := c.connected_induce_supp
  have hsurj : Function.Surjective f := by
    intro i
    let v := (Finset.equivFin (outsideComponentVertices Γ P c)).symm i
    have hv := v.2
    change v.1 ∈ Finset.univ.filter _ at hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨x, hx, hxv⟩ := hv
    have hxH := support_vertex_mem_componentSet Γ P c x hx
    have hsub : v = ⟨x.1, hxH⟩ := by
      apply Subtype.ext
      exact hxv.symm
    have hi : (Finset.equivFin (outsideComponentVertices Γ P c)) v = i := by
      exact (Finset.equivFin (outsideComponentVertices Γ P c)).apply_symm_apply i
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa [f, componentSupportVertexMap, v, hsub] using hi
  have hstep : ∀ ⦃u v⦄, J.Adj u v → f u = f v ∨ D.toSimpleGraph.Adj (f u) (f v) := by
    intro u v huv
    have hadj : Γ.toSimpleGraph.Adj u.1.1 v.1.1 := huv
    rcases hadj with ⟨hne, e, hend | hend⟩
    · have huH := support_vertex_mem_componentSet Γ P c u.1 u.2
      have hvH := support_vertex_mem_componentSet Γ P c v.1 v.2
      have hsH : Γ.src e ∈ outsideComponentVertices Γ P c := by rw [hend.1]; exact huH
      have htH : Γ.dst e ∈ outsideComponentVertices Γ P c := by rw [hend.2]; exact hvH
      have he : e ∈ internalEdges Γ (outsideComponentVertices Γ P c) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hsH, htH⟩
      have hsource : D.src ((Finset.equivFin
          (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩) = f u := by
        have hsub : (⟨Γ.src e, hsH⟩ : {x : Γ.Vertex // x ∈ outsideComponentVertices Γ P c}) =
            ⟨u.1.1, huH⟩ := Subtype.ext hend.1
        simpa [D, f, componentSupportVertexMap, componentInternalGraph] using
          congrArg (Finset.equivFin (outsideComponentVertices Γ P c)) hsub
      have htarget : D.dst ((Finset.equivFin
          (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩) = f v := by
        have hsub : (⟨Γ.dst e, htH⟩ : {x : Γ.Vertex // x ∈ outsideComponentVertices Γ P c}) =
            ⟨v.1.1, hvH⟩ := Subtype.ext hend.2
        simpa [D, f, componentSupportVertexMap, componentInternalGraph] using
          congrArg (Finset.equivFin (outsideComponentVertices Γ P c)) hsub
      right
      refine ⟨?_, ⟨(Finset.equivFin
        (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩, ?_⟩⟩
      · intro hEq
        have hsub := congrArg ((Finset.equivFin
          (outsideComponentVertices Γ P c)).symm) hEq
        have hvEq : u.1.1 = v.1.1 := by
          simpa [f, componentSupportVertexMap] using congrArg Subtype.val hsub
        exact hne hvEq
      · exact Or.inl ⟨hsource, htarget⟩
    · have huH := support_vertex_mem_componentSet Γ P c u.1 u.2
      have hvH := support_vertex_mem_componentSet Γ P c v.1 v.2
      have hsH : Γ.src e ∈ outsideComponentVertices Γ P c := by rw [hend.1]; exact hvH
      have htH : Γ.dst e ∈ outsideComponentVertices Γ P c := by rw [hend.2]; exact huH
      have he : e ∈ internalEdges Γ (outsideComponentVertices Γ P c) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          hsH, htH⟩
      have hsource : D.src ((Finset.equivFin
          (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩) = f v := by
        have hsub : (⟨Γ.src e, hsH⟩ : {x : Γ.Vertex // x ∈ outsideComponentVertices Γ P c}) =
            ⟨v.1.1, hvH⟩ := Subtype.ext hend.1
        simpa [D, f, componentSupportVertexMap, componentInternalGraph] using
          congrArg (Finset.equivFin (outsideComponentVertices Γ P c)) hsub
      have htarget : D.dst ((Finset.equivFin
          (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩) = f u := by
        have hsub : (⟨Γ.dst e, htH⟩ : {x : Γ.Vertex // x ∈ outsideComponentVertices Γ P c}) =
            ⟨u.1.1, huH⟩ := Subtype.ext hend.2
        simpa [D, f, componentSupportVertexMap, componentInternalGraph] using
          congrArg (Finset.equivFin (outsideComponentVertices Γ P c)) hsub
      right
      refine ⟨?_, ⟨(Finset.equivFin
        (internalEdges Γ (outsideComponentVertices Γ P c))) ⟨e, he⟩, ?_⟩⟩
      · intro hEq
        have hsub := congrArg ((Finset.equivFin
          (outsideComponentVertices Γ P c)).symm) hEq
        have hvEq : u.1.1 = v.1.1 := by
          simpa [f, componentSupportVertexMap] using congrArg Subtype.val hsub
        exact hne hvEq
      · exact Or.inr ⟨hsource, htarget⟩
  exact AssembledCorridorCompression.SimpleGraph.connected_of_surjective_step
    J D.toSimpleGraph f hsurj hstep hJ

/-- Euler's formula for a connected induced component graph. -/
theorem componentInternalGraph_euler
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex) (c : OutsideComponent Γ P)
    (hconn : (componentInternalGraph Γ P c).toSimpleGraph.Connected) :
    outsideComponentRank Γ P c + (outsideComponentVertices Γ P c).card =
      (internalEdges Γ (outsideComponentVertices Γ P c)).card + 1 := by
  classical
  let D := componentInternalGraph Γ P c
  have hv : Nonempty D.Vertex := hconn.nonempty
  letI : Subsingleton D.ConnectedComponent := hconn.preconnected.subsingleton_connectedComponent
  letI : Unique D.ConnectedComponent :=
    ⟨⟨D.componentOf (Classical.choice hv)⟩, fun x => Subsingleton.elim _ _⟩
  have hcard : D.componentCount = 1 := by
    simp [FiniteMultiGraph.componentCount, Fintype.card_unique]
  have he := FiniteMultiGraph.euler_formula D
  rw [hcard] at he
  simpa [D, outsideComponentRank, componentInternalGraph_vertexCount,
    componentInternalGraph_edgeCount] using he

/-- Steps 6--7's per-component data, after the elementary rank and incidence
bookkeeping has been performed on the suppressed multigraph. The `rank`
values are the cycle ranks of the induced component multigraphs; the Euler
field records the cubic ambient-degree identity needed to compare rank and
order. -/
structure ComponentExtractionProfile
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (r R A : ℕ) where
  cubicOutside : ∀ v, v ∉ P → ambientDegree Γ v = 3
  componentCount_le : Fintype.card
      (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent ≤ A
  rank_sum_lower : (r : ℝ) / (10 * R) ≤
      ∑ c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent,
        (outsideComponentRank Γ P c : ℝ)
  component_cut_le : ∀ c, (cutEdges Γ (outsideComponentVertices Γ P c)).card ≤ A

private theorem ambientDegree_eq_endpoint_sum (Γ : FiniteMultiGraph) (v : Γ.Vertex) :
    ambientDegree Γ v = ∑ e : Γ.Edge,
      ((if Γ.src e = v then 1 else 0) + (if Γ.dst e = v then 1 else 0)) := by
  classical
  unfold ambientDegree
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_add_distrib]

theorem ambientDegree_sum_region (Γ : FiniteMultiGraph) (S : Finset Γ.Vertex) :
    (∑ v ∈ S, ambientDegree Γ v) =
      2 * (internalEdges Γ S).card + (cutEdges Γ S).card := by
  classical
  simp_rw [ambientDegree_eq_endpoint_sum]
  rw [Finset.sum_comm]
  have hp (e : Γ.Edge) :
      (if Γ.src e ∈ S then 1 else 0) + (if Γ.dst e ∈ S then 1 else 0) =
        2 * (if Γ.src e ∈ S ∧ Γ.dst e ∈ S then 1 else 0) +
          (if (Γ.src e ∈ S ∧ Γ.dst e ∉ S) ∨
              (Γ.src e ∉ S ∧ Γ.dst e ∈ S) then 1 else 0) := by
    by_cases hs : Γ.src e ∈ S <;> by_cases ht : Γ.dst e ∈ S <;> simp [hs, ht]
  calc
    (∑ e : Γ.Edge, ∑ v ∈ S,
        ((if Γ.src e = v then 1 else 0) + (if Γ.dst e = v then 1 else 0))) =
        ∑ e : Γ.Edge,
          ((if Γ.src e ∈ S then 1 else 0) + (if Γ.dst e ∈ S then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro e _
      simp [Finset.sum_add_distrib, eq_comm]
    _ = ∑ e : Γ.Edge,
        (2 * (if Γ.src e ∈ S ∧ Γ.dst e ∈ S then 1 else 0) +
          (if (Γ.src e ∈ S ∧ Γ.dst e ∉ S) ∨
              (Γ.src e ∉ S ∧ Γ.dst e ∈ S) then 1 else 0)) :=
      Finset.sum_congr rfl fun e _ => hp e
    _ = _ := by
      simp only [internalEdges, cutEdges, Finset.card_eq_sum_ones,
        Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.sum_add_distrib, Finset.mul_sum, Finset.mem_compl]

theorem component_cubic_incidence
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hcubic : ∀ v, v ∉ P → ambientDegree Γ v = 3)
    (c : OutsideComponent Γ P) :
    3 * (outsideComponentVertices Γ P c).card =
      2 * (internalEdges Γ (outsideComponentVertices Γ P c)).card +
        (cutEdges Γ (outsideComponentVertices Γ P c)).card := by
  classical
  let H := outsideComponentVertices Γ P c
  have hdisj := componentVertexSet_disjoint Γ.toSimpleGraph P c
  have hsum : (∑ v ∈ H, ambientDegree Γ v) = 3 * H.card := by
    calc
      (∑ v ∈ H, ambientDegree Γ v) = ∑ _v ∈ H, 3 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvP : v ∉ P := (Finset.disjoint_left.mp hdisj) hv
        exact hcubic v hvP
      _ = 3 * H.card := by simp [Nat.mul_comm]
  rw [← hsum]
  exact ambientDegree_sum_region Γ H

theorem componentRank_incidence_formula
    {Γ : FiniteMultiGraph} {P : Finset Γ.Vertex} {r R A : ℕ}
    (profile : ComponentExtractionProfile Γ P r R A)
    (c : OutsideComponent Γ P) :
    2 * outsideComponentRank Γ P c +
        (cutEdges Γ (outsideComponentVertices Γ P c)).card =
      (outsideComponentVertices Γ P c).card + 2 := by
  have he := componentInternalGraph_euler Γ P c
    (componentInternalGraph_connected Γ P c)
  have hi := component_cubic_incidence Γ P profile.cubicOutside c
  omega

/-- Select a component whose rank receives at least its average share. This
is the finite averaging step of Section 10, with all ranks kept in ℝ so the
paper's ratio bounds transfer without rounding losses. -/
theorem exists_component_rank_ge_average
    {Γ : FiniteMultiGraph} {P : Finset Γ.Vertex} {r R A : ℕ}
    (profile : ComponentExtractionProfile Γ P r R A)
    (hR : 0 < R) (hA : 0 < A)
    (hnonempty : Nonempty (OutsideComponent Γ P)) :
    ∃ c : OutsideComponent Γ P,
      (r : ℝ) / (10 * R * A) ≤ outsideComponentRank Γ P c := by
  classical
  let ι := OutsideComponent Γ P
  letI : Fintype ι := SetLike.instFintype
  let t : ℝ := (r : ℝ) / (10 * R * A)
  by_contra hnot
  have hstrict : ∀ c : ι, (outsideComponentRank Γ P c : ℝ) < t := by
    intro c
    have hnotc : ¬ t ≤ (outsideComponentRank Γ P c : ℝ) := by
      intro hc
      exact hnot ⟨c, hc⟩
    exact lt_of_not_ge hnotc
  have hs : (∑ c : ι, (outsideComponentRank Γ P c : ℝ)) < ∑ _c : ι, t :=
    Finset.sum_lt_sum (fun c _ => le_of_lt (hstrict c))
      (by
        obtain ⟨c⟩ := hnonempty
        exact ⟨c, Finset.mem_univ _, hstrict c⟩)
  have htpos : 0 ≤ t := by
    dsimp [t]
    positivity
  have hsumConst : (∑ _c : ι, t) = (Fintype.card ι : ℝ) * t := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card ι : ℝ) ≤ A := by
    exact_mod_cast profile.componentCount_le
  have htotal := profile.rank_sum_lower
  rw [hsumConst] at hs
  have hupper : (Fintype.card ι : ℝ) * t ≤ (A : ℝ) * t :=
    mul_le_mul_of_nonneg_right hcard htpos
  have hcontr : (∑ c : ι, (outsideComponentRank Γ P c : ℝ)) <
      (r : ℝ) / (10 * R) := by
    calc
      _ < (Fintype.card ι : ℝ) * ((r : ℝ) / (10 * R * A)) := hs
      _ ≤ (A : ℝ) * ((r : ℝ) / (10 * R * A)) := hupper
      _ = (r : ℝ) / (10 * R) := by
        field_simp
        ring
  exact (not_lt_of_ge htotal) hcontr

/-- Cubic ambient degree and the Euler identity imply that a component's
cycle rank is at most its number of vertices, once its boundary is nonempty. -/
theorem componentRank_le_order
    {Γ : FiniteMultiGraph} {P : Finset Γ.Vertex} {r R A : ℕ}
    (profile : ComponentExtractionProfile Γ P r R A)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (c : OutsideComponent Γ P) :
    outsideComponentRank Γ P c ≤ (outsideComponentVertices Γ P c).card := by
  classical
  have horder : 0 < (outsideComponentVertices Γ P c).card := by
    obtain ⟨v, hv⟩ := c.nonempty_supp
    have hvH : v.1 ∈ outsideComponentVertices Γ P c := by
      change v.1 ∈ Finset.univ.filter _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v, hv, rfl⟩
    exact Finset.card_pos.mpr ⟨v.1, hvH⟩
  have hcut : 1 ≤ (cutEdges Γ (outsideComponentVertices Γ P c)).card := by
    have hne := outsideComponent_cut_nonempty Γ P hconn hP c
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  have heuler := componentRank_incidence_formula profile c
  omega

/-- The actual exterior of a chosen outside component is bounded by a core
component count plus the number of newly protected vertices, as in Step 7. -/
theorem exterior_bound_of_component_rank
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected)
    (c : (Γ.toSimpleGraph.induce (↑(Pᶜ) : Set Γ.Vertex)).ConnectedComponent)
    (K : SimpleGraph Γ.Vertex) (Aset B C : Finset Γ.Vertex)
    (hA : Aset ⊆ P) (hP : P ⊆ Aset ∪ B ∪ C)
    (hAdj : ∀ u v, K.Adj u v → Γ.toSimpleGraph.Adj u v)
    (n B₃ m₂ Cext R : ℕ)
    (hcore : Fintype.card (K.induce (↑Aset : Set Γ.Vertex)).ConnectedComponent ≤ n)
    (hn : n < 5 * R) (hB : B.card < B₃ * R)
    (hC : C.card < 2 * m₂ * R ^ 2) (hR : 1 ≤ R)
    (hconst : 5 + B₃ + 2 * m₂ ≤ Cext) :
    exteriorComponentCount Γ (outsideComponentVertices Γ P c) ≤ Cext * R ^ 2 := by
  have hbound := exteriorComponentCount_le_core_plus_two_sets_of_outside_component
    Γ K Aset P B C hA hP hAdj hcore hconn c
  exact cleanupExteriorCount_le_quadratic R B₃ m₂ Cext n B.card C.card
    (exteriorComponentCount Γ (outsideComponentVertices Γ P c))
    hR hconst hn hB hC hbound

/-- Combined Steps 6--7 extraction. The profile supplies the rank sum after
deleting protected incidences, the cubic-component Euler accounting, and the
attachment/cut bounds. The remaining root-exterior estimate is discharged by
the protected-set component lemmas. -/
theorem exists_cleanup_component
    (Γ : FiniteMultiGraph) (P : Finset Γ.Vertex)
    (hconn : Γ.toSimpleGraph.Connected) (hP : P.Nonempty)
    (R r A B₃ m₂ Cext n : ℕ)
    (profile : ComponentExtractionProfile Γ P r R A)
    (hRpos : 0 < R) (hApos : 0 < A)
    (hnonempty : Nonempty (OutsideComponent Γ P))
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
      (outsideComponentVertices Γ P c).card < Γ.vertexCount ∧
      r ≤ (outsideComponentVertices Γ P c).card * 2 ^ (8 * R) ∧
      (cutEdges Γ (outsideComponentVertices Γ P c)).card ≤ 2 ^ (5 * R) ∧
      exteriorComponentCount Γ (outsideComponentVertices Γ P c) ≤ Cext * R ^ 2 := by
  classical
  obtain ⟨c, hshare⟩ := exists_component_rank_ge_average
    profile hRpos hApos hnonempty
  have horderRank := componentRank_le_order profile hconn hP c
  have hshare' : (r : ℝ) ≤ (10 * R * A : ℝ) * outsideComponentRank Γ P c := by
    have hden : (0 : ℝ) < 10 * R * A := by positivity
    simpa [mul_comm] using (div_le_iff₀ hden).mp hshare
  have hscale' : (10 * R * A : ℝ) ≤ (2 : ℝ) ^ (8 * R) := by
    exact_mod_cast hscale
  have hrankOrder : (outsideComponentRank Γ P c : ℝ) ≤
      (outsideComponentVertices Γ P c).card := by
    exact_mod_cast horderRank
  have horderReal : (r : ℝ) ≤
      (outsideComponentVertices Γ P c).card * (2 : ℝ) ^ (8 * R) := by
    calc
      (r : ℝ) ≤ (10 * R * A : ℝ) * outsideComponentRank Γ P c := hshare'
      _ ≤ (2 : ℝ) ^ (8 * R) *
          (outsideComponentVertices Γ P c).card :=
        mul_le_mul hscale' hrankOrder (by positivity) (by positivity)
      _ = (outsideComponentVertices Γ P c).card * (2 : ℝ) ^ (8 * R) := by ring
  have horderNat : r ≤
      (outsideComponentVertices Γ P c).card * 2 ^ (8 * R) := by
    exact_mod_cast horderReal
  have hden : (0 : ℝ) < 10 * R * A := by positivity
  have hDleR : 10 * R * A ≤ r := le_trans hscale hr
  have hthreshold : 1 ≤ (r : ℝ) / (10 * R * A) :=
    (le_div_iff₀ hden).2 (by simpa using (show (10 * R * A : ℝ) ≤ r by exact_mod_cast hDleR))
  have hrankPositive : 0 < outsideComponentRank Γ P c := by
    have hge : (1 : ℝ) ≤ outsideComponentRank Γ P c := hthreshold.trans hshare
    exact_mod_cast hge
  have hcutNat : (cutEdges Γ (outsideComponentVertices Γ P c)).card ≤
      2 ^ (5 * R) := (profile.component_cut_le c).trans hAbound
  have hext := exterior_bound_of_component_rank Γ P hconn c K Aset B C
    hAset hPcover hAdj n B₃ m₂ Cext R hcore hn hB hC hR hconst
  have hrootProper : (outsideComponentVertices Γ P c).card < Γ.vertexCount := by
    have hneq : outsideComponentVertices Γ P c ≠ Finset.univ := by
      intro heq
      obtain ⟨p, hp⟩ := hP
      have hpH : p ∈ outsideComponentVertices Γ P c := by
        rw [heq]
        exact Finset.mem_univ _
      exact (Finset.disjoint_left.mp
        (componentVertexSet_disjoint Γ.toSimpleGraph P c)) hpH hp
    have hss : outsideComponentVertices Γ P c ⊂ Finset.univ :=
      Finset.ssubset_univ_iff.mpr hneq
    have hlt := Finset.card_lt_card hss
    simpa [FiniteMultiGraph.Vertex] using hlt
  exact ⟨c, hrankPositive, hrootProper, horderNat, hcutNat, hext⟩

end Erdos1016.Proof.ComponentExtraction

end
