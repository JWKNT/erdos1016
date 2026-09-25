import Erdos1016.Decomposition.TwoCore.MaximalCore
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
noncomputable section
namespace Erdos1016.Proof.TwoCorePathGeometry
open Erdos1016.Nonbacktracking.FiniteTwoCore
local instance corePathDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem degreeWithin_mono {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) {A B : Finset V} (hAB : A ⊆ B) (v : V) :
    degreeWithin J A v ≤ degreeWithin J B v := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ hAB)

/-- Every simple path between vertices of the full two-core stays in the
core, provided it stays in the original region. -/
theorem path_support_subset_twoCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) (region : Finset V)
    {u v : V} (p : J.Walk u v) (hp : p.IsPath)
    (hu : u ∈ vertices J region) (hv : v ∈ vertices J region)
    (hsupport : ∀ z ∈ p.support, z ∈ region) :
    ∀ z ∈ p.support, z ∈ vertices J region := by
  let C := vertices J region
  let A := C ∪ p.support.toFinset
  have hAreg : A ⊆ region := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact vertices_subset J region hz
    · exact hsupport z (List.mem_toFinset.mp hz)
  have hmin : MinTwo J A := by
    intro z hz
    by_cases hzC : z ∈ C
    · exact (vertices_minTwo J region z hzC).trans
        (degreeWithin_mono J Finset.subset_union_left z)
    · have hzpath : z ∈ p.support := by
        exact List.mem_toFinset.mp ((Finset.mem_union.mp hz).resolve_left hzC)
      obtain ⟨i, hi, hib⟩ := (SimpleGraph.Walk.mem_support_iff_exists_getVert).mp hzpath
      have hi0 : i ≠ 0 := by
        intro h
        have huz : u = z := by simpa [h] using hi
        exact hzC (huz ▸ hu)
      have hil : i < p.length := by
        have hine : i ≠ p.length := by
          intro h
          have hvz : v = z := by simpa [h] using hi
          exact hzC (hvz ▸ hv)
        omega
      have htwo := hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil
      rw [hi] at htwo
      have hsub : p.toSubgraph.neighborSet z ⊆
          (↑(A.filter (fun w => J.Adj z w)) : Set V) := by
        intro w hw
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_union_right _ (List.mem_toFinset.mpr
          ((p.mem_verts_toSubgraph).mp (p.toSubgraph.edge_vert hw.symm))),
          p.toSubgraph.adj_sub hw⟩
      have hcard := Set.ncard_le_ncard hsub
      rw [htwo] at hcard
      simpa only [Set.ncard_coe_Finset] using hcard
  have hAC := maximal J region A hAreg hmin
  intro z hz
  exact hAC (Finset.mem_union_right _ (List.mem_toFinset.mpr hz))

end Erdos1016.Proof.TwoCorePathGeometry
