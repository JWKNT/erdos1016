import Erdos1016.ExactMaximum.NetJoin
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The adjacent-port case of the gap theorem

A path that uses the edge between its terminals is that single edge.
The other paths use at most half the affine parity fiber when the edge lies on a cycle.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleAdjacentGap
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance adjacentGapDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A path containing a direct edge between its terminals is the singleton path. -/
theorem path_eq_unit_of_selected {s t : V} {e : E} (he : N.Joins e s t)
    {x : N.Word} (hx : N.IsPathWord s t x) (hxe : x e ≠ 0) : x = unitWord e := by
  apply word_eq_of_add_eq_zero
  apply hx.eq_zero_of_even_subword (N.isSubword_unitWord hxe).add_self
  rw [map_add,hx.boundary_eq,(N.isPathWord_unitWord he).boundary_eq]
  exact word_add_self _

/-- At most one terminal path uses the direct terminal edge. -/
theorem numPaths_le_avoiding_add_one {s t : V} {e : E} (he : N.Joins e s t) :
    N.numPaths s t ≤ Nat.card {x : N.Word // N.IsPathWord s t x ∧ x e = 0} + 1 := by
  classical
  let A : Finset N.Word := Finset.univ.filter fun x => N.IsPathWord s t x ∧ x e = 0
  have hsub : (Finset.univ.filter fun x => N.IsPathWord s t x) ⊆ insert (unitWord e) A := by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).2
    by_cases hxe : x e = 0
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hxe⟩)
    · exact Finset.mem_insert.mpr (Or.inl (path_eq_unit_of_selected N he hp hxe))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  simpa only [numPaths,Nat.card_eq_fintype_card,Fintype.card_subtype,A] using hh

/-- Translation by an actual cycle pairs the two edge-coordinate classes of the affine fiber. -/
theorem two_mul_avoiding_paths_le {s t : V} {e : E} (he : N.Joins e s t)
    {z : N.Word} (hz : N.IsCycleWord z) (hze : z e ≠ 0) :
    2 * Nat.card {x : N.Word // N.IsPathWord s t x ∧ x e = 0} ≤ 2 ^ networkRank N := by
  let A := {x : N.Word // N.IsPathWord s t x ∧ x e = 0}
  let f : A ⊕ A → Parity.Fiber N.boundary (N.pathDemand s t) := fun x =>
    match x with
    | Sum.inl x => ⟨x.1,x.2.1.boundary_eq⟩
    | Sum.inr x => ⟨x.1+z,x.2.1.add_cycle_boundary hz⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · have h : a.1 = b.1 := congrArg (fun v : Parity.Fiber N.boundary (N.pathDemand s t) => v.1) hab
      exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h : a.1 = b.1+z := congrArg (fun v : Parity.Fiber N.boundary (N.pathDemand s t) => v.1) hab
      have hh := congrFun h e
      simp only [Pi.add_apply,a.2.2,b.2.2,zero_add] at hh
      exact hze hh.symm
    · exfalso
      have h : a.1+z = b.1 := congrArg (fun v : Parity.Fiber N.boundary (N.pathDemand s t) => v.1) hab
      have hh := congrFun h e
      simp only [Pi.add_apply,a.2.2,b.2.2,zero_add] at hh
      exact hze hh
    · have h : a.1+z = b.1+z := congrArg (fun v : Parity.Fiber N.boundary (N.pathDemand s t) => v.1) hab
      exact congrArg Sum.inr (Subtype.ext (add_right_cancel h))
  have hh := Nat.card_le_card_of_injective f hf
  rw [N.card_joins s t ⟨unitWord e,(N.isPathWord_unitWord he).boundary_eq⟩,Nat.card_sum] at hh
  change 2 * Nat.card A ≤ 2 ^ networkRank N
  omega

/-- A direct terminal edge on a cycle gives the exact half-capacity bound with one extra path. -/
theorem two_mul_numPaths_le {s t : V} {e : E} (he : N.Joins e s t)
    {z : N.Word} (hz : N.IsCycleWord z) (hze : z e ≠ 0) :
    2 * N.numPaths s t ≤ 2 ^ networkRank N + 2 := by
  have h1 := numPaths_le_avoiding_add_one N he
  have h2 := two_mul_avoiding_paths_le N he hz hze
  omega

/-- In rank at least two, adjacent ports in a bridgeless pole lose at least one quarter. -/
theorem adjacent_port_quarter (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (hadj : N.graph.Adj s t) (hrank : 2 ≤ networkRank N) :
    4 * N.numPaths s t ≤ 3 * 2 ^ networkRank N := by
  obtain ⟨e,he⟩ := hadj
  obtain ⟨z,hz,hze⟩ := hN.bridgeless e
  have hh := two_mul_numPaths_le N he hz hze
  have hpow : 4 ≤ 2 ^ networkRank N := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2 ^ networkRank N := Nat.pow_le_pow_right (by decide) hrank
  omega

end Erdos1016.ExactMaximumSupport.PoleAdjacentGap
