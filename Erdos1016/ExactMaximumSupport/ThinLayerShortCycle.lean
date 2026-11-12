import Erdos1016.ExactMaximumSupport.NetworkFourLayers
import Erdos1016.ExactMaximumSupport.GoodLayerBlock

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A short cycle away from exceptional distance layers

Four consecutive good interior layers contain an actual physical cycle.
The rank threshold is the one used in Corollary 5.6 of the paper.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThinLayerShortCycle
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance thinLayerShortCycleDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A long enough run with few exceptional layers contains a physical short cycle. -/
theorem exists_cycle_of_few_bad_layers
    (hconn : N.graph.Connected) (s t : V) (bad : Finset ℕ) (B : ℕ)
    (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hcubic : ∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3)
    (hbad : bad.card ≤ B)
    (hthin : ∀ j, 1 ≤ j → j < N.graph.dist s t → j ∉ bad →
      Nat.card {v : V // N.graph.dist s v = j} = 2)
    (hlength : 4 * (B + 1) < N.graph.dist s t) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v →
        1 ≤ N.graph.dist s v ∧ N.graph.dist s v < N.graph.dist s t ∧
          N.graph.dist s v ∉ bad := by
  obtain ⟨k,hk,hkl,hgood⟩ := GoodLayerBlock.exists_four_good bad B
    (N.graph.dist s t - 1) hbad (by omega)
  have hlt : k + 3 < N.graph.dist s t := by omega
  have hcard (i : Fin 4) :
      Nat.card {v : V // N.graph.dist s v = k + i.val} = 2 := by
    have hi := i.isLt
    apply hthin (k + i.val) (by omega) (by omega)
    exact hgood _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hmiddle (v : V)
      (hv : N.graph.dist s v = k + 1 ∨ N.graph.dist s v = k + 2) :
      N.deg (fun _ => 1) v = 3 := by
    apply hcubic v
    · intro hvs
      subst v
      simp only [SimpleGraph.dist_self] at hv
      omega
    · intro hvt
      subst v
      omega
  obtain ⟨z,hz,hlen,hsupport⟩ :=
    NetworkFourLayers.exists_cycle_of_four_distance_layers N hconn s k hk hcard
      hdegree hmiddle
  refine ⟨z,hz,hlen,?_⟩
  intro v hv
  obtain ⟨hlo,hhi⟩ := hsupport v hv
  exact ⟨by omega, by omega, hgood _ (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)⟩

/-- The paper's rank and exceptional-layer budgets imply an actual short cycle. -/
theorem exists_cycle_of_rank_budget
    (hconn : N.graph.Connected) (s t : V) (bad : Finset ℕ) (C g : ℕ)
    (hdegree : ∀ v, N.deg (fun _ => 1) v ≤ 3)
    (hcubic : ∀ v, v ≠ s → v ≠ t → N.deg (fun _ => 1) v = 3)
    (hbad : bad.card ≤ 2 * C + 2 * g)
    (hthin : ∀ j, 1 ≤ j → j < N.graph.dist s t → j ∉ bad →
      Nat.card {v : V // N.graph.dist s v = j} = 2)
    (hdefect : networkRank N ≤ N.graph.dist s t + C)
    (hrank : 9 * C + 8 * g + 9 ≤ networkRank N) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v →
        1 ≤ N.graph.dist s v ∧ N.graph.dist s v < N.graph.dist s t ∧
          N.graph.dist s v ∉ bad := by
  exact exists_cycle_of_few_bad_layers N hconn s t bad (2 * C + 2 * g)
    hdegree hcubic hbad hthin (by omega)

end Erdos1016.ExactMaximumSupport.ThinLayerShortCycle
