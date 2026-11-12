import Erdos1016.ExactMaximumSupport.PoleMarginLayers
import Erdos1016.ExactMaximumSupport.NetworkShortCycleCut

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A cubic cyclic shore in a large path-rich bridgeless two-pole

Avoid the two ports and the specified exceptional vertices with a short cycle.
Its actual support has a cyclic complement and at most four crossing edges.
This proves the bridgeless two-pole part of the pole-only cyclic-shore input.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleCyclicShore
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

/-- A short actual cycle gives a cubic cyclic shore away from every prescribed bounded set. -/
theorem exists_avoiding_constant (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, ∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V), N.IsBridgelessTwoPole s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t →
      ∀ X : Finset V, X.card ≤ k → 5*C+4*k+13 ≤ networkRank N →
      ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
        N.IsCyclicCut (fun v => 0 < N.deg z v) ∧
        N.cutSize (fun v => 0 < N.deg z v) ≤ 4 ∧
        ∀ v, 0 < N.deg z v → N.deg (fun _ => 1) v = 3 ∧ v ∉ X := by
  classical
  obtain ⟨C,hC⟩ := PoleMarginLayers.exists_avoiding_constant ε hε
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hpaths X hX hrank
  let Y := X ∪ ({s,t} : Finset V)
  have hY : Y.card ≤ k+2 := by
    have hh := Finset.card_union_le X ({s,t} : Finset V)
    rw [Finset.card_pair hN.ne] at hh
    dsimp only [Y]
    omega
  obtain ⟨z,hz,hsize,havoid⟩ := hC (k+2) V E N s t hN hpaths Y hY (by omega)
  have hdegree (v : V) : N.deg (fun _ => 1) v ≤ 3 := by
    by_cases hs : v=s
    · subst v; rw [hN.deg_s]; decide
    by_cases ht : v=t
    · subst v; rw [hN.deg_t]; decide
    exact (hN.deg_other v hs ht).le
  obtain ⟨hcut,hcutsize⟩ := NetworkShortCycleCut.cycle_support_cyclic_cut N hdegree z hz 4 hsize
    (by omega)
  refine ⟨z,hz,hsize,hcut,hcutsize,?_⟩
  intro v hv
  have hh : v ∉ X ∧ v ≠ s ∧ v ≠ t := by
    simpa only [Y,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] using havoid v hv
  exact ⟨hN.deg_other v hh.2.1 hh.2.2,hh.1⟩

/-- The pole alone has a cubic cyclic shore once its rank exceeds a margin-dependent constant. -/
theorem exists_cubic_shore_constant (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V), N.IsBridgelessTwoPole s t →
      (1/2 + ε) * (2:ℝ)^networkRank N ≤ N.numPaths s t → B ≤ networkRank N →
      ∃ S : V → Prop, N.IsCyclicCut S ∧ N.cutSize S ≤ 4 ∧
        ∀ v, S v → N.deg (fun _ => 1) v = 3 := by
  obtain ⟨C,hC⟩ := exists_avoiding_constant ε hε
  refine ⟨5*C+13,?_⟩
  intro V E _ _ N s t hN hpaths hrank
  obtain ⟨z,hz,hsize,hcut,hcutsize,hdeg⟩ := hC 0 V E N s t hN hpaths ∅ (by simp) (by omega)
  exact ⟨fun v => 0 < N.deg z v,hcut,hcutsize,fun v hv => (hdeg v hv).1⟩

end Erdos1016.ExactMaximumSupport.PoleCyclicShore
