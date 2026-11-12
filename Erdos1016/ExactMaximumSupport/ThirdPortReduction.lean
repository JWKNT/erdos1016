import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleSides
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Suppression with a marked original thread

The unused port of a full three-pole is suppressed without forgetting its
two physical edge labels. The retained label is the edge to be subdivided
when the third port is restored. Isolated vertices remain in the network.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortReduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance thirdPortDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A full tested pair excludes a digon at the unused port. -/
theorem thread_of_full_pair {s t v : V} (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t) (hv : N.IsPort v)
    (hsv : s ≠ v) (htv : t ≠ v) (hfull : N.IsFullPair s t) :
    ∃ (e f : E) (u w : V), N.Thread e f u v w := by
  obtain ⟨e,f,u,w,hef,he,hf,honly⟩ := N.exists_two_edges_of_deg_two hv
  have huw : u ≠ w := by
    intro h
    subst w
    have hdeg : ∀ z, N.deg (fun _ => 1) z ≤ 3 := by
      intro z
      rcases hN.1 z with h | h | h <;> omega
    have hhalf := N.two_mul_numPaths_le_of_digon hdeg hs ht hsv.symm htv.symm
      hef he hf honly
    change N.numPaths s t = 2 ^ networkRank N at hfull
    have hpos := Nat.two_pow_pos (networkRank N)
    omega
  exact ⟨e,f,u,w,⟨he,hf,hef,huw,honly⟩⟩

omit [Fintype V] in
/-- Suppressing the sole unused port gives exactly the designated two ports. -/
theorem two_pole_of_thread {s t v u w : V} {e f : E}
    (T : N.Thread e f u v w) (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t) (hst : s ≠ t)
    (hsv : s ≠ v) (htv : t ≠ v)
    (honly : ∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v) :
    (N.suppress e f u w T.huw).IsWeakTwoPole s t := by
  refine ⟨T.isWeakPole_suppress hN,(T.isPort_suppress hsv).2 hs,
    (T.isPort_suppress htv).2 ht,hst,?_⟩
  intro z hz
  have hzv : z ≠ v := by
    intro h
    subst z
    have hh := T.deg_suppress_v (fun _ => 1)
    change (N.suppress e f u w T.huw).deg (fun _ => 1) v = 2 at hz
    omega
  exact (honly z ((T.isPort_suppress hzv).1 hz)).elim Or.inl
    (fun h => h.elim Or.inr (fun h => (hzv h).elim))

/-- The concrete marked suppression, with every numerical invariant and the
retained physical label recorded explicitly. -/
theorem exists_full_two_pole_thread (s t v : V) (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t) (hv : N.IsPort v)
    (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (honly : ∀ z, N.IsPort z → z = s ∨ z = t ∨ z = v)
    (hfull : N.IsFullPair s t) :
    ∃ (e f : E) (u w : V) (T : N.Thread e f u v w),
      (N.suppress e f u w T.huw).IsWeakTwoPole s t ∧
      (N.suppress e f u w T.huw).IsFullPair s t ∧
      networkRank (N.suppress e f u w T.huw) = networkRank N ∧
      (N.suppress e f u w T.huw).numPaths s t = N.numPaths s t ∧
      (N.suppress e f u w T.huw).numCycles = N.numCycles ∧
      (N.suppress e f u w T.huw).Joins ⟨e,T.hef⟩ u w ∧
      (N.suppress e f u w T.huw).deg (fun _ => 1) v = 0 := by
  obtain ⟨e,f,u,w,T⟩ := thread_of_full_pair N hN hs ht hv hsv htv hfull
  refine ⟨e,f,u,w,T,two_pole_of_thread N T hN hs ht hst hsv htv honly,?_,
    T.networkRank_suppress,T.numPaths_suppress hsv htv,T.numCycles_suppress,
    N.suppress_joins_of_eq T.huw ⟨e,T.hef⟩ rfl,T.deg_suppress_v _⟩
  change (N.suppress e f u w T.huw).numPaths s t =
    2 ^ networkRank (N.suppress e f u w T.huw)
  rw [T.numPaths_suppress hsv htv,T.networkRank_suppress]
  exact hfull

/-- Suppression preserves the assertion that every physical label lies on a
cycle, including the retained label and the deleted thread label. -/
theorem bridgeless_suppress_iff {e f : E} {u v w : V} (T : N.Thread e f u v w) :
    (N.suppress e f u w T.huw).IsBridgeless ↔ N.IsBridgeless := by
  constructor
  · intro h g
    by_cases hgf : g = f
    · obtain ⟨z,hz,hze⟩ := h ⟨e,T.hef⟩
      refine ⟨grow e f T.hef z,(T.isCycleWord_grow_iff z).2 hz,?_⟩
      rw [hgf,grow_apply_f]
      exact hze
    · obtain ⟨z,hz,hzg⟩ := h ⟨g,hgf⟩
      refine ⟨grow e f T.hef z,(T.isCycleWord_grow_iff z).2 hz,?_⟩
      rw [grow_apply_of_ne T.hef z hgf]
      exact hzg
  · intro h g
    obtain ⟨z,hz,hzg⟩ := h g.1
    have hzero : N.boundary z v = 0 := by rw [hz.boundary_eq_zero]; rfl
    refine ⟨pull (fun a => a ≠ f) z,(T.isCycleWord_grow_iff _).1 ?_,hzg⟩
    rw [T.grow_pull_of_even hzero]
    exact hz

end Erdos1016.ExactMaximumSupport.ThirdPortReduction
