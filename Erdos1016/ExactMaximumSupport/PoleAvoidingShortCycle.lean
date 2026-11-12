import Erdos1016.ExactMaximumSupport.PoleThinLayers
import Erdos1016.ExactMaximumSupport.OrdinaryLayerOrder
import Erdos1016.ExactMaximumSupport.ThinLayerShortCycle

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A short cycle avoiding a prescribed finite set in a path-rich pole

Mark the distance levels of nonordinary vertices and of the forbidden set.
A long enough source-to-target interval then has four consecutive thin layers
avoiding every marked level. Their actual short cycle avoids the forbidden set.
The pole itself remains connected, bridgeless, and has exactly two ports.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle
open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance poleAvoidingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A bounded nonordinary vertex set leaves a short cycle away from any bounded forbidden set. -/
theorem exists_cycle_avoiding_of_nonordinary_bound (s t : V)
    (hN : N.IsBridgelessTwoPole s t) (C k : ℕ)
    (hcount : Nat.card {v : V // ¬ N.IsOrdinaryLayer s t (N.graph.dist s v)} ≤ C)
    (X : Finset V) (hX : X.card ≤ k) (hrank : 5*C+4*k+5 ≤ networkRank N) :
    ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
      ∀ v, 0 < N.deg z v → v ∉ X := by
  let level : V → ℕ := N.graph.dist s
  let Q : Finset V := Finset.univ.filter fun v => ¬ N.IsOrdinaryLayer s t (level v)
  let bad : Finset ℕ := Q.image level ∪ X.image level
  have hQ : Q.card ≤ C := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,Q,level] using hcount
  have hbad : bad.card ≤ C+k := by
    have hu := Finset.card_union_le (Q.image level) (X.image level)
    have hq := Finset.card_image_le (s := Q) (f := level)
    have hx := Finset.card_image_le (s := X) (f := level)
    dsimp only [bad]
    omega
  have hthin (j : ℕ) (_hj : 1 ≤ j) (hjt : j < N.graph.dist s t) (hnot : j ∉ bad) :
      Nat.card {v : V // N.graph.dist s v = j} = 2 := by
    obtain ⟨v,hv⟩ := BridgelessLayers.exists_vertex_at_distance N hN.connected s t j (by omega)
    have ho : N.IsOrdinaryLayer s t j := by
      by_contra hno
      apply hnot
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨v,?_,hv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [level,hv] using hno⟩
    exact ho.1.2.2
  have hdegree (v : V) : N.deg (fun _ => 1) v ≤ 3 := by
    by_cases hs : v=s
    · subst v
      exact hN.deg_s.le.trans (by decide)
    by_cases ht : v=t
    · subst v
      exact hN.deg_t.le.trans (by decide)
    exact (hN.deg_other v hs ht).le
  have hdefect := OrdinaryLayerOrder.rank_le_distance_add_bad N s t hN C hcount
  have hlength : 4*(C+k+1) < N.graph.dist s t := by omega
  obtain ⟨z,hz,hsize,hsupport⟩ := ThinLayerShortCycle.exists_cycle_of_few_bad_layers
    N hN.connected s t bad (C+k) hdegree hN.deg_other hbad hthin hlength
  refine ⟨z,hz,hsize,?_⟩
  intro v hv hmem
  apply (hsupport v hv).2.2
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem level hmem)

/-- Uniformly, a sufficiently large path-rich bridgeless two-pole has a short cycle
avoiding any prescribed set of at most `k` vertices. -/
theorem exists_avoiding_constant :
    ∃ C : ℕ, ∀ (k : ℕ) (V E : Type) [Fintype V] [Fintype E]
      (N : Network V E) (s t : V),
      N.IsBridgelessTwoPole s t →
      501*2^networkRank N ≤ 1000*N.numPaths s t →
      ∀ X : Finset V, X.card ≤ k → 5*C+4*k+5 ≤ networkRank N →
      ∃ z : N.Word, N.IsCycleWord z ∧ size z ≤ 4 ∧
        ∀ v, 0 < N.deg z v → v ∉ X := by
  obtain ⟨C,hC⟩ := thinLayersStatement
  refine ⟨C,?_⟩
  intro k V E _ _ N s t hN hpaths X hX hrank
  exact exists_cycle_avoiding_of_nonordinary_bound N s t hN C k
    (hC V E N s t hN hpaths).2 X hX hrank

end Erdos1016.ExactMaximumSupport.PoleAvoidingShortCycle
