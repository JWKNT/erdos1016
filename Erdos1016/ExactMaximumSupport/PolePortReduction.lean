import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleSides

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Suppress extra ports while preserving the exact counts

Above half of the affine path capacity, every extra port has distinct neighbours.
Repeated physical suppression leaves exactly the designated two ports.
The rank, path count, and cycle count are preserved without a fixed margin.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PolePortReduction
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance portReductionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual two-pole reduction preserves all three numerical invariants. -/
theorem exists_two_pole (V E : Type) [Fintype V] [Fintype E]
    (N : Network V E) (hN : N.IsWeakPole) (s t : V)
    (hs : N.IsPort s) (ht : N.IsPort t) (hst : s ≠ t)
    (hmany : 2 ^ networkRank N < 2 * N.numPaths s t) :
    ∃ (E' : Type) (_ : Fintype E') (N' : Network V E'),
      N'.IsWeakTwoPole s t ∧ networkRank N' = networkRank N ∧
        N'.numPaths s t = N.numPaths s t ∧ N'.numCycles = N.numCycles := by
  have key : ∀ n : ℕ, ∀ (E : Type) [Fintype E] (N : Network V E), Fintype.card E = n →
      N.IsWeakPole → N.IsPort s → N.IsPort t →
      2 ^ networkRank N < 2 * N.numPaths s t →
      ∃ (E' : Type) (_ : Fintype E') (N' : Network V E'),
        N'.IsWeakTwoPole s t ∧ networkRank N' = networkRank N ∧
          N'.numPaths s t = N.numPaths s t ∧ N'.numCycles = N.numCycles := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro E _ N hcard hN hs ht hmany
      by_cases hall : ∀ z, N.IsPort z → z = s ∨ z = t
      · exact ⟨E,inferInstance,N,⟨hN,hs,ht,hst,hall⟩,rfl,rfl,rfl⟩
      · obtain ⟨z,hz⟩ := not_forall.1 hall
        obtain ⟨hzport,hzst⟩ := Classical.not_imp.1 hz
        have hzs : z ≠ s := fun h => hzst (Or.inl h)
        have hzt : z ≠ t := fun h => hzst (Or.inr h)
        obtain ⟨e,f,u,w,hef,he,hf,honly⟩ := N.exists_two_edges_of_deg_two hzport
        have huw : u ≠ w := by
          intro huw
          subst huw
          have hdeg : ∀ x, N.deg (fun _ => 1) x ≤ 3 := by
            intro x
            rcases hN.1 x with h | h | h <;> omega
          have hh := N.two_mul_numPaths_le_of_digon hdeg hs ht hzs hzt hef he hf honly
          omega
        have T : Thread N e f u z w := ⟨he,hf,hef,huw,honly⟩
        have hlt : Fintype.card {g : E // g ≠ f} < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (fun h : f ≠ f => h rfl)
        obtain ⟨E',inst,N',hN',hr,hp,hc⟩ := ih _ hlt {g : E // g ≠ f}
          (N.suppress e f u w huw) rfl (T.isWeakPole_suppress hN)
          ((T.isPort_suppress (Ne.symm hzs)).2 hs)
          ((T.isPort_suppress (Ne.symm hzt)).2 ht)
          (by rw [T.networkRank_suppress,T.numPaths_suppress (Ne.symm hzs) (Ne.symm hzt)]
              exact hmany)
        refine ⟨E',inst,N',hN',?_,?_,?_⟩
        · exact hr.trans T.networkRank_suppress
        · exact hp.trans (T.numPaths_suppress (Ne.symm hzs) (Ne.symm hzt))
        · exact hc.trans T.numCycles_suppress
  exact key _ E N rfl hN hs ht hmany

end Erdos1016.ExactMaximumSupport.PolePortReduction
