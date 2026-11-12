import Erdos1016.ExactMaximumSupport.PoleTrackedSuppression
import Erdos1016.ExactMaximumSupport.Shortening.ShortCycleTransversal

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Suppress extra ports while retaining a short-cycle transversal

The reduction keeps exact rank and path counts. Each suppression adds at most
three marked vertices. No cyclic-shore conclusion or lifting theorem is used.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalSuppression
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
open PoleTrackedSuppression ShortCycleTransversal
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V : Type} [Fintype V]

/-- The reduced actual two-pole retains the original rank and tested path count. -/
def Reduction {E E' : Type} [Fintype E] [Fintype E'] (N : Network V E)
    (s t : V) (X : Finset V) (g : ℕ) (M : Network V E') (Y : Finset V) : Prop :=
  M.IsWeakTwoPole s t ∧ networkRank M=networkRank N ∧
    M.numPaths s t=N.numPaths s t ∧ X⊆Y ∧ Y.card≤X.card+3*g ∧ Hits M Y

/-- Every extra port is suppressed, with a bounded transversal of short cycles. -/
theorem exists_reduction (g : ℕ) :
    ∀ (E : Type) [Fintype E] (N : Network V E) (s t : V) (X : Finset V),
      N.IsWeakPole → N.IsPort s → N.IsPort t → s≠t →
      (extraPorts N s t).card≤g → 2^networkRank N<2*N.numPaths s t → Hits N X →
      ∃ (E' : Type) (iE' : Fintype E'),letI := iE';
        ∃ (M : Network V E') (Y : Finset V),Reduction N s t X g M Y := by
  classical
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro E _ N s t X hN hs ht hst hcount hrich hhit
    by_cases hall : ∀v,N.IsPort v → v=s ∨ v=t
    · exact ⟨E,inferInstance,N,X,⟨hN,hs,ht,hst,hall⟩,rfl,rfl,
        Finset.Subset.refl _,by omega,hhit⟩
    · obtain ⟨v,hv⟩ := not_forall.mp hall
      obtain ⟨hvp,hvst⟩ := Classical.not_imp.mp hv
      have hvs : v≠s := fun h => hvst (Or.inl h)
      have hvt : v≠t := fun h => hvst (Or.inr h)
      have hmem : v∈extraPorts N s t := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hvp,hvs,hvt⟩
      obtain ⟨e,f,u,w,T⟩ := exists_thread N hN hs ht hmem hrich
      let M := N.suppress e f u w T.huw
      let X' := insert u (insert v (insert w X))
      have hX : X⊆X' := by intro x hx; simp [X',hx]
      have hXcard : X'.card≤X.card+3 := marks_card_le (u:=u) (v:=v) (w:=w) X
      have hdecrease : (extraPorts M s t).card+1=(extraPorts N s t).card := by
        rw [extraPorts_suppress N T,Finset.card_erase_of_mem hmem]
        have hp := Finset.card_pos.mpr ⟨v,hmem⟩
        omega
      have hlt : (extraPorts M s t).card<g := by omega
      have hMrich : 2^networkRank M<2*M.numPaths s t := by
        dsimp only [M]
        rw [T.networkRank_suppress,T.numPaths_suppress hvs.symm hvt.symm]
        exact hrich
      obtain ⟨E',iE',L,Y,hL⟩ := ih _ hlt _ M s t X'
        (T.isWeakPole_suppress hN) ((T.isPort_suppress hvs.symm).mpr hs)
        ((T.isPort_suppress hvt.symm).mpr ht) hst (le_refl _) hMrich
        (hits_suppress T X hhit)
      letI := iE'
      obtain ⟨hLp,hLr,hLpath,hXY,hYcard,hLhit⟩ := hL
      exact ⟨E',iE',L,Y,hLp,hLr.trans T.networkRank_suppress,
        hLpath.trans (T.numPaths_suppress hvs.symm hvt.symm),hX.trans hXY,by omega,hLhit⟩

/-- A pole of girth at least five gives a two-pole with at most three marks per extra port. -/
theorem exists_two_pole {E : Type} [Fintype E] (N : Network V E) (g : ℕ) (s t : V)
    (hN : N.IsWeakPole) (hs : N.IsPort s) (ht : N.IsPort t) (hst : s≠t)
    (hcount : Nat.card {v // N.IsPort v}≤g+2)
    (hrich : 2^networkRank N<2*N.numPaths s t)
    (hgirth : ∀z : N.Word,N.IsCycleWord z → 5≤size z) :
    ∃ (E' : Type) (iE' : Fintype E'),letI := iE';
      ∃ (M : Network V E') (Y : Finset V),M.IsWeakTwoPole s t ∧
        networkRank M=networkRank N ∧ M.numPaths s t=N.numPaths s t ∧
        Y.card≤3*g ∧ Hits M Y := by
  have hextra : (extraPorts N s t).card≤g := by
    have hh := extraPorts_card N hs ht hst
    omega
  have hhit : Hits N ∅ := by
    intro z hz hsize
    have := hgirth z hz
    omega
  obtain ⟨E',iE',M,Y,hM⟩ := exists_reduction g E N s t ∅ hN hs ht hst hextra hrich hhit
  letI := iE'
  exact ⟨E',iE',M,Y,hM.1,hM.2.1,hM.2.2.1,by simpa using hM.2.2.2.2.1,hM.2.2.2.2.2⟩

end Erdos1016.ExactMaximumSupport.Shortening.PoleTransversalSuppression
