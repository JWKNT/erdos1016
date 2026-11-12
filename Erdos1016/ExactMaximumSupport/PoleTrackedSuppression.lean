import Erdos1016.ExactMaximumSupport.SuppressedCyclicShore
import Erdos1016.ExactMaximum.PoleSides

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Suppress every extra port while retaining a marked shore lift

The reduced network has the original vertex type.  Each actual suppression adds
its two ends and its middle vertex to the forbidden set.  At most `g` extra ports
therefore add at most `3*g` marks.  Rank and tested path count remain exact.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleTrackedSuppression
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance trackedSuppressionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type} [Fintype V] [Fintype E]

/-- The original degree-two vertices other than the two tested ports. -/
def extraPorts (N : Network V E) (s t : V) : Finset V :=
  Finset.univ.filter fun v => N.IsPort v ∧ v≠s ∧ v≠t

/-- Suppression removes precisely its middle vertex from the extra-port set. -/
theorem extraPorts_suppress (N : Network V E) {s t u v w : V} {e f : E}
    (T : N.Thread e f u v w) :
    extraPorts (N.suppress e f u w T.huw) s t=(extraPorts N s t).erase v := by
  ext x
  by_cases hx : x=v
  · subst x
    have hz := T.deg_suppress_v (fun _ => 1)
    simp only [extraPorts,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_erase,ne_eq,not_true_eq_false,false_and,iff_false,not_and]
    intro hp
    change (N.suppress e f u w T.huw).deg (fun _ => 1) v=2 at hp
    omega
  · simp [extraPorts,hx,T.isPort_suppress hx]

/-- The two tested ports account for the two omitted vertices. -/
theorem extraPorts_card (N : Network V E) {s t : V}
    (hs : N.IsPort s) (ht : N.IsPort t) (hst : s≠t) :
    (extraPorts N s t).card+2=Nat.card {v // N.IsPort v} := by
  have hset : Finset.univ.filter N.IsPort=insert s (insert t (extraPorts N s t)) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,extraPorts]
    by_cases hvs : v=s
    · subst v; simp [hs]
    · by_cases hvt : v=t
      · subst v; simp [ht]
      · simp [hvs,hvt]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,hset]
  have hns : s∉extraPorts N s t := by simp [extraPorts]
  have hnt : t∉extraPorts N s t := by simp [extraPorts]
  rw [Finset.card_insert_of_not_mem (by simp [hst,hns]),Finset.card_insert_of_not_mem hnt]

/-- Above half capacity, every extra port has distinct thread ends. -/
theorem exists_thread (N : Network V E) {s t v : V} (hN : N.IsWeakPole)
    (hs : N.IsPort s) (ht : N.IsPort t)
    (hv : v∈extraPorts N s t) (hrich : 2^networkRank N<2*N.numPaths s t) :
    ∃ (e f : E) (u w : V),N.Thread e f u v w := by
  obtain ⟨hvp,hvs,hvt⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨e,f,u,w,hef,he,hf,honly⟩ := N.exists_two_edges_of_deg_two hvp
  have huw : u≠w := by
    intro h
    subst w
    have hdegree : ∀x,N.deg (fun _ => 1) x≤3 := by
      intro x
      rcases hN.1 x with h | h | h <;> omega
    have hh := N.two_mul_numPaths_le_of_digon hdegree hs ht hvs hvt hef he hf honly
    omega
  exact ⟨e,f,u,w,⟨he,hf,hef,huw,honly⟩⟩

/-- Exact invariants and the literal original-shore implication of a tracked
sequence of suppressions.  No terminal or geometric certificate is assumed. -/
def Reduction {E' : Type} [Fintype E'] (N : Network V E) (s t : V)
    (X : Finset V) (g : ℕ) (M : Network V E') (Y : Finset V) : Prop :=
  M.IsWeakTwoPole s t ∧ networkRank M=networkRank N ∧
  M.numPaths s t=N.numPaths s t ∧ X⊆Y ∧ Y.card≤X.card+3*g ∧
  ∀S : V → Prop,M.IsCyclicCut S →
    (∀v,S v → M.deg (fun _ => 1) v=3) → (∀v,S v → v∉Y) →
    N.IsCyclicCut S ∧ N.cutSize S=M.cutSize S ∧
      (∀v,S v → N.deg (fun _ => 1) v=3)

/-- Every extra port is removed by actual label-preserving suppression. -/
theorem exists_reduction (g : ℕ) :
    ∀ (E : Type) [Fintype E] (N : Network V E) (s t : V) (X : Finset V),
      N.IsWeakPole → N.IsPort s → N.IsPort t → s≠t →
      (extraPorts N s t).card≤g → 2^networkRank N<2*N.numPaths s t →
      ∃ (E' : Type) (iE' : Fintype E'),letI := iE';
        ∃ (M : Network V E') (Y : Finset V),Reduction N s t X g M Y := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro E _ N s t X hN hs ht hst hcount hrich
    by_cases hall : ∀v,N.IsPort v → v=s ∨ v=t
    · refine ⟨E,inferInstance,N,X,⟨hN,hs,ht,hst,hall⟩,rfl,rfl,Finset.Subset.refl _,?_,?_⟩
      · omega
      · intro S hS hdegree _
        exact ⟨hS,rfl,hdegree⟩
    · obtain ⟨v,hv⟩ := not_forall.mp hall
      obtain ⟨hvp,hvst⟩ := Classical.not_imp.mp hv
      have hvs : v≠s := fun h => hvst (Or.inl h)
      have hvt : v≠t := fun h => hvst (Or.inr h)
      have hmem : v∈extraPorts N s t := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvp,hvs,hvt⟩
      obtain ⟨e,f,u,w,T⟩ := exists_thread N hN hs ht hmem hrich
      let M := N.suppress e f u w T.huw
      let X' := insert u (insert v (insert w X))
      have hX : X⊆X' := by intro x hx; simp [X',hx]
      have hXcard : X'.card≤X.card+3 := by
        have h1 := Finset.card_insert_le u (insert v (insert w X))
        have h2 := Finset.card_insert_le v (insert w X)
        have h3 := Finset.card_insert_le w X
        dsimp only [X']; omega
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
      letI := iE'
      obtain ⟨hLp,hLr,hLpath,hXY,hYcard,hLift⟩ := hL
      refine ⟨E',iE',L,Y,hLp,?_,?_,hX.trans hXY,?_,?_⟩
      · exact hLr.trans T.networkRank_suppress
      · exact hLpath.trans (T.numPaths_suppress hvs.symm hvt.symm)
      · omega
      · intro S hS hdegree havoid
        obtain ⟨hMS,hcut,hMdeg⟩ := hLift S hS hdegree havoid
        have hnu : ¬S u := fun hu => havoid u hu (hXY (by simp [X']))
        have hnv : ¬S v := fun hv => havoid v hv (hXY (by simp [X']))
        have hnw : ¬S w := fun hw => havoid w hw (hXY (by simp [X']))
        obtain ⟨hNS,hcut',hNdeg⟩ := SuppressedCyclicShore.lift T S hnu hnv hnw hMS hMdeg
        exact ⟨hNS,hcut'.trans hcut,hNdeg⟩

/-- At most `g+2` ports give an actual two-pole with at most `3*g+2` marks,
including the original tested ports and every suppressed thread. -/
theorem exists_marked_two_pole (N : Network V E) (g : ℕ) (s t : V)
    (hN : N.IsWeakPole) (hs : N.IsPort s) (ht : N.IsPort t) (hst : s≠t)
    (hcount : Nat.card {v // N.IsPort v}≤g+2)
    (hrich : 2^networkRank N<2*N.numPaths s t) :
    ∃ (E' : Type) (iE' : Fintype E'),letI := iE';
      ∃ (M : Network V E') (Y : Finset V),Reduction N s t {s,t} g M Y ∧
        Y.card≤3*g+2 ∧ s∈Y ∧ t∈Y := by
  have hextra : (extraPorts N s t).card≤g := by
    have hh := extraPorts_card N hs ht hst
    omega
  obtain ⟨E',iE',M,Y,hM⟩ := exists_reduction g E N s t {s,t} hN hs ht hst hextra hrich
  letI := iE'
  refine ⟨E',iE',M,Y,hM,?_,hM.2.2.2.1 (by simp),hM.2.2.2.1 (by simp)⟩
  have hh := hM.2.2.2.2.1
  have hpair : ({s,t} : Finset V).card=2 := by simp [hst]
  omega

end Erdos1016.ExactMaximumSupport.PoleTrackedSuppression
