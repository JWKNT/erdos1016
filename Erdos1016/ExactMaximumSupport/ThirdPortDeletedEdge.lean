import Erdos1016.ExactMaximumSupport.PoleTerminalDeletion
import Erdos1016.ExactMaximumSupport.PoleAdjacentGap
import Erdos1016.ExactMaximumSupport.NetworkIso

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Paths from a subdividing vertex

Deleting the subdividing vertex is the same physical network as deleting the
marked edge after suppression. The two possible first labels give an exact
path-count sum, including a direct step to the terminal.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.ThirdPortDeletedEdge
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance deletedEdgeDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {e f : E} {u v w : V} (T : N.Thread e f u v w)

omit [Fintype V] [Fintype E] in
include T in
/-- The surviving original labels avoid precisely the two labels of the thread. -/
theorem outside_iff (g : E) : N.outside (fun z => z=v) g ↔ g≠e ∧ g≠f := by
  constructor
  · intro hg
    constructor
    · intro h
      subst g
      exact (T.he.at_right).elim hg.1 hg.2
    · intro h
      subst g
      exact (T.hf.at_left).elim hg.1 hg.2
  · rintro ⟨hge,hgf⟩
    exact ⟨fun h => T.not_at_v hge hgf (Or.inl h),
      fun h => T.not_at_v hge hgf (Or.inr h)⟩

/-- Remove the marked physical label from the suppressed core. -/
abbrev cutCore := (N.suppress e f u w T.huw).sub (fun g => g.1 ≠ e)

/-- Deleting the third vertex and deleting the retained core label agree physically. -/
def deletionIso : NetworkIso (PoleTerminalDeletion.deleted N v) (cutCore N T) where
  vertices := Equiv.refl V
  edges :=
    { toFun := fun g => ⟨⟨g.1,((outside_iff N T g.1).mp g.2).2⟩,
        ((outside_iff N T g.1).mp g.2).1⟩
      invFun := fun g => ⟨g.1.1,(outside_iff N T g.1.1).mpr ⟨g.2,g.1.2⟩⟩
      left_inv := fun g => by apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl }
  joins g := by
    change (N.suppress e f u w T.huw).Joins
      ⟨g.1,((outside_iff N T g.1).mp g.2).2⟩ (N.src g.1) (N.dst g.1)
    apply (N.suppress_joins_of_ne T.huw _ ((outside_iff N T g.1).mp g.2).1 _ _).mpr
    exact Or.inl ⟨rfl,rfl⟩

/-- The deleted network preserves every path count on the original vertices. -/
theorem numPaths_cutCore (a b : V) :
    (cutCore N T).numPaths a b = (PoleTerminalDeletion.deleted N v).numPaths a b :=
  (deletionIso N T).numPaths_eq a b

/-- The only terminal path selecting a direct terminal label is that singleton. -/
theorem card_first_direct {s t : V} {g : E} (hg : N.Joins g s t) :
    Nat.card {P : N.Word // N.IsPathWord s t P ∧ P g≠0} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨unitWord g,N.isPathWord_unitWord hg,?_⟩,?_⟩
  · simp [unitWord_apply]
  · intro P
    exact Subtype.ext (PoleAdjacentGap.path_eq_unit_of_selected N hg P.2.1 P.2.2)

/-- A first label either reaches the target or leaves a path in the deleted network. -/
theorem card_first_branch {s t x : V} {g : E} (hg : N.Joins g s x) :
    Nat.card {P : N.Word // N.IsPathWord s t P ∧ P g≠0} =
      if x=t then 1 else (PoleTerminalDeletion.deleted N s).numPaths x t := by
  by_cases hxt : x=t
  · subst x
    rw [if_pos rfl]
    exact card_first_direct N hg
  · rw [if_neg hxt]
    exact PoleTerminalDeletion.card_first_edge N hg hxt

include T in
/-- A path from the thread's middle vertex selects exactly one of its two labels. -/
theorem numPaths_first_split (t : V) :
    N.numPaths v t =
      Nat.card {P : N.Word // N.IsPathWord v t P ∧ P e≠0} +
      Nat.card {P : N.Word // N.IsPathWord v t P ∧ P f≠0} := by
  have hparts : ∀ P : N.Word,N.IsPathWord v t P → P e≠0 ∨ P f≠0 := by
    intro P hP
    obtain ⟨g,hg,hat⟩ := N.exists_edge_of_deg_pos
      (by rw [hP.2.1]; decide : 0<N.deg P v)
    rcases T.only g hat with h | h
    · exact Or.inl (h ▸ hg)
    · exact Or.inr (h ▸ hg)
  have hdisj : ∀ P : N.Word,(N.IsPathWord v t P ∧ P e≠0) →
      (N.IsPathWord v t P ∧ P f≠0) → False := by
    intro P he hf
    have hc : (Finset.univ.filter fun g => P g≠0 ∧ (N.src g=v ∨ N.dst g=v)).card≤1 := he.1.2.1.le
    exact T.hef (Finset.card_le_one.mp hc e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.2,T.he.at_right⟩) f
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf.2,T.hf.at_left⟩))
  have hsplit : N.numPaths v t =
      Nat.card {P : N.Word // (N.IsPathWord v t P ∧ P e≠0) ∨
        (N.IsPathWord v t P ∧ P f≠0)} := by
    unfold Network.numPaths
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun P =>
      ⟨fun h => (hparts P h).elim (fun he => Or.inl ⟨h,he⟩)
        (fun hf => Or.inr ⟨h,hf⟩),fun h => h.elim And.left And.left⟩
  rw [hsplit,natCard_or_of_disjoint _ _ hdisj]

/-- The exact restored-port count is the sum of two paths avoiding the marked core edge. -/
theorem numPaths_restored (t : V) :
    N.numPaths v t = (if u=t then 1 else (cutCore N T).numPaths u t) +
      (if w=t then 1 else (cutCore N T).numPaths w t) := by
  rw [numPaths_first_split N T t,card_first_branch N T.he.symm,card_first_branch N T.hf,
    numPaths_cutCore N T u t,numPaths_cutCore N T w t]

end Erdos1016.ExactMaximumSupport.ThirdPortDeletedEdge
