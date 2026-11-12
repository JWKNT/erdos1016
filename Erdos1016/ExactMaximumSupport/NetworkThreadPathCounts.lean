import Erdos1016.ExactMaximumSupport.ThirdPortDeletedEdge
import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Exact counts for adding a two-edge terminal route

An actual degree-two thread between distinct vertices contributes precisely one
new path between them. The two middle-to-end counts include the direct branch.
These are the local identities used after deleting one edge of a square tile.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts
open BoundaryTrace BoundaryTrace.Network
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- Equal physical label predicates have equal actual path counts. -/
theorem numPaths_sub_congr (N : Network V E) (p q : E → Prop)
    [Fintype {e // p e}] [Fintype {e // q e}] (hpq : ∀ e,p e ↔ q e) (a b : V) :
    (N.sub p).numPaths a b=(N.sub q).numPaths a b := by
  rw [N.numPaths_sub,N.numPaths_sub]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro P
  apply and_congr Iff.rfl
  exact ⟨fun h e he => (hpq e).mp (h e he),fun h e he => (hpq e).mpr (h e he)⟩

/-- A direct label adds exactly its singleton path between its two ends. -/
theorem direct_add_one (N : Network V E) {e : E} {a b : V} (he : N.Joins e a b) :
    N.numPaths a b=(N.sub (fun g => g≠e)).numPaths a b+1 := by
  have hiff (P : N.Word) : N.IsPathWord a b P ↔
      (N.IsPathWord a b P ∧ P e=0) ∨ (N.IsPathWord a b P ∧ P e≠0) := by tauto
  have hdisj (P : N.Word) (h : N.IsPathWord a b P ∧ P e=0)
      (h' : N.IsPathWord a b P ∧ P e≠0) : False := h'.2 h.2
  change Nat.card {P : N.Word // N.IsPathWord a b P}=_
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),natCard_or_of_disjoint _ _ hdisj,
    ThirdPortDeletedEdge.card_first_direct N he,N.numPaths_sub]
  apply congrArg (fun q => q+1)
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
    and_congr Iff.rfl (NetworkCutDeletedPaths.within_delete_iff N P e).symm)

variable (N : Network V E) {e f : E} {a v b : V} (T : N.Thread e f a v b)

/-- Deleting the middle of an actual two-edge route removes exactly one endpoint path. -/
theorem endpoints (N : Network V E) {e f : E} {a v b : V} (T : N.Thread e f a v b) :
    N.numPaths a b=(PoleTerminalDeletion.deleted N v).numPaths a b+1 := by
  have hfe (P : N.Word) (hP : N.IsPathWord a b P) : P f=P e := by
    apply T.apply_f_eq_of_boundary
    rw [hP.boundary_eq]
    simp [Network.pathDemand,T.u_ne_v.symm,T.v_ne_w]
  have hwithin (P : N.Word) (hP : N.IsPathWord a b P) :
      Within P (N.outside (fun z => z=v)) ↔ P e=0 := by
    constructor
    · intro h
      apply Classical.not_not.mp
      intro hne
      exact ((ThirdPortDeletedEdge.outside_iff N T e).mp (h e hne)).1 rfl
    · intro he g hg
      apply (ThirdPortDeletedEdge.outside_iff N T g).mpr
      exact ⟨fun h => hg (h ▸ he),fun h => hg (h ▸ (hfe P hP).trans he)⟩
  let Q : N.Word := unitWord e+unitWord f
  have hQ : N.IsPathWord a b Q :=
    (N.isPathWord_unitWord T.he).add_pendant T.hf
      (N.deg_unitWord_of_joins T.he T.huw.symm T.v_ne_w.symm)
  have hcard : Nat.card {P : N.Word // N.IsPathWord a b P ∧ P e≠0}=1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨Q,hQ,?_⟩,?_⟩
    · simp [Q,unitWord_apply,T.hef.symm]
    · intro P
      apply Subtype.ext
      have hpf : P.1 f≠0 := by rw [hfe P.1 P.2.1]; exact P.2.2
      have hsub : N.IsSubword Q P.1 :=
        (N.isSubword_unitWord P.2.2).add (N.isSubword_unitWord hpf)
      apply word_eq_of_add_eq_zero
      apply P.2.1.minimal (P.1+Q) (IsSubword.add_self hsub)
      rw [map_add,P.2.1.boundary_eq,hQ.boundary_eq,word_add_self]
  have hiff (P : N.Word) : N.IsPathWord a b P ↔
      (N.IsPathWord a b P ∧ P e=0) ∨ (N.IsPathWord a b P ∧ P e≠0) := by tauto
  have hdisj (P : N.Word) (h : N.IsPathWord a b P ∧ P e=0)
      (h' : N.IsPathWord a b P ∧ P e≠0) : False := h'.2 h.2
  change Nat.card {P : N.Word // N.IsPathWord a b P}=_
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),natCard_or_of_disjoint _ _ hdisj,hcard]
  apply congrArg (fun q => q+1)
  rw [PoleTerminalDeletion.deleted,N.numPaths_sub]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun P =>
    ⟨fun h => ⟨h.1,(hwithin P h.1).mpr h.2⟩,
      fun h => ⟨h.1,(hwithin P h.1).mp h.2⟩⟩

include T in
/-- A middle-to-first-end path is direct or passes through the old endpoint path family. -/
theorem middle_left :
    N.numPaths v a=1+(PoleTerminalDeletion.deleted N v).numPaths a b := by
  rw [ThirdPortDeletedEdge.numPaths_first_split N T a,
    ThirdPortDeletedEdge.card_first_branch N T.he.symm,
    ThirdPortDeletedEdge.card_first_branch N T.hf,if_pos rfl,if_neg T.huw.symm,
    ExactMaximum.numPaths_symm (PoleTerminalDeletion.deleted N v) b a]

include T in
/-- The other middle-to-end family has the same exact size. -/
theorem middle_right :
    N.numPaths v b=1+(PoleTerminalDeletion.deleted N v).numPaths a b := by
  rw [ThirdPortDeletedEdge.numPaths_first_split N T b,
    ThirdPortDeletedEdge.card_first_branch N T.he.symm,
    ThirdPortDeletedEdge.card_first_branch N T.hf,if_neg T.huw,if_pos rfl]
  omega

end Erdos1016.ExactMaximumSupport.NetworkThreadPathCounts
