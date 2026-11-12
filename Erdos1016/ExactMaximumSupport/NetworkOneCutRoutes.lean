import Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # One physical crossing label, including zero-length endpoint routes -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkOneCutRoutes
open BoundaryTrace BoundaryTrace.Network NetworkRouteWords NetworkTwoCutPaths NetworkCutDeletedPaths
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- The physical bridge product also holds when either endpoint is a cut endpoint. -/
theorem numPaths_across (N : Network V E) (S : V → Prop) {e : E} {x y a b : V}
    (he : N.Joins e x y) (hx : S x) (hy : ¬S y)
    (hC : ∀ g,N.crosses S g → g=e) (ha : S a) (hb : ¬S b) :
    N.numPaths a b=(if a=x then 1 else (N.sub (N.inside S)).numPaths a x)*
      (if y=b then 1 else (N.sub (N.outside S)).numPaths y b) := by
  have hce := N.crosses_of_joins he hx hy
  have hiff (R : N.Word) : N.IsPathWord a b R ↔
      N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord e := by
    constructor
    · intro hR
      refine ⟨hR,?_⟩
      have hre := N.eq_one_of_join_across S hC hce ha hb hR.boundary_eq
      funext g
      by_cases hg : N.crosses S g
      · rw [restrict_apply_of_pos R hg,hC g hg,hre,unitWord_apply,if_pos rfl]
      · rw [restrict_apply_of_neg R hg,unitWord_apply,if_neg]
        intro heq
        exact hg (heq ▸ hce)
    · exact And.left
  change Nat.card {R : N.Word // N.IsPathWord a b R}=_
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_paths_one_selected_crossing N S he hx hy ha hb

/-- Paths between two vertices on one side of a bridge remain on that side. -/
theorem numPaths_same_side (N : Network V E) (S : V → Prop) {e : E}
    (hce : N.crosses S e) (hC : ∀ g,N.crosses S g → g=e)
    {a b : V} (ha : S a) (hb : S b) :
    N.numPaths a b=(N.sub (N.inside S)).numPaths a b := by
  rw [N.numPaths_sub]
  change Nat.card {R : N.Word // N.IsPathWord a b R}=_
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro R
  constructor
  · intro hR
    refine ⟨hR,?_⟩
    have hre := N.eq_zero_of_join_same_side S hC hce ha hb hR.boundary_eq
    apply path_within_inside_of_cross_zero N S ha hb hR
    funext g
    by_cases hg : N.crosses S g
    · rw [restrict_apply_of_pos R hg,hC g hg]
      exact hre
    · exact restrict_apply_of_neg R hg
  · exact And.left

/-- A leaf-to-target path starts with its unique physical label. -/
theorem leaf_to_target (N : Network V E) {e : E} {x y t : V} (he : N.Joins e x y)
    (honly : ∀g,N.src g=x ∨ N.dst g=x → g=e) (ht : t≠x) :
    N.numPaths x t=if y=t then 1 else
      (N.sub (N.outside (fun v => v=x))).numPaths y t := by
  have hC (g : E) (hg : N.crosses (fun v => v=x) g) : g=e := by
    apply honly
    by_contra h
    push_neg at h
    exact hg (by simp [h.1,h.2])
  have hh := numPaths_across N (fun v => v=x) he rfl he.ne.symm hC rfl ht
  simpa using hh

/-- Deleting a leaf preserves every path count between the remaining vertices. -/
theorem delete_leaf (N : Network V E) {e : E} {x y a b : V} (he : N.Joins e x y)
    (honly : ∀g,N.src g=x ∨ N.dst g=x → g=e) (ha : a≠x) (hb : b≠x) :
    N.numPaths a b=(N.sub (N.outside (fun v => v=x))).numPaths a b := by
  apply numPaths_same_side N (fun v => v≠x)
    (N.crosses_of_joins he.symm he.ne.symm (fun h => h rfl))
    (fun g hg => ?_) ha hb
  apply honly
  by_contra h
  push_neg at h
  exact hg (by simp [h.1,h.2])

end Erdos1016.ExactMaximumSupport.NetworkOneCutRoutes
