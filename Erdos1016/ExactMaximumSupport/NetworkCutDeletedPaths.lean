import Erdos1016.ExactMaximumSupport.NetworkTwoCutPaths
import Erdos1016.ExactMaximumSupport.MarkedPathCount

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Deleted interface labels and marked-edge continuations

These are exact physical path identities for a two-label cut. They include
coincident cut endpoints and zero-length continuations; no pole model is assumed.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths
open BoundaryTrace BoundaryTrace.Network NetworkTwoCutPaths
open scoped BigOperators
local instance (priority := 2000) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- Avoiding a physical label is a literal zero coordinate. -/
theorem within_delete_iff (N : Network V E) (R : N.Word) (e : E) :
    Within R (fun g => g≠e) ↔ R e=0 := by
  constructor
  · intro h
    exact Classical.not_not.mp (fun he => h e he rfl)
  · intro h g hg heq
    subst g
    exact hg h

/-- Cut parity for exactly two crossing labels. -/
theorem sum_boundary_two (N : Network V E) (S : V → Prop) {e f : E}
    (hef : e≠f) (hce : N.crosses S e) (hcf : N.crosses S f)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) (R : N.Word) :
    (∑ v,if S v then N.boundary R v else 0)=R e+R f := by
  rw [N.cut_parity]
  have hiff (g : E) : N.crosses S g ↔ g=e ∨ g=f :=
    ⟨hC g,fun h => by rcases h with rfl | rfl; exact hce; exact hcf⟩
  have hp (g : E) : (if N.crosses S g then R g else 0)=
      (if g=e then R e else 0)+(if g=f then R f else 0) := by
    rw [hiff]
    by_cases he : g=e
    · subst g; simp [hef]
    by_cases hf : g=f
    · subst g; simp [Ne.symm hef]
    simp [he,hf]
  rw [Finset.sum_congr rfl (fun g _ => hp g),Finset.sum_add_distrib]
  simp

/-- A path with no selected crossing labels stays on the shore of its ends. -/
theorem path_within_inside_of_cross_zero (N : Network V E) (S : V → Prop)
    {a b : V} (ha : S a) (hb : S b) {R : N.Word} (hR : N.IsPathWord a b R)
    (hcross : restrict R (N.crosses S)=0) : Within R (N.inside S) := by
  have hsum : restrict R (N.inside S)+restrict R (N.outside S)=R := by
    have h := N.restrict_add_restrict_add_restrict S R
    rw [hcross,add_zero] at h
    exact h
  have hb' : N.boundary (restrict R (N.inside S))+
      N.boundary (restrict R (N.outside S))=N.pathDemand a b+0 := by
    rw [←map_add,hsum,hR.boundary_eq,add_zero]
  have ha1 : ∀ v,¬S v → N.pathDemand a b v=0 := by
    intro v hv
    have h1 : v≠a := fun h => hv (h ▸ ha)
    have h2 : v≠b := fun h => hv (h ▸ hb)
    simp [pathDemand,h1,h2]
  obtain ⟨_,hbQ⟩ := N.boundary_split (within_restrict R (N.inside S))
    (within_restrict R (N.outside S)) ha1 (fun _ _ => rfl) hb'
  have hQ0 : restrict R (N.outside S)=0 :=
    hR.eq_zero_of_even_subword (N.restrict_isSubword R _) hbQ
  intro g hg
  rcases N.inside_or_outside_or_crosses S g with h | h | h
  · exact h
  · have h0 := congrFun hQ0 g
    rw [restrict_apply_of_pos R h] at h0
    exact (hg h0).elim
  · have h0 := congrFun hcross g
    rw [restrict_apply_of_pos R h] at h0
    exact (hg h0).elim

/-- After deleting one cut label, a path between vertices of one shore stays there. -/
theorem path_within_inside_of_deleted (N : Network V E) (S : V → Prop) {e f : E}
    (hef : e≠f) (hce : N.crosses S e) (hcf : N.crosses S f)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) {a b : V} (ha : S a) (hb : S b)
    {R : N.Word} (hR : N.IsPathWord a b R) (he : R e=0) : Within R (N.inside S) := by
  have hf : R f=0 := by
    have h := sum_boundary_two N S hef hce hcf hC R
    rw [hR.boundary_eq,N.sum_pathDemand S a b,if_pos ha,if_pos hb,bit_add_self,
      he,zero_add] at h
    exact h.symm
  apply path_within_inside_of_cross_zero N S ha hb hR
  funext g
  by_cases hg : N.crosses S g
  · rw [restrict_apply_of_pos R hg]
    rcases hC g hg with rfl | rfl
    · exact he
    · exact hf
  · exact restrict_apply_of_neg R hg

/-- Deleting one cut label does not change path counts within a single shore. -/
theorem numPaths_delete_same_side (N : Network V E) (S : V → Prop) {e f : E}
    (hef : e≠f) (hce : N.crosses S e) (hcf : N.crosses S f)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) {a b : V} (ha : S a) (hb : S b) :
    (N.sub fun g => g≠e).numPaths a b=(N.sub (N.inside S)).numPaths a b := by
  rw [N.numPaths_sub,N.numPaths_sub]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro R
  constructor
  · rintro ⟨hR,hw⟩
    exact ⟨hR,path_within_inside_of_deleted N S hef hce hcf hC ha hb hR
      ((within_delete_iff N R e).mp hw)⟩
  · rintro ⟨hR,hw⟩
    refine ⟨hR,?_⟩
    rw [within_delete_iff]
    exact hw.eq_zero (N.not_inside_of_crosses hce)

/-- Across the cut, avoiding one label leaves exactly the product through the other. -/
theorem numPaths_delete_across (N : Network V E) (S : V → Prop) {e f : E}
    {u v a b : V} (hef : e≠f) (hce : N.crosses S e)
    (hf : N.Joins f u v) (hu : S u) (hv : ¬S v)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) (ha : S a) (hb : ¬S b) :
    (N.sub fun g => g≠e).numPaths a b=
      (if a=u then 1 else (N.sub (N.inside S)).numPaths a u)*
      (if v=b then 1 else (N.sub (N.outside S)).numPaths v b) := by
  rw [N.numPaths_sub]
  have hcf := N.crosses_of_joins hf hu hv
  have hiff (R : N.Word) :
      (N.IsPathWord a b R ∧ Within R (fun g => g≠e)) ↔
      (N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord f) := by
    rw [within_delete_iff]
    constructor
    · rintro ⟨hR,he⟩
      refine ⟨hR,?_⟩
      rcases join_cross_alternative N S hef hce hcf hC ha hb hR.boundary_eq with h | h
      · have hh := congrFun h e
        rw [restrict_apply_of_pos R hce,he,unitWord_apply,if_pos rfl] at hh
        exact (zero_ne_one hh).elim
      · exact h
    · rintro ⟨hR,h⟩
      refine ⟨hR,?_⟩
      have hh := congrFun h e
      simpa [restrict_apply_of_pos R hce,unitWord_apply,Ne.symm hef] using hh
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_paths_one_selected_crossing N S hf hu hv ha hb

private theorem numPaths_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) :
    @Network.numPaths A B i N a b = @Network.numPaths A B j N a b := by
  rw [Subsingleton.elim i j]

/-- The exact continuation count at one edge of a two-label interface. -/
theorem marked_count_interface (N : Network V E) (S : V → Prop) {e f : E}
    {x y u v t : V} (hef : e≠f)
    (he : N.Joins e x y) (hx : S x) (hy : ¬S y)
    (hf : N.Joins f u v) (hu : S u) (hv : ¬S v)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) (ht : ¬S t) :
    MarkedPathCount.count N e t=
      (if x=u then 1 else (N.sub (N.inside S)).numPaths x u)*
        (if v=t then 1 else (N.sub (N.outside S)).numPaths v t)+
      (if y=t then 1 else (N.sub (N.outside S)).numPaths y t) := by
  rw [MarkedPathCount.count_of_joins N he,MarkedPathCount.branch,MarkedPathCount.branch]
  have hxt : x≠t := fun h => ht (h ▸ hx)
  rw [if_neg hxt]
  apply congrArg₂ Nat.add
  · exact (numPaths_instances (N.sub fun g => g≠e) _ _ x t).trans
      (numPaths_delete_across N S hef (N.crosses_of_joins he hx hy) hf hu hv hC hx ht)
  · split_ifs
    · rfl
    · exact (numPaths_instances (N.sub fun g => g≠e) _ _ y t).trans
        (numPaths_delete_same_side N (fun z => ¬S z) hef
        ((N.crosses_not_iff S e).mpr (N.crosses_of_joins he hx hy))
        ((N.crosses_not_iff S f).mpr (N.crosses_of_joins hf hu hv))
        (fun g hg => hC g ((N.crosses_not_iff S g).mp hg)) hy ht)

end Erdos1016.ExactMaximumSupport.NetworkCutDeletedPaths
