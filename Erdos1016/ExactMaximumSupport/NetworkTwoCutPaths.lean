import Erdos1016.ExactMaximumSupport.NetworkRouteWords

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Physical path counts across two crossing labels

The first theorem fixes the single selected crossing label; no assumption is
made on the other ambient crossing labels. Zero-length shore routes contribute
one. The two-label cut corollary will sum these disjoint physical families.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkTwoCutPaths
open BoundaryTrace BoundaryTrace.Network NetworkRouteWords
open scoped BigOperators
local instance (priority := 2000) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Exact product count with one specified selected crossing label. -/
theorem card_paths_one_selected_crossing (N : Network V E) (S : V → Prop)
    {e : E} {x y a b : V} (he : N.Joins e x y) (hx : S x) (hy : ¬ S y)
    (ha : S a) (hb : ¬ S b) :
    Nat.card {R : N.Word // N.IsPathWord a b R ∧ restrict R (N.crosses S) = unitWord e} =
      (if a = x then 1 else (N.sub (N.inside S)).numPaths a x) *
      (if y = b then 1 else (N.sub (N.outside S)).numPaths y b) := by
  have hce : N.crosses S e := N.crosses_of_joins he hx hy
  rw [← card_routes_within N (N.inside S) a x,
    ← card_routes_within N (N.outside S) y b, ← Nat.card_prod]
  symm
  obtain ⟨φ, hφ⟩ : ∃ φ : {P : N.Word // IsRouteWord N a x P ∧ Within P (N.inside S)} ×
      {Q : N.Word // IsRouteWord N y b Q ∧ Within Q (N.outside S)} →
      {R : N.Word // N.IsPathWord a b R ∧ restrict R (N.crosses S) = unitWord e}, ∀ z, (φ z).1 = z.1.1 + z.2.1 + unitWord e :=
    ⟨fun z => ⟨z.1.1 + z.2.1 + unitWord e,
      isPath_glue N S he hx hy ha hb z.1.2.1 z.1.2.2 z.2.2.1 z.2.2.2,by
        rw [restrict_add,restrict_add,
          restrict_eq_zero (N.crosses S) z.1.2.2 (fun g hg => N.not_crosses_of_inside hg),
          restrict_eq_zero (N.crosses S) z.2.2.2 (fun g hg => N.not_crosses_of_outside hg),
          zero_add,zero_add,restrict_eq_self (within_unitWord hce)]⟩, fun _ => rfl⟩
  have hbij : Function.Bijective φ := by
    constructor
    · intro z z' h
      have h0 : z.1.1 + z.2.1 + unitWord e = z'.1.1 + z'.2.1 + unitWord e := by
        rw [← hφ z, ← hφ z', h]
      have h1 : z.1.1 + z.2.1 = z'.1.1 + z'.2.1 := add_right_cancel h0
      have hP : z.1.1 = z'.1.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.inside S) =
            restrict (z'.1.1 + z'.2.1) (N.inside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.1.2.2, restrict_eq_self z'.1.2.2,
          restrict_eq_zero (N.inside S) z.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          restrict_eq_zero (N.inside S) z'.2.2.2 (fun g hg => N.not_inside_of_outside hg),
          add_zero, add_zero] at h2
        exact h2
      have hQ : z.2.1 = z'.2.1 := by
        have h2 : restrict (z.1.1 + z.2.1) (N.outside S) =
            restrict (z'.1.1 + z'.2.1) (N.outside S) := by rw [h1]
        rw [restrict_add, restrict_add, restrict_eq_self z.2.2.2, restrict_eq_self z'.2.2.2,
          restrict_eq_zero (N.outside S) z.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          restrict_eq_zero (N.outside S) z'.1.2.2 (fun g hg => N.not_outside_of_inside hg),
          zero_add, zero_add] at h2
        exact h2
      exact Prod.ext (Subtype.ext hP) (Subtype.ext hQ)
    · intro R
      have hcross := R.2.2
      have hsum : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) + unitWord e = R.1 := by
        simpa only [hcross] using N.restrict_add_restrict_add_restrict S R.1
      have hPQ : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) =
          R.1 + unitWord e := by
        have h2 : restrict R.1 (N.inside S) + restrict R.1 (N.outside S) + unitWord e +
            unitWord e = R.1 + unitWord e := by rw [hsum]
        rw [add_assoc, word_add_self (unitWord e), add_zero] at h2
        exact h2
      have hdem : N.pathDemand a b + N.boundary (unitWord e) =
          N.pathDemand a x + N.pathDemand y b := by
        rw [N.boundary_unitWord_of_joins he]
        show (unitWord a + unitWord b : V → Bit) + (unitWord x + unitWord y) =
          unitWord a + unitWord x + (unitWord y + unitWord b)
        abel
      have hb' : N.boundary (restrict R.1 (N.inside S)) +
          N.boundary (restrict R.1 (N.outside S)) = N.pathDemand a x + N.pathDemand y b := by
        rw [← map_add, hPQ, map_add, R.2.1.boundary_eq, hdem]
      have ha1 : ∀ v, ¬ S v → N.pathDemand a x v = 0 := by
        intro v hv
        have h1 : v ≠ a := fun h => hv (h ▸ ha)
        have h2 : v ≠ x := fun h => hv (h ▸ hx)
        simp [pathDemand, h1, h2]
      have hb1 : ∀ v, S v → N.pathDemand y b v = 0 := by
        intro v hv
        have h1 : v ≠ y := fun h => hy (h ▸ hv)
        have h2 : v ≠ b := fun h => hb (h ▸ hv)
        simp [pathDemand, h1, h2]
      obtain ⟨hbP, hbQ⟩ := N.boundary_split (within_restrict R.1 (N.inside S))
        (within_restrict R.1 (N.outside S)) ha1 hb1 hb'
      have hminP : ∀ z : N.Word, N.IsSubword z (restrict R.1 (N.inside S)) →
          N.boundary z = 0 → z = 0 := fun z hsub hz =>
        R.2.1.eq_zero_of_even_subword (fun g hg => N.restrict_isSubword R.1 _ g (hsub g hg)) hz
      have hminQ : ∀ z : N.Word, N.IsSubword z (restrict R.1 (N.outside S)) →
          N.boundary z = 0 → z = 0 := fun z hsub hz =>
        R.2.1.eq_zero_of_even_subword (fun g hg => N.restrict_isSubword R.1 _ g (hsub g hg)) hz
      refine ⟨(⟨restrict R.1 (N.inside S), ⟨hbP,hminP⟩,
        within_restrict _ _⟩, ⟨restrict R.1 (N.outside S),
        ⟨hbQ,hminQ⟩, within_restrict _ _⟩), ?_⟩
      apply Subtype.ext
      rw [hφ]
      exact hsum
  exact Nat.card_eq_of_bijective φ hbij

/-- A join across a two-label cut selects exactly one of its labels. -/
theorem join_cross_alternative (N : Network V E) (S : V → Prop) {e f : E}
    (hef : e ≠ f) (hce : N.crosses S e) (hcf : N.crosses S f)
    (hC : ∀ g, N.crosses S g → g = e ∨ g = f) {a b : V}
    (ha : S a) (hb : ¬ S b) {R : N.Word}
    (hR : N.boundary R = N.pathDemand a b) :
    restrict R (N.crosses S) = unitWord e ∨
      restrict R (N.crosses S) = unitWord f := by
  have hiff (g : E) : N.crosses S g ↔ g=e ∨ g=f :=
    ⟨hC g,fun h => by rcases h with rfl | rfl; exact hce; exact hcf⟩
  have hsum : (∑ g, if N.crosses S g then R g else 0) = R e + R f := by
    have hp (g : E) : (if N.crosses S g then R g else 0) =
        (if g=e then R e else 0)+(if g=f then R f else 0) := by
      rw [hiff]
      by_cases he : g=e
      · subst g; simp [hef]
      by_cases hf : g=f
      · subst g; simp [Ne.symm hef]
      simp [he,hf]
    rw [Finset.sum_congr rfl (fun g _ => hp g),Finset.sum_add_distrib]
    simp
  have hodd : R e+R f=1 := by
    rw [←hsum,←N.cut_parity S R,hR,N.sum_pathDemand S a b]
    simp [ha,hb]
  have hvalues : (R e=1 ∧ R f=0) ∨ (R e=0 ∧ R f=1) := by
    rcases bit_cases (R e) with he | he <;> rcases bit_cases (R f) with hf | hf
    · simp [he,hf] at hodd
    · exact Or.inr ⟨he,hf⟩
    · exact Or.inl ⟨he,hf⟩
    · rw [he,hf,bit_add_self] at hodd
      exact (zero_ne_one hodd).elim
  have hword (u v : E) (hu : R u=1) (hv : R v=0)
      (hc : ∀ g,N.crosses S g ↔ g=u ∨ g=v) :
      restrict R (N.crosses S)=unitWord u := by
    have hne : u≠v := by intro heq; rw [heq,hv] at hu; exact zero_ne_one hu
    funext g
    by_cases hg : N.crosses S g
    · rw [restrict_apply_of_pos R hg]
      rcases (hc g).mp hg with rfl | rfl
      · simp [unitWord_apply,hu]
      · simp [unitWord_apply,hv,hne]
    · rw [restrict_apply_of_neg R hg,unitWord_apply,if_neg]
      intro heq
      exact hg ((hc g).mpr (Or.inl heq.symm))
  rcases hvalues with ⟨he,hf⟩ | ⟨he,hf⟩
  · exact Or.inl (hword e f he hf hiff)
  · exact Or.inr (hword f e hf he (fun g => (hiff g).trans or_comm))

/-- Actual paths across two physical cut labels are the sum of two shore products.
Coincident shore endpoints contribute the unique zero-length route. -/
theorem numPaths_of_two_crossing (N : Network V E) (S : V → Prop)
    {e f : E} {x y u v a b : V} (hef : e ≠ f)
    (he : N.Joins e x y) (hx : S x) (hy : ¬ S y)
    (hf : N.Joins f u v) (hu : S u) (hv : ¬ S v)
    (hC : ∀ g,N.crosses S g → g=e ∨ g=f) (ha : S a) (hb : ¬ S b) :
    N.numPaths a b =
      (if a=x then 1 else (N.sub (N.inside S)).numPaths a x)*
        (if y=b then 1 else (N.sub (N.outside S)).numPaths y b)+
      (if a=u then 1 else (N.sub (N.inside S)).numPaths a u)*
        (if v=b then 1 else (N.sub (N.outside S)).numPaths v b) := by
  have hce := N.crosses_of_joins he hx hy
  have hcf := N.crosses_of_joins hf hu hv
  have hiff (R : N.Word) : N.IsPathWord a b R ↔
      (N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord e) ∨
      (N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord f) := by
    constructor
    · intro hR
      rcases join_cross_alternative N S hef hce hcf hC ha hb hR.boundary_eq with h | h
      · exact Or.inl ⟨hR,h⟩
      · exact Or.inr ⟨hR,h⟩
    · rintro (h | h) <;> exact h.1
  have hdisj (R : N.Word)
      (he : N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord e)
      (hf : N.IsPathWord a b R ∧ restrict R (N.crosses S)=unitWord f) : False := by
    have hh := congrFun (he.2.symm.trans hf.2) e
    simp [unitWord_apply,Ne.symm hef] at hh
  change Nat.card {R : N.Word // N.IsPathWord a b R} = _
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),natCard_or_of_disjoint _ _ hdisj,
    card_paths_one_selected_crossing N S he hx hy ha hb,
    card_paths_one_selected_crossing N S hf hu hv ha hb]

end Erdos1016.ExactMaximumSupport.NetworkTwoCutPaths
