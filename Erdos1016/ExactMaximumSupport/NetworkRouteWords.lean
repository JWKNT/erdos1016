import Erdos1016.ExactMaximum.NetBridgeCut
import Erdos1016.ExactMaximum.NetJoin

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual path words, including a zero-length route

The zero word is the unique route from a vertex to itself. For distinct ends,
routes are exactly the existing physical path words. This convention keeps
cut decompositions valid when an endpoint is a cut endpoint.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.NetworkRouteWords
open BoundaryTrace BoundaryTrace.Network
open scoped BigOperators
local instance (priority := 2000) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E]

/-- A minimal physical join, allowing its two ends to coincide. -/
def IsRouteWord (N : Network V E) (a b : V) (P : N.Word) : Prop :=
  N.boundary P = N.pathDemand a b ∧
    ∀ z : N.Word, N.IsSubword z P → N.boundary z = 0 → z = 0

/-- For distinct ends the route predicate is the actual path predicate. -/
theorem route_iff_path (N : Network V E) {a b : V} (hab : a ≠ b) (P : N.Word) :
    IsRouteWord N a b P ↔ N.IsPathWord a b P := by
  exact ⟨fun h => N.isPathWord_of_minimal hab h.1 h.2,
    fun h => ⟨h.boundary_eq,h.minimal⟩⟩

omit [Fintype V] in
/-- A route whose ends coincide is the zero word. -/
theorem route_self_iff (N : Network V E) (a : V) (P : N.Word) :
    IsRouteWord N a a P ↔ P = 0 := by
  constructor
  · intro h
    apply h.2 P (fun _ h => h)
    simpa [pathDemand,word_add_self] using h.1
  · rintro rfl
    constructor
    · simp [pathDemand,word_add_self]
    · intro z hsub _
      funext e
      exact Classical.not_not.mp (fun h => hsub e h rfl)

/-- The route count within a literal edge restriction, with direct branch one. -/
theorem card_routes_within (N : Network V E) (p : E → Prop) (a b : V) :
    Nat.card {P : N.Word // IsRouteWord N a b P ∧ Within P p} =
      if a = b then 1 else (N.sub p).numPaths a b := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have hiff : ∀ P : N.Word, (IsRouteWord N a a P ∧ Within P p) ↔ P = 0 := by
      intro P
      rw [route_self_iff]
      exact ⟨And.left,fun h => ⟨h,by subst P; intro e he; exact (he rfl).elim⟩⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    simp
  · rw [if_neg hab,N.numPaths_sub]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
      and_congr (route_iff_path N hab P) Iff.rfl)

/-- Two routes on opposite shores and one physical crossing label form a path. -/
theorem isPath_glue (N : Network V E) (S : V → Prop) {e : E} {a s t b : V}
    (he : N.Joins e s t) (hs : S s) (ht : ¬ S t) (ha : S a) (hb : ¬ S b)
    {P Q : N.Word} (hP : IsRouteWord N a s P)
    (hPin : Within P (N.inside S)) (hQ : IsRouteWord N t b Q)
    (hQout : Within Q (N.outside S)) : N.IsPathWord a b (P + Q + unitWord e) := by
  have hce : N.crosses S e := N.crosses_of_joins he hs ht
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  obtain ⟨x, hxdef⟩ : ∃ x : N.Word, x = P + Q + unitWord e := ⟨_, rfl⟩
  rw [← hxdef]
  have hxin : ∀ g, N.inside S g → x g = P g := by
    intro g hg
    have h1 : Q g = 0 := hQout.eq_zero (N.not_outside_of_inside hg)
    have h2 : unitWord e g = 0 := by
      rw [unitWord_apply, if_neg]
      intro h
      exact N.not_crosses_of_inside hg (h ▸ hce)
    rw [hxdef]
    show P g + Q g + unitWord e g = P g
    rw [h1, h2, add_zero, add_zero]
  have hxout : ∀ g, N.outside S g → x g = Q g := by
    intro g hg
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_outside hg)
    have h2 : unitWord e g = 0 := by
      rw [unitWord_apply, if_neg]
      intro h
      exact N.not_crosses_of_outside hg (h ▸ hce)
    rw [hxdef]
    show P g + Q g + unitWord e g = Q g
    rw [h1, h2, zero_add, add_zero]
  have hxcr : ∀ g, N.crosses S g → g ≠ e → x g = 0 := by
    intro g hg hne
    have h1 : P g = 0 := hPin.eq_zero (N.not_inside_of_crosses hg)
    have h2 : Q g = 0 := hQout.eq_zero (N.not_outside_of_crosses hg)
    rw [hxdef]
    show P g + Q g + unitWord e g = 0
    rw [h1, h2, unitWord_apply, if_neg (Ne.symm hne), add_zero, add_zero]
  apply N.isPathWord_of_minimal hab
  · rw [hxdef, map_add, map_add, hP.1, hQ.1,
      N.boundary_unitWord_of_joins he]
    show unitWord a + unitWord s + (unitWord t + unitWord b) + (unitWord s + unitWord t) =
      unitWord a + unitWord b
    have h3 : ∀ p q r w : V → Bit, p + q + (r + w) + (q + r) = p + w := by
      intro p q r w
      have h : p + q + (r + w) + (q + r) = p + w + (q + q) + (r + r) := by abel
      rw [h, word_add_self q, word_add_self r, add_zero, add_zero]
    exact h3 _ _ _ _
  · intro y hsub hy0
    have hyother : ∀ g, N.crosses S g → g ≠ e → y g = 0 := by
      intro g hg hne
      exact Classical.not_not.1 fun hy => hsub g hy (hxcr g hg hne)
    have hye : y e = 0 := by
      have hsum : (∑ g, if N.crosses S g then y g else 0) = y e := by
        rw [Finset.sum_eq_single e]
        · rw [if_pos hce]
        · intro g _ hg
          by_cases hc : N.crosses S g
          · rw [if_pos hc]
            exact hyother g hc hg
          · rw [if_neg hc]
        · intro h
          exact absurd (Finset.mem_univ e) h
      rw [← hsum, ← N.cut_parity S y, hy0]
      simp
    apply N.eq_zero_of_even_of_sides S hP.2 hQ.2 hy0
    · intro g hg hc
      by_cases h1 : g = e
      · exact hg (h1 ▸ hye)
      · exact hg (hyother g hc h1)
    · intro g hg hing
      rw [← hxin g hing]
      exact hsub g hg
    · intro g hg houtg
      rw [← hxout g houtg]
      exact hsub g hg

end Erdos1016.ExactMaximumSupport.NetworkRouteWords
