import Erdos1016.ExactMaximumSupport.FullPairMatching

set_option autoImplicit false

/-!
# Full-pair joins cannot avoid an even word

Fullness makes the actual path injection onto the whole parity fiber.
This turns explicit boundary words into paths without an extra geometry premise.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairJoinObstruction
open BoundaryTrace BoundaryTrace.Network
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Every terminal parity join is an actual path when the pair is full. -/
theorem isPath_of_boundary {s t : V} (hfull : N.IsFullPair s t)
    {x : N.Word} (hx : N.boundary x=N.pathDemand s t) : N.IsPathWord s t x := by
  let f : {p : N.Word // N.IsPathWord s t p} → Parity.Fiber N.boundary (N.pathDemand s t) :=
    fun p => ⟨p.1,p.2.boundary_eq⟩
  have hf : Function.Injective f := by
    intro a b h
    have h' := congrArg (fun y : Parity.Fiber N.boundary (N.pathDemand s t) => y.1) h
    exact Subtype.ext h'
  have hcard : Nat.card {p : N.Word // N.IsPathWord s t p}=
      Nat.card (Parity.Fiber N.boundary (N.pathDemand s t)) := by
    rw [N.card_joins s t ⟨x,hx⟩]
    exact hfull
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩).2
  obtain ⟨p,hp⟩ := hsurj ⟨x,hx⟩
  have heq : p.1=x := congrArg Subtype.val hp
  exact heq ▸ p.2

/-- A terminal join cannot be edge-disjoint from a nonzero even word in a full two-pole. -/
theorem no_even_disjoint_join {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) {x z : N.Word}
    (hx : N.boundary x=N.pathDemand s t) (hz : N.boundary z=0) (hne : z≠0)
    (hdisj : ∀ e,x e≠0 → z e=0) : False := by
  obtain ⟨c,hc,hsub⟩ := N.exists_isCycleWord_subword z hz hne
  apply FullPairMatching.not_cycle_of_edge_disjoint N hN hfull
    (isPath_of_boundary N hfull hx) (z:=c) _ hc
  intro e he
  by_contra hce
  exact hsub e hce (hdisj e he)

end Erdos1016.ExactMaximumSupport.FullPairJoinObstruction
