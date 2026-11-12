import Erdos1016.ExactMaximumSupport.FullPairRailEquiv
import Erdos1016.ExactMaximumSupport.NetworkPathInterior

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The actual ordered rail permutation

The matching equivalence identifies the two actual inner rail supports.
Their path orders give equal lengths and an explicit permutation, with every
matching label and every remaining physical label accounted for.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairPermutation
open BoundaryTrace BoundaryTrace.Network FullPairMatching NetworkPathOrder
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {s t : V} (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
  {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
  (hedge : ∀ e,p e≠0 → q e=0) (L : Order N s t p) (R : Order N s t q)
include hN hfull hp hq hedge

/-- Match ordered positions through the actual physical matching. -/
def coordinateEquiv : Fin L.innerCount ≃ Fin R.innerCount :=
  ((L.innerEquiv hp).trans (FullPairRailEquiv.matchingEquiv N hN hfull hp hq hedge)).trans
    (R.innerEquiv hq).symm

/-- Both rails have the same number of actual inner vertices. -/
theorem innerCount_eq : L.innerCount=R.innerCount := by
  have h := Nat.card_congr (coordinateEquiv N hN hfull hp hq hedge L R)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using h

/-- The permutation induced by the actual matching and the two path orders. -/
def permutation : Equiv.Perm (Fin L.innerCount) :=
  (coordinateEquiv N hN hfull hp hq hedge L R).trans
    (finCongr (innerCount_eq N hN hfull hp hq hedge L R).symm)

/-- Right-rail coordinates use the same finite index type as the left rail. -/
def rightVertex (i : Fin L.innerCount) : V :=
  R.innerVertex (Fin.cast (innerCount_eq N hN hfull hp hq hedge L R) i)

/-- The original physical matching label at a left-rail position. -/
def label (i : Fin L.innerCount) : E :=
  FullPairRailEquiv.matchingLabel N hN hfull hp hq hedge (L.innerEquiv hp i)

/-- Coordinate transport retains the actual right endpoint. -/
theorem partner_coordinate (i : Fin L.innerCount) :
    (FullPairRailEquiv.matchingEquiv N hN hfull hp hq hedge (L.innerEquiv hp i)).1=
      R.innerVertex (coordinateEquiv N hN hfull hp hq hedge L R i) := by
  have h := (R.innerEquiv hq).apply_symm_apply
    (FullPairRailEquiv.matchingEquiv N hN hfull hp hq hedge (L.innerEquiv hp i))
  exact (congrArg Subtype.val h).symm

/-- The reindexed permutation has the same right-coordinate value. -/
theorem cast_permutation (i : Fin L.innerCount) :
    Fin.cast (innerCount_eq N hN hfull hp hq hedge L R)
      (permutation N hN hfull hp hq hedge L R i)=
        coordinateEquiv N hN hfull hp hq hedge L R i := by
  apply Fin.ext
  rfl

/-- Each matching label has exactly its designated ordered rail endpoints. -/
theorem label_joins (i : Fin L.innerCount) :
    N.Joins (label N hN hfull hp hq hedge L i) (L.innerVertex i)
      (rightVertex N hN hfull hp hq hedge L R (permutation N hN hfull hp hq hedge L R i)) := by
  have h := (FullPairRailEquiv.matchingLabel_spec N hN hfull hp hq hedge (L.innerEquiv hp i)).2
  rw [partner_coordinate N hN hfull hp hq hedge L R i] at h
  simpa only [label,Order.innerEquiv_apply,rightVertex,cast_permutation] using h

/-- Ordered matching labels are all different. -/
theorem label_injective : Function.Injective (label N hN hfull hp hq hedge L) :=
  (FullPairRailEquiv.matchingLabel_injective N hN hfull hp hq hedge).comp
    (L.innerEquiv hp).injective

/-- The ordered matching labels exhaust the residual physical labels. -/
theorem label_coverage {e:E} (he : residual N p q e≠0) :
    ∃ i:Fin L.innerCount,label N hN hfull hp hq hedge L i=e := by
  obtain ⟨u,hu⟩ := FullPairRailEquiv.matchingLabel_coverage N hN hfull hp hq hedge he
  refine ⟨(L.innerEquiv hp).symm u,?_⟩
  simpa only [label,Equiv.apply_symm_apply] using hu

/-- Each ordered matching label is selected by the actual residual word. -/
theorem label_selected (i : Fin L.innerCount) :
    residual N p q (label N hN hfull hp hq hedge L i)≠0 :=
  (FullPairRailEquiv.matchingLabel_spec N hN hfull hp hq hedge (L.innerEquiv hp i)).1

/-- The two inner rail arrays have no common vertex. -/
theorem inner_disjoint (i j : Fin L.innerCount) :
    L.innerVertex i≠rightVertex N hN hfull hp hq hedge L R j := by
  intro h
  have hzero := (FullPairRailEquiv.inner_degrees N hN hfull hp hq hedge (L.innerEquiv hp i)).2
  have htwo := R.innerVertex_degree hq
    (Fin.cast (innerCount_eq N hN hfull hp hq hedge L R) j)
  change N.deg q (L.innerVertex i)=0 at hzero
  rw [h] at hzero
  change N.deg q (rightVertex N hN hfull hp hq hedge L R j)=2 at htwo
  omega

/-- The two ordered rail paths and the ordered matching cover every original label. -/
theorem edge_coverage (e:E) :
    (∃ i:Fin (L.innerCount+1),L.edge i=e) ∨
    (∃ i:Fin (R.innerCount+1),R.edge i=e) ∨
    (∃ i:Fin L.innerCount,label N hN hfull hp hq hedge L i=e) := by
  by_cases hp0:p e=0
  · by_cases hq0:q e=0
    · exact Or.inr (Or.inr (label_coverage N hN hfull hp hq hedge L
        ((residual_selected_iff N hedge e).2 ⟨hp0,hq0⟩)))
    · exact Or.inr (Or.inl ((R.edge_support e).mp hq0))
  · exact Or.inl ((L.edge_support e).mp hp0)

end Erdos1016.ExactMaximumSupport.FullPairPermutation
