import Erdos1016.ExactMaximumSupport.FullPairPermutation
import Erdos1016.ExactMaximumSupport.NetworkPathSegment

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Exact values of ordered rail words

These formulas retain the original physical labels. They prepare explicit
parity joins and even words for the forbidden-pattern obstruction.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairOrderedWords
open BoundaryTrace BoundaryTrace.Network NetworkPathOrder FullPairMatching
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
/-- A segment is unchanged when its endpoints are exchanged. -/
theorem segment_comm {s t : V} {p : N.Word} (O : Order N s t p)
    (i j : Fin (O.innerCount+2)) : O.segment i j=O.segment j i := add_comm _ _

omit [Fintype V] [Fintype E] in
/-- The selected labels of an unoriented interval use its sorted endpoints. -/
theorem segment_selected {s t : V} {p : N.Word} (O : Order N s t p)
    (i j : Fin (O.innerCount+2)) (e : E) : O.segment i j e≠0 ↔
    ∃ h : Fin (O.innerCount+1), min i.val j.val≤h.val ∧ h.val< max i.val j.val ∧ O.edge h=e := by
  rcases le_total i j with hij | hji
  · simpa only [min_eq_left (show i.val≤j.val from hij),max_eq_right (show i.val≤j.val from hij)] using O.segment_selected i j hij e
  · rw [segment_comm N O i j]
    have hm : min i.val j.val=j.val := min_eq_right hji
    have hx : max i.val j.val=i.val := max_eq_left hji
    rw [hm,hx]
    exact O.segment_selected j i hji e

omit [Fintype V] [Fintype E] in
/-- The value on an original rail label is its interval indicator. -/
theorem segment_edge {s t : V} {p : N.Word} (O : Order N s t p)
    (i j : Fin (O.innerCount+2)) (h : Fin (O.innerCount+1)) :
    O.segment i j (O.edge h)=
      if min i.val j.val≤h.val ∧ h.val< max i.val j.val then 1 else 0 := by
  classical
  have hx : O.segment i j (O.edge h)≠0 ↔
      min i.val j.val≤h.val ∧ h.val< max i.val j.val := by
    rw [segment_selected N O]
    constructor
    · rintro ⟨k,hik,hkj,hkh⟩
      exact O.edge_injective hkh ▸ ⟨hik,hkj⟩
    · exact fun hc => ⟨h,hc.1,hc.2,rfl⟩
  split_ifs with hc
  · exact (bit_cases _).resolve_left (hx.mpr hc)
  · exact not_not.mp (fun hn => hc (hx.mp hn))

omit [Fintype V] [Fintype E] in
/-- Every selected interval label belongs to the original rail word. -/
theorem segment_subword {s t : V} {p : N.Word} (O : Order N s t p)
    (i j : Fin (O.innerCount+2)) : N.IsSubword (O.segment i j) p := by
  intro e he
  obtain ⟨h,_,_,hh⟩ := (segment_selected N O i j e).mp he
  exact (O.edge_support e).mpr ⟨h,hh⟩

omit [Fintype V] [Fintype E] in
/-- A segment vanishes on any label absent from its rail. -/
theorem segment_zero {s t : V} {p : N.Word} (O : Order N s t p)
    (i j : Fin (O.innerCount+2)) {e : E} (he : p e=0) : O.segment i j e=0 := by
  by_contra hz
  exact segment_subword N O i j e hz he

omit [Fintype V] [Fintype E] in
/-- Nonoverlapping label intervals have disjoint selected labels. -/
theorem segment_separated_zero {s t : V} {p : N.Word} (O : Order N s t p)
    (i j k l : Fin (O.innerCount+2))
    (hsep : max i.val j.val≤ min k.val l.val) {e : E}
    (he : O.segment k l e≠0) : O.segment i j e=0 := by
  by_contra hi
  obtain ⟨a,_,ha,hae⟩ := (segment_selected N O i j e).mp hi
  obtain ⟨b,hb,_,hbe⟩ := (segment_selected N O k l e).mp he
  have hab := O.edge_injective (hae.trans hbe.symm)
  subst b
  omega

variable {s t : V} (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
  {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
  (hedge : ∀ e,p e≠0 → q e=0) (L : Order N s t p) (R : Order N s t q)
include hN hfull hp hq hedge

/-- Matching labels are absent from both actual rail words. -/
theorem label_rail_zero (i : Fin L.innerCount) :
    p (FullPairPermutation.label N hN hfull hp hq hedge L i)=0 ∧
    q (FullPairPermutation.label N hN hfull hp hq hedge L i)=0 :=
  (residual_selected_iff N hedge _).mp
    (FullPairPermutation.label_selected N hN hfull hp hq hedge L i)

/-- A left rail label cannot be a matching label. -/
theorem left_ne_label (h : Fin (L.innerCount+1)) (i : Fin L.innerCount) :
    L.edge h≠FullPairPermutation.label N hN hfull hp hq hedge L i := by
  intro he
  have hs := (L.edge_support _).mpr ⟨h,rfl⟩
  rw [he] at hs
  exact hs (label_rail_zero N hN hfull hp hq hedge L i).1

/-- A right rail label cannot be a matching label. -/
theorem right_ne_label (h : Fin (R.innerCount+1)) (i : Fin L.innerCount) :
    R.edge h≠FullPairPermutation.label N hN hfull hp hq hedge L i := by
  intro he
  have hs := (R.edge_support _).mpr ⟨h,rfl⟩
  rw [he] at hs
  exact hs (label_rail_zero N hN hfull hp hq hedge L i).2

omit hN hfull hp hq [Fintype V] [Fintype E] in
/-- Every right segment vanishes on every left rail label. -/
theorem right_segment_left (i j : Fin (R.innerCount+2)) (h : Fin (L.innerCount+1)) :
    R.segment i j (L.edge h)=0 :=
  segment_zero N R i j (hedge _ ((L.edge_support _).mpr ⟨h,rfl⟩))

omit hN hfull hp hq [Fintype V] [Fintype E] in
/-- Every left segment vanishes on every right rail label. -/
theorem left_segment_right (i j : Fin (L.innerCount+2)) (h : Fin (R.innerCount+1)) :
    L.segment i j (R.edge h)=0 := by
  apply segment_zero N L i j
  by_contra hp0
  exact ((R.edge_support _).mpr ⟨h,rfl⟩) (hedge _ hp0)


/-- Matching coordinates retain the actual right-rail vertex before reindexing. -/
theorem label_joins_coordinate (i : Fin L.innerCount) :
    N.Joins (FullPairPermutation.label N hN hfull hp hq hedge L i)
      (L.innerVertex i)
      (R.innerVertex (FullPairPermutation.coordinateEquiv N hN hfull hp hq hedge L R i)) := by
  have h := (FullPairRailEquiv.matchingLabel_spec N hN hfull hp hq hedge (L.innerEquiv hp i)).2
  rw [FullPairPermutation.partner_coordinate N hN hfull hp hq hedge L R i] at h
  exact h

end Erdos1016.ExactMaximumSupport.FullPairOrderedWords
