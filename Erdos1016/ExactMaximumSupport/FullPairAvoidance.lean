import Erdos1016.ExactMaximumSupport.FullPairOrderedWords
import Erdos1016.ExactMaximumSupport.FullPairJoinObstruction
import Erdos1016.ExactMaximumSupport.LadderPermutation

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Actual forbidden-pattern words

Rail segments and original matching labels give explicit parity words.
Fullness excludes a disjoint even word and terminal join.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairAvoidance
open BoundaryTrace BoundaryTrace.Network NetworkPathOrder FullPairMatching FullPairOrderedWords
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {s t : V} (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
  {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
  (hedge : ∀ e,p e≠0 → q e=0) (L : Order N s t p) (R : Order N s t q)
include hN hfull hp hq hedge
local notation "τ" => FullPairPermutation.coordinateEquiv N hN hfull hp hq hedge L R
local notation "M" => FullPairPermutation.label N hN hfull hp hq hedge L

def leftPos (i : Fin L.innerCount) : Fin (L.innerCount+2) := i.succ.castSucc

def rightPos (i : Fin L.innerCount) : Fin (R.innerCount+2) := (τ i).succ.castSucc

/-- Two matching labels close the two rail intervals to an even word. -/
def closedWord (i j : Fin L.innerCount) : N.Word :=
  L.segment (leftPos N L i) (leftPos N L j) +
  R.segment (rightPos N hN hfull hp hq hedge L R i) (rightPos N hN hfull hp hq hedge L R j) +
  (unitWord (M i)+unitWord (M j))

/-- A lower-right prefix and upper-left suffix give a terminal join. -/
def lowerJoin (i : Fin L.innerCount) : N.Word :=
  R.segment 0 (rightPos N hN hfull hp hq hedge L R i) +
  L.segment (leftPos N L i) (Fin.last (L.innerCount+1)) + unitWord (M i)

/-- The opposite detour uses the upper-left prefix and lower-right suffix. -/
def upperJoin (i : Fin L.innerCount) : N.Word :=
  L.segment 0 (leftPos N L i) +
  R.segment (rightPos N hN hfull hp hq hedge L R i) (Fin.last (R.innerCount+1)) + unitWord (M i)

theorem matching_joins (i : Fin L.innerCount) : N.Joins (M i)
    (L.vertex (leftPos N L i)) (R.vertex (rightPos N hN hfull hp hq hedge L R i)) :=
  label_joins_coordinate N hN hfull hp hq hedge L R i

theorem closed_boundary (i j : Fin L.innerCount) :
    N.boundary (closedWord N hN hfull hp hq hedge L R i j)=0 := by
  rw [closedWord,map_add,map_add,L.segment_boundary,R.segment_boundary,map_add,
    N.boundary_unitWord_of_joins (matching_joins N hN hfull hp hq hedge L R i),
    N.boundary_unitWord_of_joins (matching_joins N hN hfull hp hq hedge L R j)]
  unfold pathDemand
  let a := unitWord (L.vertex (leftPos N L i))
  let b := unitWord (L.vertex (leftPos N L j))
  let c := unitWord (R.vertex (rightPos N hN hfull hp hq hedge L R i))
  let d := unitWord (R.vertex (rightPos N hN hfull hp hq hedge L R j))
  change (a+b)+(c+d)+((a+c)+(b+d))=0
  calc
    _ = (a+a)+(b+b)+(c+c)+(d+d) := by abel
    _ = 0 := by simp only [word_add_self,zero_add]

theorem lower_boundary (i : Fin L.innerCount) :
    N.boundary (lowerJoin N hN hfull hp hq hedge L R i)=N.pathDemand s t := by
  rw [lowerJoin,map_add,map_add,R.segment_boundary,L.segment_boundary,
    N.boundary_unitWord_of_joins (matching_joins N hN hfull hp hq hedge L R i),R.first,L.last]
  unfold pathDemand
  let a := unitWord (L.vertex (leftPos N L i))
  let b := unitWord (R.vertex (rightPos N hN hfull hp hq hedge L R i))
  change (unitWord s+b)+(a+unitWord t)+(a+b)=unitWord s+unitWord t
  calc
    _ = (unitWord s+unitWord t)+(a+a)+(b+b) := by abel
    _ = _ := by simp only [word_add_self,add_zero]

theorem upper_boundary (i : Fin L.innerCount) :
    N.boundary (upperJoin N hN hfull hp hq hedge L R i)=N.pathDemand s t := by
  rw [upperJoin,map_add,map_add,L.segment_boundary,R.segment_boundary,
    N.boundary_unitWord_of_joins (matching_joins N hN hfull hp hq hedge L R i),L.first,R.last]
  unfold pathDemand
  let a := unitWord (L.vertex (leftPos N L i))
  let b := unitWord (R.vertex (rightPos N hN hfull hp hq hedge L R i))
  change (unitWord s+a)+(b+unitWord t)+(a+b)=unitWord s+unitWord t
  calc
    _ = (unitWord s+unitWord t)+(a+a)+(b+b) := by abel
    _ = _ := by simp only [word_add_self,add_zero]

/-- The first matching label witnesses that the closed word is nonzero. -/
theorem closed_nonzero (i j : Fin L.innerCount) (hij : i≠j) :
    closedWord N hN hfull hp hq hedge L R i j≠0 := by
  classical
  have hi := label_rail_zero N hN hfull hp hq hedge L i
  have hji : M j≠M i := fun h => hij ((FullPairPermutation.label_injective N hN hfull hp hq hedge L h).symm)
  have hzL : L.segment (leftPos N L i) (leftPos N L j) (M i)=0 :=
    segment_zero N L _ _ hi.1
  have hzR : R.segment (rightPos N hN hfull hp hq hedge L R i)
      (rightPos N hN hfull hp hq hedge L R j) (M i)=0 :=
    segment_zero N R _ _ hi.2
  intro hz
  have he := congrFun hz (M i)
  simp only [closedWord,Pi.add_apply,hzL,hzR,zero_add,unitWord_apply,
    if_pos rfl,if_neg hji,add_zero,Pi.zero_apply] at he
  exact (one_ne_zero : (1:Bit)≠0) he

/-- A right prefix below both matched endpoints avoids the closed interval word. -/
theorem lower_disjoint (i j k : Fin L.innerCount) (hij : i<j) (hjk : j<k)
    (hki : τ k<τ i) (hkj : τ k<τ j) :
    ∀ e,lowerJoin N hN hfull hp hq hedge L R k e≠0 →
      closedWord N hN hfull hp hq hedge L R i j e=0 := by
  classical
  intro e he
  rcases FullPairPermutation.edge_coverage N hN hfull hp hq hedge L R e with
    ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩
  · have hzR (a b) := right_segment_left N hedge L R a b h
    have hmu (a) : unitWord (M a) (L.edge h)=0 := by
      simp only [unitWord_apply,if_neg (left_ne_label N hN hfull hp hq hedge L h a).symm]
    simp only [lowerJoin,closedWord,Pi.add_apply,hzR,hmu,zero_add,add_zero] at he ⊢
    apply segment_separated_zero N L _ _ _ _ _ he
    dsimp only [leftPos]
    simp only [Fin.coe_castSucc,Fin.val_succ,Fin.val_last]
    have := k.isLt
    change i.val<j.val at hij
    change j.val<k.val at hjk
    omega
  · have hzL (a b) := left_segment_right N hedge L R a b h
    have hmu (a) : unitWord (M a) (R.edge h)=0 := by
      simp only [unitWord_apply,if_neg (right_ne_label N hN hfull hp hq hedge L R h a).symm]
    simp only [lowerJoin,closedWord,Pi.add_apply,hzL,hmu,zero_add,add_zero] at he ⊢
    by_contra hc
    apply he
    apply segment_separated_zero N R _ _ _ _ _ hc
    dsimp only [rightPos]
    simp only [Fin.coe_castSucc,Fin.val_succ,Fin.val_zero]
    change (τ k).val<(τ i).val at hki
    change (τ k).val<(τ j).val at hkj
    omega
  · have hm := label_rail_zero N hN hfull hp hq hedge L h
    have hzL (a b) := segment_zero N L a b hm.1
    have hzR (a b) := segment_zero N R a b hm.2
    simp only [lowerJoin,closedWord,Pi.add_apply,hzL,hzR,zero_add] at he ⊢
    have hkh : k=h := by
      by_contra hne
      have hmne : M k≠M h := fun hh => hne (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
      exact he (by simp only [unitWord_apply,if_neg hmne])
    subst h
    have hik : i≠k := ne_of_lt (lt_trans hij hjk)
    have hjk' : j≠k := ne_of_lt hjk
    have hi : M i≠M k := fun hh => hik (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
    have hj : M j≠M k := fun hh => hjk' (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
    simp only [unitWord_apply,if_neg hi,if_neg hj,add_zero]

/-- A left prefix before both endpoints avoids the closed interval word. -/
theorem upper_disjoint (i j k : Fin L.innerCount) (hij : i<j) (hjk : j<k)
    (hji : τ j<τ i) (hki : τ k<τ i) :
    ∀ e,upperJoin N hN hfull hp hq hedge L R i e≠0 →
      closedWord N hN hfull hp hq hedge L R j k e=0 := by
  classical
  intro e he
  rcases FullPairPermutation.edge_coverage N hN hfull hp hq hedge L R e with
    ⟨h,rfl⟩ | ⟨h,rfl⟩ | ⟨h,rfl⟩
  · have hzR (a b) := right_segment_left N hedge L R a b h
    have hmu (a) : unitWord (M a) (L.edge h)=0 := by
      simp only [unitWord_apply,if_neg (left_ne_label N hN hfull hp hq hedge L h a).symm]
    simp only [upperJoin,closedWord,Pi.add_apply,hzR,hmu,zero_add,add_zero] at he ⊢
    by_contra hc
    apply he
    apply segment_separated_zero N L _ _ _ _ _ hc
    dsimp only [leftPos]
    simp only [Fin.coe_castSucc,Fin.val_succ,Fin.val_zero]
    change i.val<j.val at hij
    change j.val<k.val at hjk
    omega
  · have hzL (a b) := left_segment_right N hedge L R a b h
    have hmu (a) : unitWord (M a) (R.edge h)=0 := by
      simp only [unitWord_apply,if_neg (right_ne_label N hN hfull hp hq hedge L R h a).symm]
    simp only [upperJoin,closedWord,Pi.add_apply,hzL,hmu,zero_add,add_zero] at he ⊢
    apply segment_separated_zero N R _ _ _ _ _ he
    dsimp only [rightPos]
    simp only [Fin.coe_castSucc,Fin.val_succ,Fin.val_last]
    have := (τ i).isLt
    change (τ j).val<(τ i).val at hji
    change (τ k).val<(τ i).val at hki
    omega
  · have hm := label_rail_zero N hN hfull hp hq hedge L h
    have hzL (a b) := segment_zero N L a b hm.1
    have hzR (a b) := segment_zero N R a b hm.2
    simp only [upperJoin,closedWord,Pi.add_apply,hzL,hzR,zero_add] at he ⊢
    have hih : i=h := by
      by_contra hne
      have hmne : M i≠M h := fun hh => hne (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
      exact he (by simp only [unitWord_apply,if_neg hmne])
    subst h
    have hji' : j≠i := (ne_of_lt hij).symm
    have hki' : k≠i := (ne_of_lt (lt_trans hij hjk)).symm
    have hj : M j≠M i := fun hh => hji' (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
    have hk : M k≠M i := fun hh => hki' (FullPairPermutation.label_injective N hN hfull hp hq hedge L hh)
    simp only [unitWord_apply,if_neg hj,if_neg hk,add_zero]

/-- The first forbidden permutation pattern yields a disjoint even word and join. -/
theorem not_lower_pattern (i j k : Fin L.innerCount) (hij : i<j) (hjk : j<k) :
    ¬(τ k<τ i ∧ τ k<τ j) := by
  rintro ⟨hki,hkj⟩
  exact FullPairJoinObstruction.no_even_disjoint_join N hN hfull
    (lower_boundary N hN hfull hp hq hedge L R k)
    (closed_boundary N hN hfull hp hq hedge L R i j)
    (closed_nonzero N hN hfull hp hq hedge L R i j (ne_of_lt hij))
    (lower_disjoint N hN hfull hp hq hedge L R i j k hij hjk hki hkj)

/-- The second forbidden permutation pattern gives the opposite detour. -/
theorem not_upper_pattern (i j k : Fin L.innerCount) (hij : i<j) (hjk : j<k) :
    ¬(τ j<τ i ∧ τ k<τ i) := by
  rintro ⟨hji,hki⟩
  exact FullPairJoinObstruction.no_even_disjoint_join N hN hfull
    (upper_boundary N hN hfull hp hq hedge L R i)
    (closed_boundary N hN hfull hp hq hedge L R j k)
    (closed_nonzero N hN hfull hp hq hedge L R j k (ne_of_lt hjk))
    (upper_disjoint N hN hfull hp hq hedge L R i j k hij hjk hji hki)

/-- The actual ordered matching avoids both forbidden patterns. -/
theorem avoids_ladder_patterns : LadderPermutation.AvoidsLadderPatterns
    (FullPairPermutation.permutation N hN hfull hp hq hedge L R) := by
  have hc (a b : Fin L.innerCount) :
      FullPairPermutation.permutation N hN hfull hp hq hedge L R a <
        FullPairPermutation.permutation N hN hfull hp hq hedge L R b ↔ τ a<τ b := Iff.rfl
  intro i j k hij hjk
  exact ⟨fun h => not_lower_pattern N hN hfull hp hq hedge L R i j k hij hjk
      ⟨(hc k i).mp h.1,(hc k j).mp h.2⟩,
    fun h => not_upper_pattern N hN hfull hp hq hedge L R i j k hij hjk
      ⟨(hc j i).mp h.1,(hc k i).mp h.2⟩⟩

end Erdos1016.ExactMaximumSupport.FullPairAvoidance
