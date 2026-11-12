import Erdos1016.ExactMaximumSupport.FullPairOrderedRails
import Erdos1016.ExactMaximumSupport.PermutationLadder
import Erdos1016.ExactMaximumSupport.PolePathRank

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The actual full pole is its physical permutation ladder

Vertex and edge equivalences retain every original physical label.
The construction also includes the two-edge pole with no inner rail vertices.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.FullPairLadderIso
open BoundaryTrace BoundaryTrace.Network BoundaryDecay NetworkPathOrder FullPairOrderedWords
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
variable {s t : V} (hN : N.IsBridgelessTwoPole s t) (hfull : N.IsFullPair s t)
  {p q : N.Word} (hp : N.IsPathWord s t p) (hq : N.IsPathWord s t q)
  (hedge : ∀ e,p e≠0 → q e=0) (L : Order N s t p) (R : Order N s t q)
include hN hfull hp hq hedge
local notation "hcount" => FullPairPermutation.innerCount_eq N hN hfull hp hq hedge L R
local notation "π" => FullPairPermutation.permutation N hN hfull hp hq hedge L R
local notation "M" => FullPairPermutation.label N hN hfull hp hq hedge L
local notation "RV" => FullPairPermutation.rightVertex N hN hfull hp hq hedge L R

/-- Reindex an actual right-rail position with the common rail length. -/
def rightIndex (c : ℕ) (i : Fin (L.innerCount+c)) : Fin (R.innerCount+c) :=
  Fin.cast (congrArg (fun n => n+c) hcount) i

/-- The two actual inner rail vertices at a common position. -/
def innerVertex : Fin L.innerCount × Bool → V
  | (i,false) => L.innerVertex i
  | (i,true) => RV i

/-- The physical model's vertex map includes the actual cap vertices. -/
def vertices : PermutationLadder.Vertex L.innerCount → V
  | Sum.inl v => innerVertex N hN hfull hp hq hedge L R v
  | Sum.inr false => s
  | Sum.inr true => t

/-- The actual inner vertices are all distinct across both rails. -/
theorem innerVertex_injective : Function.Injective (innerVertex N hN hfull hp hq hedge L R) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c
  · exact Prod.ext (L.innerVertex_injective h) rfl
  · exact False.elim (FullPairPermutation.inner_disjoint N hN hfull hp hq hedge L R i j h)
  · exact False.elim (FullPairPermutation.inner_disjoint N hN hfull hp hq hedge L R j i h.symm)
  · have hc := R.innerVertex_injective h
    have hv := congrArg (fun x : Fin R.innerCount => x.val) hc
    exact Prod.ext (Fin.ext hv) rfl

theorem innerVertex_ne_left (v : Fin L.innerCount × Bool) :
    innerVertex N hN hfull hp hq hedge L R v≠s := by
  rcases v with ⟨i,b⟩
  cases b
  · exact L.innerVertex_ne_left i
  · exact R.innerVertex_ne_left (Fin.cast hcount i)

theorem innerVertex_ne_right (v : Fin L.innerCount × Bool) :
    innerVertex N hN hfull hp hq hedge L R v≠t := by
  rcases v with ⟨i,b⟩
  cases b
  · exact L.innerVertex_ne_right i
  · exact R.innerVertex_ne_right (Fin.cast hcount i)

/-- The physical vertex map is injective. -/
theorem vertices_injective : Function.Injective (vertices N hN hfull hp hq hedge L R) := by
  intro u v huv
  rcases u with u | b <;> rcases v with v | c
  · exact congrArg Sum.inl (innerVertex_injective N hN hfull hp hq hedge L R huv)
  · cases c
    · exact False.elim (innerVertex_ne_left N hN hfull hp hq hedge L R u huv)
    · exact False.elim (innerVertex_ne_right N hN hfull hp hq hedge L R u huv)
  · cases b
    · exact False.elim (innerVertex_ne_left N hN hfull hp hq hedge L R v huv.symm)
    · exact False.elim (innerVertex_ne_right N hN hfull hp hq hedge L R v huv.symm)
  · cases b <;> cases c
    · rfl
    · exact False.elim (hN.ne huv)
    · exact False.elim (hN.ne huv.symm)
    · rfl

/-- The actual two rails and cap vertices exhaust the original vertex set. -/
theorem vertices_surjective : Function.Surjective (vertices N hN hfull hp hq hedge L R) := by
  intro v
  by_cases hs : v=s
  · exact ⟨Sum.inr false,hs.symm⟩
  by_cases ht : v=t
  · exact ⟨Sum.inr true,ht.symm⟩
  rcases (FullPairMatching.residual_matching_degrees N hN hfull hp hq hedge).1 v with hv | hv
  · have hd : N.deg p v=2 := (hp.2.2.2.1 v hs ht).resolve_left (Nat.ne_of_gt hv)
    obtain ⟨i,hi⟩ := L.exists_innerVertex hp v hd
    exact ⟨Sum.inl (i,false),hi⟩
  · have hd : N.deg q v=2 := (hq.2.2.2.1 v hs ht).resolve_left (Nat.ne_of_gt hv)
    obtain ⟨j,hj⟩ := R.exists_innerVertex hq v hd
    let i : Fin L.innerCount := Fin.cast (hcount).symm j
    have hi : Fin.cast hcount i=j := Fin.ext rfl
    refine ⟨Sum.inl (i,true),?_⟩
    change R.innerVertex (Fin.cast hcount i)=v
    rw [hi,hj]

/-- Every canonical rail position maps to the matching actual path-order vertex. -/
theorem vertices_rail_false (i : Fin (L.innerCount+2)) :
    vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i false)=L.vertex i := by
  cases i using Fin.cases with
  | zero => exact L.first.symm
  | succ j =>
    cases j using Fin.lastCases with
    | last =>
      change vertices N hN hfull hp hq hedge L R
        (PermutationLadder.railVertex (Fin.last (L.innerCount+1)) false)=_
      rw [PermutationLadder.railVertex_last]
      exact L.last.symm
    | cast j =>
      change vertices N hN hfull hp hq hedge L R
        (PermutationLadder.railVertex j.succ.castSucc false)=_
      rw [PermutationLadder.railVertex_inner]
      rfl

theorem vertices_rail_true (i : Fin (L.innerCount+2)) :
    vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i true)=
      R.vertex (rightIndex N hN hfull hp hq hedge L R 2 i) := by
  cases i using Fin.cases with
  | zero =>
    have h : rightIndex N hN hfull hp hq hedge L R 2 0=0 := Fin.ext rfl
    rw [h,R.first]
    rfl
  | succ j =>
    cases j using Fin.lastCases with
    | last =>
      have h : rightIndex N hN hfull hp hq hedge L R 2
          (Fin.last (L.innerCount+1))=Fin.last (R.innerCount+1) := by
        apply Fin.ext
        change L.innerCount+1=R.innerCount+1
        exact congrArg (fun n => n+1) hcount
      change vertices N hN hfull hp hq hedge L R
        (PermutationLadder.railVertex (Fin.last (L.innerCount+1)) true)=
          R.vertex (rightIndex N hN hfull hp hq hedge L R 2 (Fin.last (L.innerCount+1)))
      rw [PermutationLadder.railVertex_last,h,R.last]
      rfl
    | cast j =>
      change vertices N hN hfull hp hq hedge L R
        (PermutationLadder.railVertex j.succ.castSucc true)=_
      rw [PermutationLadder.railVertex_inner]
      change R.innerVertex (Fin.cast hcount j)=R.vertex _
      apply congrArg R.vertex
      exact Fin.ext rfl

/-- All original rail and matching labels define the physical edge map. -/
def edges : PermutationLadder.Edge L.innerCount → E
  | Sum.inl (i,false) => L.edge i
  | Sum.inl (i,true) => R.edge (rightIndex N hN hfull hp hq hedge L R 1 i)
  | Sum.inr i => M i

omit [Fintype V] [Fintype E] hN hfull hp hq in
/-- A label cannot belong to both ordered rails. -/
theorem rail_edges_ne (i : Fin (L.innerCount+1)) (j : Fin (R.innerCount+1)) : L.edge i≠R.edge j := by
  intro hij
  have hp' := (L.edge_support _).mpr ⟨i,rfl⟩
  have hq' := (R.edge_support _).mpr ⟨j,rfl⟩
  rw [hij] at hp'
  exact hq' (hedge _ hp')

/-- Every physical label is retained exactly once. -/
theorem edges_injective : Function.Injective (edges N hN hfull hp hq hedge L R) := by
  intro e f hef
  rcases e with ⟨i,b⟩ | i <;> rcases f with ⟨j,c⟩ | j
  · cases b <;> cases c
    · exact congrArg Sum.inl (Prod.ext (L.edge_injective hef) rfl)
    · exact False.elim (rail_edges_ne N hedge L R i _ hef)
    · exact False.elim (rail_edges_ne N hedge L R j _ hef.symm)
    · have h := R.edge_injective hef
      have hv := congrArg (fun x : Fin (R.innerCount+1) => x.val) h
      exact congrArg Sum.inl (Prod.ext (Fin.ext hv) rfl)
  · cases b
    · exact False.elim (left_ne_label N hN hfull hp hq hedge L i j hef)
    · exact False.elim (right_ne_label N hN hfull hp hq hedge L R _ j hef)
  · cases c
    · exact False.elim (left_ne_label N hN hfull hp hq hedge L j i hef.symm)
    · exact False.elim (right_ne_label N hN hfull hp hq hedge L R _ i hef.symm)
  · exact congrArg Sum.inr (FullPairPermutation.label_injective N hN hfull hp hq hedge L hef)

theorem edges_surjective : Function.Surjective (edges N hN hfull hp hq hedge L R) := by
  intro e
  rcases FullPairPermutation.edge_coverage N hN hfull hp hq hedge L R e with
    ⟨i,hi⟩ | ⟨j,hj⟩ | ⟨i,hi⟩
  · exact ⟨Sum.inl (i,false),hi⟩
  · let i : Fin (L.innerCount+1) := Fin.cast (congrArg (fun n => n+1) (hcount).symm) j
    have hi : rightIndex N hN hfull hp hq hedge L R 1 i=j := Fin.ext rfl
    refine ⟨Sum.inl (i,true),?_⟩
    change R.edge (rightIndex N hN hfull hp hq hedge L R 1 i)=e
    rw [hi,hj]
  · exact ⟨Sum.inr i,hi⟩

/-- The canonical model retains the endpoints of every original physical label. -/
theorem edges_join (e : PermutationLadder.Edge L.innerCount) :
    N.Joins (edges N hN hfull hp hq hedge L R e)
      (vertices N hN hfull hp hq hedge L R ((PermutationLadder.network π).src e))
      (vertices N hN hfull hp hq hedge L R ((PermutationLadder.network π).dst e)) := by
  rcases e with ⟨i,b⟩ | i
  · cases b
    · change N.Joins (L.edge i)
        (vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i.castSucc false))
        (vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i.succ false))
      rw [vertices_rail_false,vertices_rail_false]
      exact L.joins i
    · change N.Joins (R.edge (rightIndex N hN hfull hp hq hedge L R 1 i))
        (vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i.castSucc true))
        (vertices N hN hfull hp hq hedge L R (PermutationLadder.railVertex i.succ true))
      rw [vertices_rail_true,vertices_rail_true]
      have hl : rightIndex N hN hfull hp hq hedge L R 2 i.castSucc=
          (rightIndex N hN hfull hp hq hedge L R 1 i).castSucc := Fin.ext rfl
      have hr : rightIndex N hN hfull hp hq hedge L R 2 i.succ=
          (rightIndex N hN hfull hp hq hedge L R 1 i).succ := Fin.ext rfl
      rw [hl,hr]
      exact R.joins _
  · exact FullPairPermutation.label_joins N hN hfull hp hq hedge L R i

/-- An actual isomorphism from the canonical physical ladder to the original full pole. -/
def iso : NetworkIso (PermutationLadder.network π) N where
  vertices := Equiv.ofBijective (vertices N hN hfull hp hq hedge L R)
    ⟨vertices_injective N hN hfull hp hq hedge L R,vertices_surjective N hN hfull hp hq hedge L R⟩
  edges := Equiv.ofBijective (edges N hN hfull hp hq hedge L R)
    ⟨edges_injective N hN hfull hp hq hedge L R,edges_surjective N hN hfull hp hq hedge L R⟩
  joins := edges_join N hN hfull hp hq hedge L R

include R
/-- The common inner-rail count is one less than the original cycle rank. -/
theorem rank_eq : networkRank N=L.innerCount+1 := by
  have hc := Fintype.card_congr (iso N hN hfull hp hq hedge L R).vertices
  change Fintype.card ((Fin L.innerCount × Bool) ⊕ Bool)=Fintype.card V at hc
  rw [PolePathRank.bridgeless_order N s t hN] at hc
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hc
  omega

/-- The zero-inner-position model is exactly the rank-one case. -/
theorem inner_zero_iff_rank_one : L.innerCount=0 ↔ networkRank N=1 := by
  rw [rank_eq N hN hfull hp hq hedge L R]
  omega

omit hN hfull hp hq hedge R in
/-- An actual full pole supplies a physical ladder isomorphism, including its original caps. -/
theorem exists_ladder_iso {s t : V} (hN : N.IsBridgelessTwoPole s t)
    (hfull : N.IsFullPair s t) :
    ∃ n : ℕ, ∃ σ : Equiv.Perm (Fin n), ∃ I : NetworkIso (PermutationLadder.network σ) N,
      LadderPermutation.AvoidsLadderPatterns σ ∧
      I.vertices (PermutationLadder.left n)=s ∧
      I.vertices (PermutationLadder.right n)=t ∧ networkRank N=n+1 := by
  obtain ⟨p,q,hp,hq,hedge,L,R,hπ⟩ := FullPairOrderedRails.exists_ordered_rails N hN hfull
  exact ⟨L.innerCount,FullPairPermutation.permutation N hN hfull hp hq hedge L R,
    iso N hN hfull hp hq hedge L R,hπ,rfl,rfl,rank_eq N hN hfull hp hq hedge L R⟩

end Erdos1016.ExactMaximumSupport.FullPairLadderIso
