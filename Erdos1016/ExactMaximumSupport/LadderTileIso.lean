import Erdos1016.ExactMaximumSupport.LadderTileEdges

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Exact physical relabeling from canonical tiles to the permutation ladder

Every matching label belongs to its canonical block. Every rail label is a
cap, an interface, or the internal rail edge of a square. Equal edge counts
then turn this exhaustive physical map into an equivalence.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LadderTileIso
open BoundaryTrace BoundaryTrace.Network LadderPermutation LadderTileOrder MixedTiles
open LadderTileSequence LadderTileEdges
variable {n k : ℕ} (π : Equiv.Perm (Fin n)) (hc : (tileStarts π).card=k+1)

/-- Every original rail position belongs to a concrete canonical tile. -/
theorem exists_tile (hπ : AvoidsLadderPatterns π) (j : Fin n) :
    ∃ i : Fin (k+1),j ∈ tile π (anchor π hc i) := by
  have hmem : j ∈ (tileStarts π).biUnion (tile π) := by rw [tiles_cover hπ]; simp
  obtain ⟨a,ha,hja⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨i,rfl⟩ := exists_start π ha
  refine ⟨(index π hc).symm i,?_⟩
  simpa only [anchor,Equiv.apply_symm_apply] using hja

/-- A tile supplies every matching label whose position lies in that block. -/
theorem inner_matching_cover (i : Fin (k+1)) (j : Fin n)
    (hj : j ∈ tile π (anchor π hc i)) :
    ∃ e : (tiles π hc i).Edge,
      innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e=Sum.inr j := by
  have hfix := LadderTileSequence.rung_fixed π hc i
  generalize ht : tiles π hc i=t
  cases t with
  | rung =>
    have he : j=anchor π hc i := by simpa [tile,hfix ht] using hj
    exact ⟨(),by rw [he]; rfl⟩
  | square =>
    simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨(false,true),rfl⟩
    · exact ⟨(true,false),rfl⟩

/-- A moved block position supplies the internal rail label of its square. -/
theorem inner_rail_cover (i : Fin (k+1)) (r : Bool)
    (hne : π (anchor π hc i) ≠ anchor π hc i) :
    ∃ e : (tiles π hc i).Edge,
      innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e=
        Sum.inl ((π (anchor π hc i)).castSucc,r) := by
  have hfix := LadderTileSequence.rung_fixed π hc i
  generalize ht : tiles π hc i=t
  cases t with
  | rung => exact (hne (hfix ht)).elim
  | square => exact ⟨(r,r),by simp [innerMap]⟩

/-- Every original physical matching label is retained. -/
theorem matching_coverage (hπ : AvoidsLadderPatterns π) (j : Fin n) :
    ∃ e : CappedEdge (tiles π hc),edgeMap π hc e=Sum.inr j := by
  obtain ⟨i,hi⟩ := exists_tile π hc hπ j
  obtain ⟨e,he⟩ := inner_matching_cover π hc i j hi
  exact ⟨Sum.inl (Sum.inl ⟨i,e⟩),he⟩

/-- Every original physical rail label is retained. -/
theorem rail_coverage (hπ : AvoidsLadderPatterns π) (j : Fin (n+1)) (r : Bool) :
    ∃ e : CappedEdge (tiles π hc),edgeMap π hc e=Sum.inl (j,r) := by
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    exact ⟨Sum.inr (Sum.inl r),by subst j; rfl⟩
  by_cases hjn : j.val=n
  · have hj : j=Fin.last n := Fin.ext hjn
    exact ⟨Sum.inr (Sum.inr r),by subst j; rfl⟩
  have hjlt : j.val<n := by have := j.isLt; omega
  let x : Fin n := ⟨j.val,hjlt⟩
  obtain ⟨i,hi⟩ := exists_tile π hc hπ x
  by_cases hstart : x=anchor π hc i
  · have hipos : 0 < (i.val : ℕ) := by
      apply Nat.pos_of_ne_zero
      intro hn
      have hi0 : i=0 := Fin.ext hn
      have hz := anchor_first π hc hπ
      rw [←hi0,←hstart] at hz
      exact hj0 hz
    let a : Fin k := ⟨i.val-1,by have := i.isLt; omega⟩
    have hai : a.succ=i := by apply Fin.ext; change i.val-1+1=i.val; omega
    refine ⟨Sum.inl (Sum.inr (a,r)),?_⟩
    change Sum.inl ((anchor π hc a.succ).castSucc,r)=Sum.inl (j,r)
    rw [hai,←hstart]
    rfl
  · have hmatch : x=π (anchor π hc i) := by
      simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hi
      exact hi.resolve_left hstart
    have hne : π (anchor π hc i)≠anchor π hc i := by
      intro he
      exact hstart (hmatch.trans he)
    obtain ⟨e,he⟩ := inner_rail_cover π hc i r hne
    refine ⟨Sum.inl (Sum.inl ⟨i,e⟩),?_⟩
    change innerMap (anchor π hc i) (π (anchor π hc i)) (tiles π hc i) e=Sum.inl (j,r)
    rw [he,←hmatch]
    rfl

/-- The complete physical label map is onto. -/
theorem edgeMap_surjective (hπ : AvoidsLadderPatterns π) : Function.Surjective (edgeMap π hc) := by
  rintro (⟨j,r⟩ | j)
  · exact rail_coverage π hc hπ j r
  · exact matching_coverage π hc hπ j

/-- Both physical label types have exactly the same cardinality. -/
theorem edge_card_eq (hπ : AvoidsLadderPatterns π) :
    Fintype.card (CappedEdge (tiles π hc))=Fintype.card (PermutationLadder.Edge n) := by
  rw [capped_edge_card,total_weight π hc hπ]
  simp [PermutationLadder.Edge]
  omega

/-- The exhaustive physical map is an edge equivalence. -/
def edges (hπ : AvoidsLadderPatterns π) :
    CappedEdge (tiles π hc) ≃ PermutationLadder.Edge n :=
  Equiv.ofBijective (edgeMap π hc)
    ⟨(Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq (edge_card_eq π hc hπ))).mpr
      (edgeMap_surjective π hc hπ),edgeMap_surjective π hc hπ⟩

/-- The exact cap-preserving physical isomorphism for the nonempty canonical tile sequence. -/
def cappedIso (hπ : AvoidsLadderPatterns π) :
    NetworkIso (capped (tiles π hc)) (PermutationLadder.network π) where
  vertices := vertices π hc hπ
  edges := edges π hc hπ
  joins := edgeMap_joins π hc hπ

/-- Every nonempty pattern-avoiding physical ladder is a concrete capped mixed ladder. -/
theorem exists_capped_iso (hπ : AvoidsLadderPatterns π) (hn : 0<n) :
    ∃ k : ℕ,∃ T : Fin (k+1) → Kind,∃ R : NetworkIso (capped T) (PermutationLadder.network π),
      weight T=n ∧ R.vertices (Sum.inr false)=PermutationLadder.left n ∧
      R.vertices (Sum.inr true)=PermutationLadder.right n := by
  have hpos := tile_count_pos π hn
  let k := (tileStarts π).card-1
  have hc : (tileStarts π).card=k+1 := by dsimp [k]; omega
  exact ⟨k,tiles π hc,cappedIso π hc hπ,total_weight π hc hπ,rfl,rfl⟩

end Erdos1016.ExactMaximumSupport.LadderTileIso
