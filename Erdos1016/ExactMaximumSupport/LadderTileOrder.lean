import Erdos1016.ExactMaximumSupport.LadderPermutation
import Erdos1016.ExactMaximumSupport.MixedTiles
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Ordered tile coordinates for a ladder matching

Canonical tile starts are enumerated in their actual rail order.
The start of each tile equals the total weight of the preceding tiles.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LadderTileOrder
open LadderPermutation
variable {n : ℕ}

/-- Canonical starts in increasing rail order. -/
def start (π : Equiv.Perm (Fin n)) : Fin (tileStarts π).card ↪o Fin n :=
  (tileStarts π).orderEmbOfFin rfl

theorem start_mem (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card) :
    start π i ∈ tileStarts π := (tileStarts π).orderEmbOfFin_mem rfl i

theorem exists_start (π : Equiv.Perm (Fin n)) {x : Fin n} (hx : x ∈ tileStarts π) :
    ∃ i, start π i = x := by
  have hh : x ∈ Set.range (start π) := by
    change x ∈ Set.range ((tileStarts π).orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact hx
  exact hh

/-- Every tile lies at or after its canonical start. -/
theorem start_le_member (π : Equiv.Perm (Fin n)) {i x : Fin n}
    (hi : i ∈ tileStarts π) (hx : x ∈ tile π i) : i ≤ x := by
  have hs := (Finset.mem_filter.mp hi).2
  simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact le_rfl
  · exact hs

/-- Tiles before a given start cover exactly the earlier rail positions. -/
theorem prefix_tiles {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    {i : Fin n} (hi : i ∈ tileStarts π) :
    ((tileStarts π).filter fun j => j < i).biUnion (tile π) = Finset.Iio i := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hj,hji⟩ := Finset.mem_filter.mp hj
    have hxbound : x.val ≤ j.val+1 := by
      simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · omega
      · exact (displacement_le_one hπ j).1
    have hxne : x ≠ i := by
      intro hxi
      have hd := tiles_pairwise_disjoint hπ hj hi (ne_of_lt hji)
      exact Finset.disjoint_left.mp hd hx (by simp [tile,hxi])
    have hxval : x.val ≠ i.val := fun h => hxne (Fin.ext h)
    exact Finset.mem_Iio.mpr (by change x.val < i.val; omega)
  · intro hx
    have hxi := Finset.mem_Iio.mp hx
    have hcover : x ∈ (tileStarts π).biUnion (tile π) := by rw [tiles_cover hπ]; simp
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hcover
    have hjx := start_le_member π hj hxj
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hjx.trans_lt hxi⟩,hxj⟩

/-- The sum of the preceding canonical tile weights is the actual start index. -/
theorem prefix_weights {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    {i : Fin n} (hi : i ∈ tileStarts π) :
    ∑ j ∈ (tileStarts π).filter (fun j => j < i), tileWeight π j = i.val := by
  classical
  have hdis : (↑((tileStarts π).filter fun j => j < i) : Set (Fin n)).PairwiseDisjoint (tile π) := by
    intro a ha b hb hab
    exact tiles_pairwise_disjoint hπ (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  have hh := Finset.card_biUnion hdis
  rw [prefix_tiles hπ hi,Fin.card_Iio] at hh
  simpa only [tile_card] using hh.symm

/-- The ordered-coordinate version of the prefix identity. -/
theorem ordered_prefix_weights {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    (i : Fin (tileStarts π).card) :
    ∑ j ∈ Finset.Iio i, tileWeight π (start π j) = (start π i).val := by
  classical
  rw [← prefix_weights hπ (start_mem π i)]
  apply Finset.sum_bij (fun j _ => start π j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨start_mem π j,(start π).strictMono (Finset.mem_Iio.mp hj)⟩
  · intro a _ b _ hab
    exact (start π).injective hab
  · intro j hj
    obtain ⟨hj,hji⟩ := Finset.mem_filter.mp hj
    obtain ⟨k,rfl⟩ := exists_start π hj
    exact ⟨k,Finset.mem_Iio.mpr ((start π).lt_iff_lt.mp hji),rfl⟩
  · intro j _
    rfl

/-- Consecutive ordered tiles occupy consecutive rail intervals. -/
theorem consecutive_starts {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    (i j : Fin (tileStarts π).card) (hij : j.val = i.val+1) :
    (start π j).val = (start π i).val + tileWeight π (start π i) := by
  classical
  have hset : Finset.Iio j = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iio,Finset.mem_insert]
    have he : k = i ↔ k.val = i.val := Fin.ext_iff
    change k.val < j.val ↔ k = i ∨ k.val < i.val
    rw [he]
    omega
  have hh := ordered_prefix_weights hπ j
  rw [hset,Finset.sum_insert (by simp),ordered_prefix_weights hπ i] at hh
  omega

/-- The ordered weights still sum to the exact number of rail positions. -/
theorem ordered_total_weight {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    ∑ i, tileWeight π (start π i) = n := by
  classical
  calc
    _ = ∑ i ∈ tileStarts π, tileWeight π i := by
      apply Finset.sum_bij (fun i _ => start π i)
      · intro i _
        exact start_mem π i
      · intro a _ b _ hab
        exact (start π).injective hab
      · intro j hj
        obtain ⟨i,hi⟩ := exists_start π hj
        exact ⟨i,Finset.mem_univ _,hi⟩
      · intro i _
        rfl
    _ = n := sum_tileWeights hπ

/-- The last tile ends at the total rail length. -/
theorem last_endpoint {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    (i : Fin (tileStarts π).card) (hi : i.val+1 = (tileStarts π).card) :
    (start π i).val + tileWeight π (start π i) = n := by
  classical
  have hset : (Finset.univ : Finset (Fin (tileStarts π).card)) = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_Iio,true_iff]
    have hk := k.isLt
    have he : k = i ↔ k.val = i.val := Fin.ext_iff
    change k = i ∨ k.val < i.val
    rw [he]
    omega
  have hh := ordered_total_weight hπ
  rw [hset,Finset.sum_insert (by simp),ordered_prefix_weights hπ i] at hh
  omega

/-- A nonempty rail has at least one canonical tile. -/
theorem tile_count_pos (π : Equiv.Perm (Fin n)) (hn : 0 < n) : 0 < (tileStarts π).card := by
  apply Finset.card_pos.mpr
  refine ⟨⟨0,hn⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  change 0 ≤ (π ⟨0,hn⟩).val
  omega

/-- The first tile starts at the first rail position. -/
theorem first_start {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π)
    (i : Fin (tileStarts π).card) (hi : i.val = 0) : (start π i).val = 0 := by
  have hset : Finset.Iio i = ∅ := by
    ext j
    simp only [Finset.mem_Iio,Finset.not_mem_empty,iff_false]
    change ¬ j.val < i.val
    omega
  have hh := ordered_prefix_weights hπ i
  rw [hset,Finset.sum_empty] at hh
  exact hh.symm

/-- The tile kind uses the same rung/square convention as the physical model. -/
def kind (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card) : MixedTiles.Kind :=
  if π (start π i) = start π i then .rung else .square

@[simp] theorem kind_weight (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card) :
    (kind π i).weight = tileWeight π (start π i) := by
  unfold kind tileWeight
  split_ifs <;> rfl

end Erdos1016.ExactMaximumSupport.LadderTileOrder
