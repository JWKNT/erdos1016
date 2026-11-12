import Erdos1016.Graph.Multigraph.RegionDegrees
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Physical boundaries of level windows

Every physical edge joins equal or consecutive integer levels. A symmetric
window contains only unmarked vertices. Its cut is charged to the two
next unmarked layers and the marked vertices in the expanded interval.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.Probability.LevelWindowBoundary
open FiniteMultiGraph

local instance levelDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (P : Finset G.Vertex) (level : G.Vertex → ℤ)

def window (j : ℤ) (n : ℕ) : Finset G.Vertex :=
  Finset.univ.filter fun v => v ∉ P ∧ j-(n : ℤ) ≤ level v ∧ level v ≤ j+(n : ℤ)

def markedWindow (j : ℤ) (n : ℕ) : Finset G.Vertex :=
  Finset.univ.filter fun v => v ∈ P ∧ j-(n : ℤ) ≤ level v ∧ level v ≤ j+(n : ℤ)

def markedLayer (j : ℤ) : Finset G.Vertex := Finset.univ.filter fun v => v ∈ P ∧ level v = j

def ring (j : ℤ) (n : ℕ) : Finset G.Vertex := window G P level j (n+1) \ window G P level j n

def boundaryContainer (j : ℤ) (n : ℕ) : Finset G.Vertex :=
  ring G P level j n ∪ markedWindow G P level j (n+1)

@[simp] theorem mem_window (j : ℤ) (n : ℕ) (v : G.Vertex) :
    v ∈ window G P level j n ↔ v ∉ P ∧ j-(n : ℤ) ≤ level v ∧ level v ≤ j+(n : ℤ) := by
  simp [window]

@[simp] theorem mem_markedWindow (j : ℤ) (n : ℕ) (v : G.Vertex) :
    v ∈ markedWindow G P level j n ↔ v ∈ P ∧ j-(n : ℤ) ≤ level v ∧ level v ≤ j+(n : ℤ) := by
  simp [markedWindow]

theorem window_mono (j : ℤ) {n m : ℕ} (hnm : n ≤ m) :
    window G P level j n ⊆ window G P level j m := by
  intro v hv
  rw [mem_window] at hv ⊢
  exact ⟨hv.1, by omega, by omega⟩

theorem mass_monotone (j : ℤ) : Monotone (fun n => (window G P level j n).card) :=
  fun _ _ h => Finset.card_le_card (window_mono G P level j h)

theorem mass_bounded (j : ℤ) : ∃ B, ∀ n, (window G P level j n).card ≤ B :=
  ⟨G.vertexCount, fun n => by simpa using Finset.card_le_univ (window G P level j n)⟩

theorem ring_card_add (j : ℤ) (n : ℕ) :
    (ring G P level j n).card + (window G P level j n).card = (window G P level j (n+1)).card :=
  Finset.card_sdiff_add_card_eq_card (window_mono G P level j (Nat.le_succ n))

theorem window_subset_unmarked (j : ℤ) (n : ℕ) : window G P level j n ⊆ Pᶜ := by
  intro v hv
  exact Finset.mem_compl.mpr ((mem_window G P level j n v).mp hv).1

theorem window_disjoint_container (j : ℤ) (n : ℕ) :
    Disjoint (window G P level j n) (boundaryContainer G P level j n) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact (Finset.mem_sdiff.mp hc).2 hv
  · exact ((mem_window G P level j n v).mp hv).1 ((mem_markedWindow G P level j (n+1) v).mp hc).1

/-- A neighbor just outside the unmarked window belongs to its boundary container. -/
theorem outside_neighbor_mem (j : ℤ) (n : ℕ) {u v : G.Vertex}
    (hu : u ∈ window G P level j n) (hv : v ∉ window G P level j n)
    (huv : level u ≤ level v+1) (hvu : level v ≤ level u+1) :
    v ∈ boundaryContainer G P level j n := by
  have hu' := (mem_window G P level j n u).mp hu
  by_cases hp : v ∈ P
  · apply Finset.mem_union_right
    rw [mem_markedWindow]
    exact ⟨hp, by omega, by omega⟩
  · apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hv⟩
    rw [mem_window]
    exact ⟨hp, by omega, by omega⟩

/-- Each cut label is charged to the cut of the disjoint boundary container. -/
theorem cut_subset_container (j : ℤ) (n : ℕ)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧ level (G.dst e) ≤ level (G.src e)+1) :
    G.cutEdges (window G P level j n) ⊆ G.cutEdges (boundaryContainer G P level j n) := by
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  have hd := Finset.disjoint_left.mp (window_disjoint_container G P level j n)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hh with hh | hh
  · right
    exact ⟨fun h => hd hh.1 h, outside_neighbor_mem G P level j n hh.1 hh.2
      (hlevel e).1 (hlevel e).2⟩
  · left
    exact ⟨outside_neighbor_mem G P level j n hh.2 hh.1 (hlevel e).2 (hlevel e).1,
      fun h => hd hh.2 h⟩

/-- Bound the number of marked vertices in an interval by its number of levels. -/
theorem markedWindow_card_le (k : ℕ)
    (hmark : ∀ j, (markedLayer G P level j).card ≤ k) (j : ℤ) (n : ℕ) :
    (markedWindow G P level j n).card ≤ k*(2*n+1) := by
  let I := Finset.Icc (j-(n : ℤ)) (j+(n : ℤ))
  have hsub : markedWindow G P level j n ⊆ I.biUnion (markedLayer G P level) := by
    intro v hv
    have hh := (mem_markedWindow G P level j n v).mp hv
    apply Finset.mem_biUnion.mpr
    exact ⟨level v, Finset.mem_Icc.mpr hh.2, by simp [markedLayer, hh.1]⟩
  have hcard : I.card = 2*n+1 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (I.biUnion (markedLayer G P level)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, (markedLayer G P level i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, k := Finset.sum_le_sum (fun i _ => hmark i)
    _ = _ := by simp [hcard, Nat.mul_comm]

/-- The physical cut of a subcubic region is at most three times its order. -/
theorem cut_card_le_three (hdegree : ∀ v, G.degree v ≤ 3) (S : Finset G.Vertex) :
    (G.cutEdges S).card ≤ 3*S.card := by
  have he := G.sum_region_degree S
  have hh : (∑ v ∈ S, G.degree v) ≤ 3*S.card := by
    calc
      _ ≤ ∑ _v ∈ S, 3 := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- The symmetric-window boundary bound, with exact integer increment mass. -/
theorem cut_window_le (hdegree : ∀ v, G.degree v ≤ 3)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧ level (G.dst e) ≤ level (G.src e)+1)
    (k : ℕ) (hmark : ∀ j, (markedLayer G P level j).card ≤ k) (j : ℤ) (n : ℕ) :
    (G.cutEdges (window G P level j n)).card ≤
      3*(ring G P level j n).card + 3*k*(2*n+3) := by
  have hbound := (Finset.card_le_card (cut_subset_container G P level j n hlevel)).trans
    (cut_card_le_three G hdegree (boundaryContainer G P level j n))
  have hc := Finset.card_union_le (ring G P level j n) (markedWindow G P level j (n+1))
  have hm := markedWindow_card_le G P level k hmark j (n+1)
  dsimp [boundaryContainer] at hbound
  nlinarith

end Erdos1016.Probability.LevelWindowBoundary
