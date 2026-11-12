import Erdos1016.Probability.Avoidance.LevelWindowBoundary

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Interval boundaries beside a thin marker

Each marker vertex has at most one incidence outside the marker.
The physical boundary of an unmarked interval uses two neighboring layers
and the marked vertices in the expanded interval.
-/
noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
open FiniteMultiGraph
local instance thinIntervalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (P : Finset G.Vertex) (level : G.Vertex → ℤ)

def region (a b : ℤ) : Finset G.Vertex :=
  Finset.univ.filter fun v => v∉P ∧ a≤level v ∧ level v≤b

def layer (j : ℤ) : Finset G.Vertex :=
  Finset.univ.filter fun v => v∉P ∧ level v=j

def markedInterval (a b : ℤ) : Finset G.Vertex :=
  Finset.univ.filter fun v => v∈P ∧ a≤level v ∧ level v≤b

def neighbors (a b : ℤ) : Finset G.Vertex := layer G P level (a-1) ∪ layer G P level (b+1)

def container (a b : ℤ) : Finset G.Vertex :=
  neighbors G P level a b ∪ markedInterval G P level (a-1) (b+1)

/-- Delete precisely the physical edges internal to the marker. -/
def outsideWord : G.EdgeWord := G.restrictEdges (G.internalEdges P)ᶜ (fun _ => 1)

@[simp] theorem mem_region (a b : ℤ) (v : G.Vertex) :
    v∈region G P level a b ↔ v∉P ∧ a≤level v ∧ level v≤b := by simp [region]

@[simp] theorem mem_layer (j : ℤ) (v : G.Vertex) :
    v∈layer G P level j ↔ v∉P ∧ level v=j := by simp [layer]

@[simp] theorem mem_markedInterval (a b : ℤ) (v : G.Vertex) :
    v∈markedInterval G P level a b ↔ v∈P ∧ a≤level v ∧ level v≤b := by
  simp [markedInterval]

theorem region_disjoint_container (a b : ℤ) :
    Disjoint (region G P level a b) (container G P level a b) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  have hh := (mem_region G P level a b v).mp hv
  rcases Finset.mem_union.mp hc with hn | hm
  · rcases Finset.mem_union.mp hn with h | h
    · have h' := (mem_layer G P level (a-1) v).mp h
      omega
    · have h' := (mem_layer G P level (b+1) v).mp h
      omega
  · exact hh.1 ((mem_markedInterval G P level (a-1) (b+1) v).mp hm).1

theorem outside_neighbor_mem (a b : ℤ) {u v : G.Vertex}
    (hu : u∈region G P level a b) (hv : v∉region G P level a b)
    (huv : level u≤level v+1) (hvu : level v≤level u+1) :
    v∈container G P level a b := by
  have hu' := (mem_region G P level a b u).mp hu
  by_cases hp : v∈P
  · apply Finset.mem_union_right
    exact (mem_markedInterval G P level (a-1) (b+1) v).mpr ⟨hp,by omega,by omega⟩
  · apply Finset.mem_union_left
    have hn : ¬(a≤level v ∧ level v≤b) := by
      intro h
      exact hv ((mem_region G P level a b v).mpr ⟨hp,h⟩)
    have h : level v=a-1 ∨ level v=b+1 := by omega
    rcases h with h | h
    · exact Finset.mem_union_left _ ((mem_layer G P level (a-1) v).mpr ⟨hp,h⟩)
    · exact Finset.mem_union_right _ ((mem_layer G P level (b+1) v).mpr ⟨hp,h⟩)

theorem cut_subset_selected_container (a b : ℤ)
    (hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1) :
    G.cutEdges (region G P level a b) ⊆
      (G.cutEdges (container G P level a b)).filter (fun e => outsideWord G P e≠0) := by
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  have hd := Finset.disjoint_left.mp (region_disjoint_container G P level a b)
  have hi : e∉G.internalEdges P := by
    intro hi
    have hp := (Finset.mem_filter.mp hi).2
    rcases hh with h | h
    · exact ((mem_region G P level a b (G.src e)).mp h.1).1 hp.1
    · exact ((mem_region G P level a b (G.dst e)).mp h.2).1 hp.2
  refine Finset.mem_filter.mpr ⟨?_,by simp [outsideWord,restrictEdges,hi]⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rcases hh with h | h
  · exact Or.inr ⟨fun hc => hd h.1 hc,
      outside_neighbor_mem G P level a b h.1 h.2 (hlevel e).1 (hlevel e).2⟩
  · exact Or.inl ⟨outside_neighbor_mem G P level a b h.2 h.1 (hlevel e).2 (hlevel e).1,
      fun hc => hd h.2 hc⟩

omit P level in
theorem selectedDegree_le_degree (x : G.EdgeWord) (v : G.Vertex) :
    G.selectedDegree x v≤G.degree v := by
  simp only [degree,selectedDegree_eq_sum_endpoints]
  apply Finset.sum_le_sum
  intro e _
  by_cases hx : x e=0 <;> simp [hx]

theorem neighbors_disjoint_marked (a b : ℤ) :
    Disjoint (neighbors G P level a b) (markedInterval G P level (a-1) (b+1)) := by
  apply Finset.disjoint_left.mpr
  intro v hn hm
  have hp := ((mem_markedInterval G P level (a-1) (b+1) v).mp hm).1
  rcases Finset.mem_union.mp hn with h | h
  · exact ((mem_layer G P level (a-1) v).mp h).1 hp
  · exact ((mem_layer G P level (b+1) v).mp h).1 hp

/-- The interval cut uses at most three incidences per neighboring unmarked vertex. -/
theorem cut_region_le (a b : ℤ) (hdeg : ∀ v,G.degree v≤3)
    (hmark : ∀ v∈P,G.selectedDegree (outsideWord G P) v≤1)
    (hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1) :
    (G.cutEdges (region G P level a b)).card ≤
      3*(neighbors G P level a b).card+(markedInterval G P level (a-1) (b+1)).card := by
  have hcard := Finset.card_le_card (cut_subset_selected_container G P level a b hlevel)
  have hsum := G.sum_region_selectedDegree (outsideWord G P) (container G P level a b)
  have hbound : (∑ v∈container G P level a b,G.selectedDegree (outsideWord G P) v) ≤
      3*(neighbors G P level a b).card+(markedInterval G P level (a-1) (b+1)).card := by
    rw [container,Finset.sum_union (neighbors_disjoint_marked G P level a b)]
    apply Nat.add_le_add
    · calc
        _ ≤ ∑ _v∈neighbors G P level a b,3 := Finset.sum_le_sum
          (fun v _ => (selectedDegree_le_degree G _ v).trans (hdeg v))
        _ = _ := by simp [Nat.mul_comm]
    · calc
        _ ≤ ∑ _v∈markedInterval G P level (a-1) (b+1),1 := Finset.sum_le_sum
          (fun v hv => hmark v ((mem_markedInterval G P level (a-1) (b+1) v).mp hv).1)
        _ = _ := by simp
  omega

theorem markedInterval_card_le (a b : ℤ)
    (hmark : ∀ j,(Probability.LevelWindowBoundary.markedLayer G P level j).card≤1) :
    (markedInterval G P level a b).card≤(b-a+1).toNat := by
  let I := Finset.Icc a b
  have hsub : markedInterval G P level a b ⊆
      I.biUnion (Probability.LevelWindowBoundary.markedLayer G P level) := by
    intro v hv
    have hh := (mem_markedInterval G P level a b v).mp hv
    exact Finset.mem_biUnion.mpr ⟨level v,Finset.mem_Icc.mpr hh.2,by
      simp [Probability.LevelWindowBoundary.markedLayer,hh.1]⟩
  calc
    _ ≤ (I.biUnion (Probability.LevelWindowBoundary.markedLayer G P level)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j∈I,(Probability.LevelWindowBoundary.markedLayer G P level j).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j∈I,1 := Finset.sum_le_sum (fun j _ => hmark j)
    _ = _ := by
      simp [I,Int.card_Icc]
      omega

/-- The boundary estimate used in the shortest cyclic interval argument. -/
theorem cut_region_le_width (a b : ℤ) (θ : ℕ) (hdeg : ∀ v,G.degree v≤3)
    (hfurther : ∀ v∈P,G.selectedDegree (outsideWord G P) v≤1)
    (hlevel : ∀ e,level (G.src e)≤level (G.dst e)+1 ∧ level (G.dst e)≤level (G.src e)+1)
    (hwidth : ∀ j,(layer G P level j).card≤θ)
    (hmark : ∀ j,(Probability.LevelWindowBoundary.markedLayer G P level j).card≤1) :
    (G.cutEdges (region G P level a b)).card≤6*θ+(b-a+3).toNat := by
  have hc := cut_region_le G P level a b hdeg hfurther hlevel
  have hn := Finset.card_union_le (layer G P level (a-1)) (layer G P level (b+1))
  have hm := markedInterval_card_le G P level (a-1) (b+1) hmark
  have he : b+1-(a-1)+1=b-a+3 := by ring
  rw [he] at hm
  dsimp only [neighbors] at hc
  have h1 := hwidth (a-1)
  have h2 := hwidth (b+1)
  omega

end Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
