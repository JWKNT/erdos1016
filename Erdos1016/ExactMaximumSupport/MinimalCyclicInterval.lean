import Erdos1016.ExactMaximumSupport.ThinIntervalBoundary
import Erdos1016.ExactMaximumSupport.CycleRegions
import Erdos1016.ExactMaximum.NetBridge
import Erdos1016.ExactMaximum.LooplessBridge
import Erdos1016.Graph.Multigraph.ForestCharacterization

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A smallest cyclic interval

The intervals and cycle words retain the original physical edge labels.
Minimal span forces the chosen cycle to meet both endpoint layers, and deleting
its first layer from the entire interval leaves a labelled forest.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MinimalCyclicInterval
open FiniteMultiGraph BoundaryTrace BoundaryDecay
open ThinIntervalBoundary

local instance intervalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A nonforest induced physical edge set contains an actual supported cycle. -/
theorem hasCycleIn_of_not_forest (G : FiniteMultiGraph) (hloop : G.IsLoopless)
    (R : Finset G.Vertex)
    (hf : ¬ G.IsForestWord (G.restrictEdges (G.internalEdges R) (fun _ => 1))) :
    G.HasCycleIn R := by
  obtain ⟨x, hx, hs⟩ := G.exists_even_support_of_not_forest _ hf
  have hb : (looplessNetwork G).boundary (nonloopWord G x.1) = 0 := by
    rw [nonloopWord_boundary]
    exact x.2
  have hn : nonloopWord G x.1 ≠ 0 :=
    (G.ne_zero_iff_nonloopWord x.1 (fun e he => (hloop e he).elim)).1 hx
  obtain ⟨y, hy, hys⟩ := (looplessNetwork G).exists_isCycleWord_subword _ hb hn
  apply (G.hasCycleIn_iff_looplessNetwork hloop R).2
  refine ⟨y, hy, ?_⟩
  intro e he
  have hf' := hs e.1 (hys e he)
  have hi : e.1 ∈ G.internalEdges R := by
    by_contra hi
    simp [restrictEdges, hi] at hf'
  exact (Finset.mem_filter.mp hi).2

/-- Edge support in a region also contains every positive-degree vertex. -/
theorem cycle_region_subset_of_supported (G : FiniteMultiGraph) (z : G.EdgeWord)
    (R : Finset G.Vertex) (hs : G.SupportedIn z R) :
    CycleRegions.region G z ⊆ R := by
  intro v hv
  obtain ⟨e, he, hv' | hv'⟩ :=
    G.exists_edge_of_selectedDegree_pos ((CycleRegions.mem_region G z v).mp hv)
  · exact hv' ▸ (hs e he).1
  · exact hv' ▸ (hs e he).2

variable (G : FiniteMultiGraph) (P : Finset G.Vertex) (level : G.Vertex → ℤ)

theorem interval_order {a b : ℤ} (h : G.HasCycleIn (region G P level a b)) : a ≤ b := by
  obtain ⟨z, hz, hs⟩ := h
  obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := Function.ne_iff.mp hz.1
  have hh := (mem_region G P level a b _).mp (hs e he).1
  omega

/-- Among the cyclic intervals inside a given interval, one has minimum span. -/
theorem exists_minimal {a b : ℤ} (h : G.HasCycleIn (region G P level a b)) :
    ∃ c d : ℤ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ G.HasCycleIn (region G P level c d) ∧
      ∀ i j : ℤ, a ≤ i → j ≤ b → G.HasCycleIn (region G P level i j) →
        (d-c).toNat ≤ (j-i).toNat := by
  let Q : ℕ → Prop := fun n => ∃ c d : ℤ,
    a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ (d-c).toNat = n ∧ G.HasCycleIn (region G P level c d)
  have hQ : ∃ n, Q n := ⟨(b-a).toNat,a,b,le_rfl,interval_order G P level h,le_rfl,rfl,h⟩
  obtain ⟨c,d,hac,hcd,hdb,hn,hcy⟩ := Nat.find_spec hQ
  refine ⟨c,d,hac,hcd,hdb,hcy,?_⟩
  intro i j hai hjb hij
  rw [hn]
  exact Nat.find_min' hQ ⟨i,j,hai,interval_order G P level hij,hjb,rfl,hij⟩

/-- A cycle in a minimum-span interval meets both endpoint layers. -/
theorem endpoint_witnesses {a b c d : ℤ}
    (hac : a ≤ c) (hdb : d ≤ b)
    (hmin : ∀ i j : ℤ, a ≤ i → j ≤ b → G.HasCycleIn (region G P level i j) →
      (d-c).toNat ≤ (j-i).toNat)
    (z : G.EdgeWord) (hz : G.IsCycleWord z) (hs : G.SupportedIn z (region G P level c d)) :
    (∃ u ∈ CycleRegions.region G z, level u = c) ∧
      (∃ v ∈ CycleRegions.region G z, level v = d) := by
  constructor
  · by_contra hn
    have hsup : G.SupportedIn z (region G P level (c+1) d) := by
      intro e he
      have hh := hs e he
      have h1 := (mem_region G P level c d _).mp hh.1
      have h2 := (mem_region G P level c d _).mp hh.2
      have hn1 : level (G.src e) ≠ c := fun hc =>
        hn ⟨G.src e,(CycleRegions.mem_region G z _).mpr (G.selectedDegree_src_pos he),hc⟩
      have hn2 : level (G.dst e) ≠ c := fun hc =>
        hn ⟨G.dst e,(CycleRegions.mem_region G z _).mpr (G.selectedDegree_dst_pos he),hc⟩
      exact ⟨(mem_region G P level (c+1) d _).mpr ⟨h1.1,by omega,h1.2.2⟩,
        (mem_region G P level (c+1) d _).mpr ⟨h2.1,by omega,h2.2.2⟩⟩
    have hc : G.HasCycleIn (region G P level (c+1) d) := ⟨z,hz,hsup⟩
    have ho := interval_order G P level hc
    have hm := hmin (c+1) d (by omega) hdb hc
    omega
  · by_contra hn
    have hsup : G.SupportedIn z (region G P level c (d-1)) := by
      intro e he
      have hh := hs e he
      have h1 := (mem_region G P level c d _).mp hh.1
      have h2 := (mem_region G P level c d _).mp hh.2
      have hn1 : level (G.src e) ≠ d := fun hd =>
        hn ⟨G.src e,(CycleRegions.mem_region G z _).mpr (G.selectedDegree_src_pos he),hd⟩
      have hn2 : level (G.dst e) ≠ d := fun hd =>
        hn ⟨G.dst e,(CycleRegions.mem_region G z _).mpr (G.selectedDegree_dst_pos he),hd⟩
      exact ⟨(mem_region G P level c (d-1) _).mpr ⟨h1.1,h1.2.1,by omega⟩,
        (mem_region G P level c (d-1) _).mpr ⟨h2.1,h2.2.1,by omega⟩⟩
    have hc : G.HasCycleIn (region G P level c (d-1)) := ⟨z,hz,hsup⟩
    have ho := interval_order G P level hc
    have hm := hmin c (d-1) hac (by omega) hc
    omega

/-- Deleting the entire first unmarked layer leaves a physical labelled forest. -/
theorem delete_first_layer_forest (hloop : G.IsLoopless) {a b c d : ℤ}
    (hac : a ≤ c) (hdb : d ≤ b)
    (hmin : ∀ i j : ℤ, a ≤ i → j ≤ b → G.HasCycleIn (region G P level i j) →
      (d-c).toNat ≤ (j-i).toNat) :
    G.IsForestWord (G.restrictEdges
      (G.internalEdges (region G P level c d \ layer G P level c)) (fun _ => 1)) := by
  by_contra hf
  obtain ⟨z,hz,hs⟩ := hasCycleIn_of_not_forest G hloop _ hf
  have hsup : G.SupportedIn z (region G P level (c+1) d) := by
    intro e he
    have hh := hs e he
    have key : ∀ v, v ∈ region G P level c d \ layer G P level c →
        v ∈ region G P level (c+1) d := by
      intro v hv
      obtain ⟨hr,hl⟩ := Finset.mem_sdiff.mp hv
      have hh := (mem_region G P level c d v).mp hr
      have hn : level v ≠ c := fun h => hl ((mem_layer G P level c v).mpr ⟨hh.1,h⟩)
      exact (mem_region G P level (c+1) d v).mpr ⟨hh.1,by omega,hh.2.2⟩
    exact ⟨key _ hh.1,key _ hh.2⟩
  have hc : G.HasCycleIn (region G P level (c+1) d) := ⟨z,hz,hsup⟩
  have ho := interval_order G P level hc
  have hm := hmin (c+1) d (by omega) hdb hc
  omega

/-- A genuine minimal cyclic subinterval, its extremal vertices, and its residual forest. -/
theorem exists_minimal_interval (hloop : G.IsLoopless) {a b : ℤ}
    (h : G.HasCycleIn (region G P level a b)) :
    ∃ c d : ℤ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
      region G P level c d ⊆ region G P level a b ∧
      ∃ z : G.EdgeWord, G.IsCycleWord z ∧
        CycleRegions.region G z ⊆ region G P level c d ∧
        (∃ u ∈ CycleRegions.region G z, level u = c) ∧
        (∃ v ∈ CycleRegions.region G z, level v = d) ∧
        G.IsForestWord (G.restrictEdges
          (G.internalEdges (region G P level c d \ layer G P level c)) (fun _ => 1)) := by
  obtain ⟨c,d,hac,hcd,hdb,hcy,hmin⟩ := exists_minimal G P level h
  obtain ⟨z,hz,hs⟩ := hcy
  refine ⟨c,d,hac,hcd,hdb,?_,z,hz,cycle_region_subset_of_supported G z _ hs,?_⟩
  · intro v hv
    have hh := (mem_region G P level c d v).mp hv
    exact (mem_region G P level a b v).mpr ⟨hh.1,by omega,by omega⟩
  · have hh := endpoint_witnesses G P level hac hdb hmin z hz hs
    exact ⟨hh.1,hh.2,delete_first_layer_forest G P level hloop hac hdb hmin⟩

end Erdos1016.ExactMaximumSupport.MinimalCyclicInterval
