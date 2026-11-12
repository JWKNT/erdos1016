import Erdos1016.ExactMaximumSupport.MinimalCyclicInterval
import Erdos1016.ExactMaximumSupport.VertexRankDeletion
import Erdos1016.Graph.PackingCover
import Erdos1016.Graph.ConnectedRegionBoundary

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Disjoint cyclic intervals with a forest remainder

An actual connected support visits every integer level between its extreme levels.
Thus its interval hull avoids every whole interval that its support avoids.
A maximal disjoint family of small cyclic intervals consequently leaves a labelled forest.

The local small-interval theorem remains an explicit input here.
All selected regions, cycles, and forest events use the original physical multigraph.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.IntervalCyclePacking
open FiniteMultiGraph ThinIntervalBoundary

local instance intervalPackingDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (P : Finset G.Vertex) (level : G.Vertex → ℤ)

/-- A connected vertex region visits every intermediate integer level. -/
theorem exists_vertex_at_level (R : Finset G.Vertex)
    (hR : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧
      level (G.dst e) ≤ level (G.src e)+1)
    (u v : G.Vertex) (hu : u ∈ R) (hv : v ∈ R)
    (j : ℤ) (huj : level u ≤ j) (hjv : j ≤ level v) :
    ∃ w ∈ R, level w = j := by
  by_cases heq : level u = j
  · exact ⟨u, hu, heq⟩
  obtain ⟨p⟩ := hR.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Proof.ConnectedRegionBoundary.Walk.exists_adj_boundary
      (S := {w : {v : G.Vertex // v ∈ R} | level w.1 < j}) p
      (by change level u < j; omega) (by change ¬ level v < j; omega)
  have hbound : level b.1 ≤ level a.1+1 := by
    obtain ⟨_, e, h | h⟩ := hab
    · simpa only [h.1, h.2] using (hlevel e).2
    · simpa only [h.1, h.2] using (hlevel e).1
  have hal : level a.1 < j := ha
  have hbl : ¬ level b.1 < j := hb
  exact ⟨b.1, b.2, by omega⟩

/-- A cycle's interval hull avoids any whole unmarked interval avoided by the cycle. -/
theorem exists_cycle_hull (z : G.EdgeWord) (hz : G.IsCycleWord z)
    (hout : CycleRegions.region G z ⊆ Pᶜ)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧
      level (G.dst e) ≤ level (G.src e)+1) :
    ∃ a b : ℤ,
      CycleRegions.region G z ⊆ region G P level a b ∧
      ∀ c d : ℤ, Disjoint (CycleRegions.region G z) (region G P level c d) →
        Disjoint (region G P level a b) (region G P level c d) := by
  let R := CycleRegions.region G z
  have hconn := CycleRegions.cycle_region_connected G z hz
  have hne : R.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v.1, v.2⟩
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image R level hne
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image R level hne
  refine ⟨level u, level v, ?_, ?_⟩
  · intro w hw
    exact (mem_region G P level _ _ w).mpr
      ⟨Finset.mem_compl.mp (hout hw), hmin w hw, hmax w hw⟩
  · intro c d hd
    apply Finset.disjoint_left.mpr
    intro w hw hc
    have hh := (mem_region G P level _ _ w).mp hw
    have hc' := (mem_region G P level c d w).mp hc
    obtain ⟨y, hy, heq⟩ := exists_vertex_at_level G level R hconn hlevel u v hu hv
      (level w) hh.2.1 hh.2.2
    apply Finset.disjoint_left.mp hd hy
    exact (mem_region G P level c d y).mpr
      ⟨Finset.mem_compl.mp (hout hy), by omega, by omega⟩

/-- Eligibility describes a literal full unmarked interval, not a chosen cycle support. -/
def Eligible (L : ℕ) (R : Finset G.Vertex) : Prop :=
  (∃ a b : ℤ, R = region G P level a b) ∧ R.card ≤ L ∧ G.HasCycleIn R

theorem eligible_nonempty (L : ℕ) (R : Finset G.Vertex) (hR : Eligible G P level L R) :
    R.Nonempty := by
  obtain ⟨z, hz, hs⟩ := hR.2.2
  obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := Function.ne_iff.mp hz.1
  exact ⟨G.src e, (hs e he).1⟩

theorem eligible_outside (L : ℕ) (R : Finset G.Vertex) (hR : Eligible G P level L R) :
    R ⊆ Pᶜ := by
  obtain ⟨a, b, rfl⟩ := hR.1
  intro v hv
  exact Finset.mem_compl.mpr ((mem_region G P level a b v).mp hv).1

/-- The finite powerset gives a maximal disjoint family of eligible actual intervals. -/
theorem exists_maximal (L : ℕ) :
    ∃ F : Finset (Finset G.Vertex),
      (∀ R ∈ F, Eligible G P level L R) ∧
      (∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S) ∧
      ∀ R, Eligible G P level L R → ((F.biUnion id) ∩ R).Nonempty := by
  let candidates := Finset.univ.filter (Eligible G P level L)
  have hn : ∀ R ∈ candidates, (id R).Nonempty := by
    intro R hR
    exact eligible_nonempty G P level L R (Finset.mem_filter.mp hR).2
  obtain ⟨F, hF, hd, hh⟩ := PackingCover.exists_maximal_disjoint_family candidates id hn
  refine ⟨F, fun R hR => (Finset.mem_filter.mp (hF hR)).2, hd, ?_⟩
  intro R hR
  exact hh R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)

/-- Local small cyclic intervals yield disjoint small intervals with an actual forest remainder. -/
theorem exists_packing_with_forest_remainder (L : ℕ) (hloop : G.IsLoopless)
    (hlevel : ∀ e, level (G.src e) ≤ level (G.dst e)+1 ∧
      level (G.dst e) ≤ level (G.src e)+1)
    (hlocal : ∀ a b : ℤ, G.HasCycleIn (region G P level a b) →
      ∃ c d : ℤ, region G P level c d ⊆ region G P level a b ∧
        (region G P level c d).card ≤ L ∧ G.HasCycleIn (region G P level c d)) :
    ∃ F : Finset (Finset G.Vertex),
      (∀ R ∈ F, Eligible G P level L R) ∧
      (∀ R ∈ F, ∀ S ∈ F, R ≠ S → Disjoint R S) ∧
      (F.biUnion id) ⊆ Pᶜ ∧
      G.IsForestWord (G.restrictEdges (G.internalEdges (Pᶜ \ F.biUnion id)) (fun _ => 1)) := by
  obtain ⟨F, hF, hd, hhit⟩ := exists_maximal G P level L
  refine ⟨F, hF, hd, ?_, ?_⟩
  · intro v hv
    obtain ⟨R, hR, hvR⟩ := Finset.mem_biUnion.mp hv
    exact eligible_outside G P level L R (hF R hR) hvR
  · by_contra hf
    obtain ⟨z, hz, hs⟩ := MinimalCyclicInterval.hasCycleIn_of_not_forest G hloop _ hf
    have hsub := MinimalCyclicInterval.cycle_region_subset_of_supported G z _ hs
    have hout : CycleRegions.region G z ⊆ Pᶜ := by
      intro v hv
      exact (Finset.mem_sdiff.mp (hsub hv)).1
    obtain ⟨a, b, hza, hhull⟩ := exists_cycle_hull G P level z hz hout hlevel
    have hcy : G.HasCycleIn (region G P level a b) := by
      refine ⟨z, hz, ?_⟩
      intro e he
      exact ⟨hza ((CycleRegions.mem_region G z _).mpr (G.selectedDegree_src_pos he)),
        hza ((CycleRegions.mem_region G z _).mpr (G.selectedDegree_dst_pos he))⟩
    obtain ⟨c, d, hsmall, hcard, hcyclic⟩ := hlocal a b hcy
    have heligible : Eligible G P level L (region G P level c d) := ⟨⟨c, d, rfl⟩, hcard, hcyclic⟩
    obtain ⟨v, hv⟩ := hhit _ heligible
    obtain ⟨R, hR, hvR⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).1
    obtain ⟨i, j, hRij⟩ := (hF R hR).1
    have hdis : Disjoint (CycleRegions.region G z) (region G P level i j) := by
      apply Finset.disjoint_left.mpr
      intro w hwz hwij
      have hwR : w ∈ R := hRij.symm ▸ hwij
      exact (Finset.mem_sdiff.mp (hsub hwz)).2 (Finset.mem_biUnion.mpr ⟨R, hR, hwR⟩)
    exact Finset.disjoint_left.mp (hhull i j hdis)
      (hsmall (Finset.mem_inter.mp hv).2) (hRij ▸ hvR)

/-- The selected union contains at most `L` vertices per chosen interval. -/
theorem union_card_le (L : ℕ) (F : Finset (Finset G.Vertex))
    (hF : ∀ R ∈ F, Eligible G P level L R) : (F.biUnion id).card ≤ L * F.card := by
  calc
    _ ≤ ∑ R ∈ F, (id R).card := Finset.card_biUnion_le
    _ ≤ ∑ _R ∈ F, L := Finset.sum_le_sum fun R hR => (hF R hR).2.1
    _ = L * F.card := by simp [Nat.mul_comm]

/-- Actual forest deletion bounds the rank of the full marker exterior. -/
theorem exterior_rank_le (L : ℕ) (F : Finset (Finset G.Vertex))
    (hloop : G.IsLoopless) (hdegree : ∀ v, G.degree v ≤ 3)
    (hF : ∀ R ∈ F, Eligible G P level L R)
    (hforest : G.IsForestWord
      (G.restrictEdges (G.internalEdges (Pᶜ \ F.biUnion id)) (fun _ => 1))) :
    (LargeGirth.PieceCore.Induced.graph G Pᶜ).cycleRank ≤ 2 * L * F.card := by
  have hr := VertexRankDeletion.rank_region_le_twice_card_of_diff_forest G Pᶜ
    (F.biUnion id) hloop (fun v _ => hdegree v) hforest
  exact hr.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (union_card_le G P level L F hF))

end Erdos1016.ExactMaximumSupport.IntervalCyclePacking
