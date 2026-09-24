import Erdos1016.Decomposition.Descent.BondDecomposition
import Erdos1016.Boundary.CubicCutPorts

set_option autoImplicit false

/-!
# One actual leaf deletion

The deleted vertex is moved to the original exterior. Its two outside
incidences are not discarded. Cut, expansion, and exterior-component
comparisons are proved at this single step and can then be iterated.
-/
noncomputable section
namespace Erdos1016.SafeCore
local instance instSafeCoreLeafPruningPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

structure LeafWitness (U : Finset G.Vertex) where
  vertex : G.Vertex
  neighbor : G.Vertex
  vertex_mem : vertex ∈ U
  neighbor_mem : neighbor ∈ U
  different : vertex ≠ neighbor
  adjacent : G.toSimpleGraph.Adj vertex neighbor
  unique_neighbor : ∀ z ∈ U, G.toSimpleGraph.Adj vertex z → z = neighbor
  inside_degree : G.traceInsideDegree U vertex = 1

/-- Two orientations of one labelled nonloop edge have the same other end. -/
theorem edge_other_end_unique (e : G.Edge) {v w z : G.Vertex}
    (h : (G.src e = v ∧ G.dst e = w) ∨ (G.src e = w ∧ G.dst e = v))
    (k : (G.src e = v ∧ G.dst e = z) ∨ (G.src e = z ∧ G.dst e = v)) : w = z := by
  rcases h with h | h <;> rcases k with k | k
  · exact h.2.symm.trans k.2
  · exact False.elim (G.noLoops e (h.1.trans k.2.symm))
  · exact False.elim (G.noLoops e (k.1.trans h.2.symm))
  · exact h.1.symm.trans k.1

/-- A degree-one vertex supplies its unique actual neighbor and edge. -/
theorem leafWitness_of_insideDegree_one {U : Finset G.Vertex} {v : G.Vertex}
    (hv : v ∈ U) (hd : G.traceInsideDegree U v = 1) :
    Nonempty (LeafWitness G U) := by
  obtain ⟨e, heq⟩ := Finset.card_eq_one.1 hd
  have he : e ∈ G.traceInsideEdgesAt U v := by rw [heq]; simp
  obtain ⟨_, hinc, hs, ht⟩ := Finset.mem_filter.1 he
  have build (w : G.Vertex) (hw : w ∈ U)
      (hedge : (G.src e = v ∧ G.dst e = w) ∨ (G.src e = w ∧ G.dst e = v)) :
      Nonempty (LeafWitness G U) := by
    have ha : G.toSimpleGraph.Adj v w := ⟨e, one_ne_zero, hedge⟩
    refine ⟨⟨v, w, hv, hw, ha.ne, ha, ?_, hd⟩⟩
    intro z hz haz
    obtain ⟨f, _, hf⟩ := haz
    have hfe : f ∈ G.traceInsideEdgesAt U v := by
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hf with hf | hf
      · exact ⟨Or.inl hf.1, hf.1.symm ▸ hv, hf.2.symm ▸ hz⟩
      · exact ⟨Or.inr hf.2, hf.1.symm ▸ hz, hf.2.symm ▸ hv⟩
    have hfeq : f = e := by simpa only [heq, Finset.mem_singleton] using hfe
    subst f
    exact (edge_other_end_unique G e hedge hf).symm
  rcases hinc with hsV | htV
  · exact build (G.dst e) ht (Or.inl ⟨hsV, rfl⟩)
  · exact build (G.src e) hs (Or.inr ⟨rfl, htV⟩)

theorem singleton_cutSize (v : G.Vertex) : cutSize G {v} = G.degree v := by
  have heq : ownerCut G {v} = Finset.univ.filter (fun e => G.incident e v) := by
    ext e
    have hn := G.noLoops e
    simp only [mem_ownerCut, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and, PhysicalGraph.incident]
    constructor
    · tauto
    · intro h
      rcases h with h | h
      · exact Or.inl ⟨h, fun k => hn (h.trans k.symm)⟩
      · exact Or.inr ⟨fun k => hn (k.trans h.symm), h⟩
  unfold cutSize
  rw [heq]
  simp [PhysicalGraph.degree, PhysicalGraph.selectedDegree]

/-- The actual split edge set agrees with the internal incident-edge set. -/
theorem crossing_singleton_erase (U : Finset G.Vertex) (v : G.Vertex) (hv : v ∈ U) :
    crossing G {v} (U.erase v) = G.traceInsideEdgesAt U v := by
  ext e
  have hn := G.noLoops e
  simp only [mem_crossing, Finset.mem_singleton, Finset.mem_erase,
    PhysicalGraph.traceInsideEdgesAt, Finset.mem_filter, Finset.mem_univ,
    true_and, PhysicalGraph.incident]
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl h.1, h.1.symm ▸ hv, h.2.2⟩
    · exact ⟨Or.inr h.2, h.1.2, h.2.symm ▸ hv⟩
  · rintro ⟨h | h, hs, ht⟩
    · exact Or.inl ⟨h, fun k => hn (h.trans k.symm), ht⟩
    · exact Or.inr ⟨⟨fun k => hn (k.trans h.symm), hs⟩, h⟩

namespace LeafWitness
variable {G} {U : Finset G.Vertex} (l : LeafWitness G U)

def remainder : Finset G.Vertex := U.erase l.vertex

theorem neighbor_mem_remainder : l.neighbor ∈ l.remainder :=
  Finset.mem_erase.2 ⟨l.different.symm, l.neighbor_mem⟩

theorem remainder_nonempty : l.remainder.Nonempty := ⟨_, l.neighbor_mem_remainder⟩

theorem remainder_subset : l.remainder ⊆ U := Finset.erase_subset _ _

theorem remainder_card : l.remainder.card + 1 = U.card :=
  Finset.card_erase_add_one l.vertex_mem

theorem remainder_union : l.remainder ∪ {l.vertex} = U := by
  ext z
  simp only [remainder, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact h.symm ▸ l.vertex_mem
  · intro hz
    by_cases h : z = l.vertex
    · exact Or.inr h
    · exact Or.inl ⟨h, hz⟩

theorem split_cut : crossSize G l.remainder {l.vertex} = 1 := by
  rw [crossSize_comm]
  change (crossing G {l.vertex} (U.erase l.vertex)).card = 1
  rw [crossing_singleton_erase G U l.vertex l.vertex_mem]
  exact l.inside_degree

/-- Move the deleted leaf onto the same side as its unique neighbor. -/
def liftShore (A : Finset G.Vertex) : Finset G.Vertex :=
  if l.neighbor ∈ A then insert l.vertex A else A

theorem liftShore_subset {A : Finset G.Vertex} (hA : A ⊆ l.remainder) :
    l.liftShore A ⊆ U := by
  intro z hz
  by_cases hn : l.neighbor ∈ A
  · simp only [liftShore, if_pos hn, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact l.vertex_mem
    · exact l.remainder_subset (hA hz)
  · exact l.remainder_subset (hA (by simpa [liftShore, hn] using hz))

theorem subset_liftShore (A : Finset G.Vertex) : A ⊆ l.liftShore A := by
  by_cases hn : l.neighbor ∈ A
  · simp only [liftShore, if_pos hn]; exact Finset.subset_insert _ _
  · simp only [liftShore, if_neg hn]; exact Finset.Subset.refl _

theorem complement_subset_liftShore (A : Finset G.Vertex) :
    l.remainder \ A ⊆ U \ l.liftShore A := by
  intro z hz
  obtain ⟨hzR, hzA⟩ := Finset.mem_sdiff.1 hz
  obtain ⟨hzv, hzU⟩ := Finset.mem_erase.1 hzR
  refine Finset.mem_sdiff.2 ⟨hzU, ?_⟩
  by_cases hn : l.neighbor ∈ A <;> simp [liftShore, hn, hzA, hzv]

/-- No cycle-space or quotient labels: the extended cut has exactly the same
original edge labels as the cut in the leaf-deleted region. -/
theorem lifted_cut {A : Finset G.Vertex} (hA : A ⊆ l.remainder) :
    relativeCut G U (l.liftShore A) = relativeCut G l.remainder A := by
  have hvA : l.vertex ∉ A := fun h => (Finset.mem_erase.1 (hA h)).1 rfl
  have hrem_ne (z : G.Vertex) (hz : z ≠ l.vertex) :
      z ∈ l.remainder ↔ z ∈ U := by
    simp [remainder, Finset.mem_erase, hz]
  have hlift_ne (z : G.Vertex) (hz : z ≠ l.vertex) :
      z ∈ l.liftShore A ↔ z ∈ A := by
    by_cases hn : l.neighbor ∈ A <;> simp [liftShore, hn, hz]
  ext e
  have hno := G.noLoops e
  by_cases sv : G.src e = l.vertex
  · by_cases dv : G.dst e = l.vertex
    · exact False.elim (hno (sv.trans dv.symm))
    · by_cases du : G.dst e ∈ U
      · have hdN : G.dst e = l.neighbor :=
          l.unique_neighbor _ du ⟨e, one_ne_zero, Or.inl ⟨sv, rfl⟩⟩
        by_cases hn : l.neighbor ∈ A <;>
          simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            du, hn, hvA, hdN, l.vertex_mem]
      · have hdnotA : G.dst e ∉ A := by
          intro hda
          exact du (l.remainder_subset (hA hda))
        by_cases hn : l.neighbor ∈ A
        · simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            du, hn, hvA, l.vertex_mem, hdnotA]
        · simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            du, hn, hvA, l.vertex_mem, hdnotA]
  · by_cases dv : G.dst e = l.vertex
    · by_cases su : G.src e ∈ U
      · have hsN : G.src e = l.neighbor :=
          l.unique_neighbor _ su ⟨e, one_ne_zero, Or.inr ⟨rfl, dv⟩⟩
        by_cases hn : l.neighbor ∈ A <;>
          simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            su, hn, hvA, hsN, l.vertex_mem]
      · have hsnotA : G.src e ∉ A := by
          intro hsa
          exact su (l.remainder_subset (hA hsa))
        by_cases hn : l.neighbor ∈ A
        · simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            su, hn, hvA, l.vertex_mem, hsnotA]
        · simp [relativeCut, mem_crossing, remainder, liftShore, sv, dv,
            su, hn, hvA, l.vertex_mem, hsnotA]
    · have hsrcV : G.src e ≠ l.vertex := sv
      have hdstV : G.dst e ≠ l.vertex := by simpa using dv
      have hsrcL := hlift_ne (G.src e) hsrcV
      have hdstL := hlift_ne (G.dst e) hdstV
      have hsrcR := hrem_ne (G.src e) hsrcV
      have hdstR := hrem_ne (G.dst e) hdstV
      simp only [relativeCut, mem_crossing, Finset.mem_sdiff]
      rw [hsrcL, hdstL, hsrcR, hdstR]

/-- Connectivity survives, proved by lifting each nontrivial shore cut. -/
theorem connected_remainder (hU : ConnectedRegion G U) : ConnectedRegion G l.remainder := by
  apply (connectedRegion_iff_cuts G _).2
  refine ⟨l.remainder_nonempty, ?_⟩
  intro A hA hAn hBn
  have ha : (l.liftShore A).Nonempty := hAn.mono (l.subset_liftShore A)
  have hb : (U \ l.liftShore A).Nonempty := hBn.mono (l.complement_subset_liftShore A)
  have hc := ((connectedRegion_iff_cuts G U).1 hU).2
    (l.liftShore A) (l.liftShore_subset hA) ha hb
  change (relativeCut G U (l.liftShore A)).Nonempty at hc
  rw [l.lifted_cut hA] at hc
  exact hc

/-- Every cut is lifted without cost and with both sides only growing. -/
theorem expansion_remainder {h : ℝ} (hh : 0 ≤ h) (hU : HasExpansion G U h) :
    HasExpansion G l.remainder h := by
  intro A hA
  have hb := hU (l.liftShore A) (l.liftShore_subset hA)
  have haSize := Finset.card_le_card (l.subset_liftShore A)
  have hbSize := Finset.card_le_card (l.complement_subset_liftShore A)
  have hmin : min A.card (l.remainder \ A).card ≤
      min (l.liftShore A).card (U \ l.liftShore A).card := min_le_min haSize hbSize
  have hcast : ((min A.card (l.remainder \ A).card : ℕ) : ℝ) ≤
      (min (l.liftShore A).card (U \ l.liftShore A).card : ℕ) := by exact_mod_cast hmin
  have heq : relativeCutSize G U (l.liftShore A) = relativeCutSize G l.remainder A :=
    congrArg Finset.card (l.lifted_cut hA)
  rw [heq] at hb
  exact (mul_le_mul_of_nonneg_left hcast hh).trans hb

/-- Each removed leaf reduces ORIGINAL cubic deficit by exactly one. -/
theorem cut_remainder (hc : G.degree l.vertex = 3) :
    cutSize G l.remainder + 1 = cutSize G U := by
  have hd : Disjoint l.remainder {l.vertex} := by
    apply Finset.disjoint_left.2
    intro z hz h
    have he : z = l.vertex := by simpa using h
    exact (Finset.mem_erase.1 hz).1 he
  have hs := cutSize_union G l.remainder {l.vertex} hd
  rw [l.remainder_union, l.split_cut, singleton_cutSize G, hc] at hs
  omega

/-- The deleted vertex has an old exterior contact. Moving it outside can
merge original components, but cannot create an extra component. -/
theorem exterior_remainder (hU : ConnectedRegion G U) (hc : G.degree l.vertex = 3) :
    exteriorCount G l.remainder ≤ exteriorCount G U := by
  let s : BondSplit G U := {
    left := l.remainder
    right := {l.vertex}
    disjoint := by
      apply Finset.disjoint_left.2
      intro z hz h
      have he : z = l.vertex := by simpa using h
      exact (Finset.mem_erase.1 hz).1 he
    union_eq := l.remainder_union
    left_connected := l.connected_remainder hU
    right_connected := connectedRegion_singleton G _ }
  apply exteriorCount_left_le_of_touch G s
  by_contra hn
  have hzero := Finset.not_nonempty_iff_eq_empty.1 hn
  have hnoc := (no_touch_iff_no_original_contact G).1 hzero
  have hcut := child_cut_eq_cross_of_no_outside G s.left s.right s.disjoint
    (by simpa only [s.union_eq] using hnoc)
  have hsplit : crossSize G s.left s.right = 1 := l.split_cut
  have hsingle : cutSize G s.right = 3 := by
    change cutSize G {l.vertex} = 3
    rw [singleton_cutSize G, hc]
  omega

end LeafWitness

/-- Internal-degree monotonicity uses subsets of the same physical edge set. -/
theorem insideDegree_mono {A U : Finset G.Vertex} (hAU : A ⊆ U) (v : G.Vertex) :
    G.traceInsideDegree A v ≤ G.traceInsideDegree U v := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨_, hi, hs, ht⟩ := Finset.mem_filter.1 he
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hi, hAU hs, hAU ht⟩

def MinTwo (U : Finset G.Vertex) : Prop := ∀ v ∈ U, 2 ≤ G.traceInsideDegree U v

/-- Every min-degree-two subregion survives an actual leaf deletion. -/
theorem minTwo_avoids_leaf {U A : Finset G.Vertex} (l : LeafWitness G U)
    (hA : MinTwo G A) (hAU : A ⊆ U) : A ⊆ l.remainder := by
  intro v hv
  refine Finset.mem_erase.2 ⟨?_, hAU hv⟩
  intro he
  have hi := insideDegree_mono G hAU l.vertex
  have ha := hA l.vertex (he ▸ hv)
  rw [l.inside_degree] at hi
  omega

/-- Low ORIGINAL cut prevents the singleton/isolated-vertex stopping case. -/
theorem exists_leaf_of_not_minTwo {U : Finset G.Vertex}
    (hc : ∀ v ∈ U, G.degree v = 3) (hU : ConnectedRegion G U)
    (hcut : cutSize G U < U.card) (hm : ¬ MinTwo G U) :
    Nonempty (LeafWitness G U) := by
  have hm' : ∃ v ∈ U, G.traceInsideDegree U v < 2 := by
    unfold MinTwo at hm
    push_neg at hm
    exact hm
  obtain ⟨v, hv, hd⟩ := hm'
  have hrest : (U \ {v}).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.1 hn
    have heq : U = {v} := by
      apply Finset.Subset.antisymm
      · exact Finset.sdiff_eq_empty_iff_subset.1 hz
      · exact Finset.singleton_subset_iff.2 hv
    have hdeg := singleton_cutSize G v
    rw [heq, hdeg, hc v hv, Finset.card_singleton] at hcut
    omega
  have hcross := ((connectedRegion_iff_cuts G U).1 hU).2
    {v} (Finset.singleton_subset_iff.2 hv) (Finset.singleton_nonempty v) hrest
  have heq : U \ {v} = U.erase v := by
    ext z
    simp [Finset.mem_erase, and_comm]
  rw [heq, crossing_singleton_erase G U v hv] at hcross
  have hp : 0 < G.traceInsideDegree U v := Finset.card_pos.2 hcross
  exact leafWitness_of_insideDegree_one G hv (by omega)

end Erdos1016.SafeCore
