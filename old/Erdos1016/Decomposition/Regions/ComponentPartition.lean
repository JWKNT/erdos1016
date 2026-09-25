import Erdos1016.Decomposition.Regions.MarkedVertexRegion
import Erdos1016.Cycles.Geometry.Supports

set_option autoImplicit false

/-!
# Components in one unchanged physical owner

Finite component sets are those of `SafeCore.Regions`. In particular all
boundaries below still refer to the original owner. These lemmas supply the
component partition, contact, and cardinality arguments used in §§3--4 of
ANALYTIC_CUBIC_INVERSE_PROOF.md.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay
local instance cycleSupplyComponentToolsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

theorem connected_univ (hG : G.IsConnected) : ConnectedRegion G Finset.univ := by
  change G.toSimpleGraph.Connected at hG
  refine ⟨?_, ?_⟩
  · obtain ⟨v⟩ := hG.nonempty
    exact ⟨v, Finset.mem_univ _⟩
  · intro u _ v _
    obtain ⟨p⟩ := hG u v
    induction p with
    | nil => exact .refl _ (Finset.mem_univ _)
    | @cons u v w huv p ih =>
        exact (InReach.edge (Finset.mem_univ _) (Finset.mem_univ _) huv).trans
          (ih (Finset.mem_univ _) (Finset.mem_univ _))

/-- A connected set cannot straddle two actual components. -/
theorem connected_subset_component {U T C : Finset G.Vertex}
    (hT : ConnectedRegion G T) (hTU : T ⊆ U)
    (hC : C ∈ components G U) {u : G.Vertex} (huT : u ∈ T) (huC : u ∈ C) :
    T ⊆ C := by
  intro v hv
  exact (((hT.2 u huT v hv).mono hTU).restrict huC (component_closed G hC)).target

theorem connected_subset_some_component {U T : Finset G.Vertex}
    (hT : ConnectedRegion G T) (hTU : T ⊆ U) :
    ∃ C ∈ components G U, T ⊆ C := by
  obtain ⟨u, hu⟩ := hT.1
  obtain ⟨C, hC, huC⟩ := components_cover G (hTU hu)
  exact ⟨C, hC, connected_subset_component G hT hTU hC hu huC⟩

theorem connected_subset_or_disjoint_component {U T C : Finset G.Vertex}
    (hT : ConnectedRegion G T) (hTU : T ⊆ U)
    (hC : C ∈ components G U) : T ⊆ C ∨ Disjoint T C := by
  by_cases hd : Disjoint T C
  · exact Or.inr hd
  · left
    have hx : ∃ u, u ∈ T ∧ u ∈ C := by
      by_contra h
      push_neg at h
      exact hd (Finset.disjoint_left.2 h)
    obtain ⟨u, huT, huC⟩ := hx
    exact connected_subset_component G hT hTU hC huT huC

/-- Removing other components does not change this component. -/
theorem component_in_smaller_ambient {U V C : Finset G.Vertex}
    (hC : C ∈ components G U) (hCV : C ⊆ V) (hVU : V ⊆ U) :
    C ∈ components G V := by
  apply (mem_components G V C).2
  exact ⟨hCV, component_connected G hC,
    fun u hu v hv huv => component_closed G hC u hu v (hVU hv) huv⟩

/-- A component remains one after restoration of vertices to which it has
no physical edge. -/
theorem component_in_larger_ambient {U V C : Finset G.Vertex}
    (hC : C ∈ components G V) (hVU : V ⊆ U)
    (hno : crossing G C (U \ V) = ∅) : C ∈ components G U := by
  apply (mem_components G U C).2
  refine ⟨(component_subset G hC).trans hVU, component_connected G hC, ?_⟩
  intro u hu v hv huv
  by_cases hvV : v ∈ V
  · exact component_closed G hC u hu v hvV huv
  · have hne := (crossing_nonempty_iff G C (U \ V)).2
      ⟨u, hu, v, Finset.mem_sdiff.2 ⟨hv, hvV⟩, huv⟩
    simpa only [hno, Finset.not_nonempty_empty] using hne

/-- In a connected ambient region every component left by a nonempty
removed set touches that set. -/
theorem component_touches_separator {U S C : Finset G.Vertex}
    (hU : ConnectedRegion G U) (hSU : S ⊆ U) (hSne : S.Nonempty)
    (hC : C ∈ components G (U \ S)) : (crossing G C S).Nonempty := by
  have hCU : C ⊆ U := (component_subset G hC).trans Finset.sdiff_subset
  have hrest : (U \ C).Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    refine ⟨s, Finset.mem_sdiff.2 ⟨hSU hs, ?_⟩⟩
    intro hsC
    exact (Finset.mem_sdiff.1 (component_subset G hC hsC)).2 hs
  obtain ⟨u, hu, v, hv, huv⟩ := (crossing_nonempty_iff G C (U \ C)).1
    (((connectedRegion_iff_cuts G U).1 hU).2 C hCU
      (component_connected G hC).1 hrest)
  have hvS : v ∈ S := by
    by_contra hvS
    exact (Finset.mem_sdiff.1 hv).2
      (component_closed G hC u hu v
        (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hv).1, hvS⟩) huv)
  exact (crossing_nonempty_iff G C S).2 ⟨u, hu, v, hvS, huv⟩

/-- Components other than the one containing the designated root. -/
def offRootComponents (U : Finset G.Vertex) (w : G.Vertex) :
    Finset (Finset G.Vertex) := (components G U).filter fun C => w ∉ C

@[simp] theorem mem_offRootComponents (U C : Finset G.Vertex) (w : G.Vertex) :
    C ∈ offRootComponents G U w ↔ C ∈ components G U ∧ w ∉ C := by
  simp only [offRootComponents, Finset.mem_filter]

def offRootVertices (U : Finset G.Vertex) (w : G.Vertex) : Finset G.Vertex :=
  (offRootComponents G U w).biUnion id

/-- The root component is identified by its original vertices. -/
theorem root_component_mem {U : Finset G.Vertex} {w : G.Vertex} (hw : w ∈ U) :
    reachSet G U w ∈ components G U :=
  (mem_components G U _).2 (reachSet_isComponent G hw)

theorem component_root_iff {U C : Finset G.Vertex} {w : G.Vertex}
    (hC : C ∈ components G U) (hw : w ∈ U) :
    w ∈ C ↔ C = reachSet G U w := by
  constructor
  · exact component_eq_reachSet G ((mem_components G U C).1 hC)
  · intro h
    rw [h]
    exact self_mem_reachSet G hw

theorem offRootComponents_eq_erase {U : Finset G.Vertex} {w : G.Vertex}
    (hw : w ∈ U) :
    offRootComponents G U w = (components G U).erase (reachSet G U w) := by
  ext C
  simp only [mem_offRootComponents, Finset.mem_erase]
  constructor
  · rintro ⟨hC, hn⟩
    exact ⟨fun h => hn ((component_root_iff G hC hw).2 h), hC⟩
  · rintro ⟨hne, hC⟩
    exact ⟨hC, fun h => hne ((component_root_iff G hC hw).1 h)⟩

theorem offRootComponents_card_add_one {U : Finset G.Vertex} {w : G.Vertex}
    (hw : w ∈ U) : (offRootComponents G U w).card + 1 = componentCount G U := by
  rw [offRootComponents_eq_erase G hw]
  exact Finset.card_erase_add_one (root_component_mem G hw)

theorem offRootVertices_eq_sdiff {U : Finset G.Vertex} {w : G.Vertex}
    (hw : w ∈ U) : offRootVertices G U w = U \ reachSet G U w := by
  ext v
  constructor
  · intro hv
    obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨hC, hwC⟩ := (mem_offRootComponents G U C w).1 hC
    refine Finset.mem_sdiff.2 ⟨component_subset G hC hvC, ?_⟩
    intro hvr
    have heq := components_eq_of_mem G hC (root_component_mem G hw) hvC hvr
    exact hwC ((component_root_iff G hC hw).2 heq)
  · rintro hv
    obtain ⟨hvU, hvn⟩ := Finset.mem_sdiff.1 hv
    obtain ⟨C, hC, hvC⟩ := components_cover G hvU
    have hwn : w ∉ C := by
      intro hwC
      exact hvn ((component_eq_reachSet G ((mem_components G U C).1 hC) hwC) ▸ hvC)
    exact Finset.mem_biUnion.2
      ⟨C, (mem_offRootComponents G U C w).2 ⟨hC, hwn⟩, hvC⟩

theorem connected_subset_root_or_offRoot {U T : Finset G.Vertex} {w : G.Vertex}
    (hw : w ∈ U) (hT : ConnectedRegion G T) (hTU : T ⊆ U) :
    T ⊆ reachSet G U w ∨ T ⊆ offRootVertices G U w := by
  rcases connected_subset_or_disjoint_component G hT hTU (root_component_mem G hw) with h | h
  · exact Or.inl h
  · right
    rw [offRootVertices_eq_sdiff G hw]
    intro v hv
    exact Finset.mem_sdiff.2 ⟨hTU hv, fun hvr => Finset.disjoint_left.1 h hv hvr⟩

/-- Cardinalities of disjoint actual component sets add exactly. -/
theorem component_subfamily_card_sum (U : Finset G.Vertex)
    (F : Finset (Finset G.Vertex)) (hF : F ⊆ components G U) :
    (F.biUnion id).card = ∑ C ∈ F, C.card := by
  apply Finset.card_biUnion
  intro C hC D hD hne
  exact components_disjoint G (hF hC) (hF hD) hne



/-- Exact original boundary of a full complementary component. -/
theorem component_ownerCut_eq {S C : Finset G.Vertex}
    (hC : C ∈ components G Sᶜ) : ownerCut G C = crossing G C S := by
  ext e
  constructor
  · intro he
    rcases (mem_ownerCut G C e).1 he with h | h
    · have hd : G.dst e ∈ S := by
        by_contra hn
        exact h.2 (component_closed G hC _ h.1 _ (Finset.mem_compl.2 hn)
          ⟨e, one_ne_zero, Or.inl ⟨rfl, rfl⟩⟩)
      exact (mem_crossing G C S e).2 (Or.inl ⟨h.1, hd⟩)
    · have hs : G.src e ∈ S := by
        by_contra hn
        exact h.1 (component_closed G hC _ h.2 _ (Finset.mem_compl.2 hn)
          ⟨e, one_ne_zero, Or.inr ⟨rfl, rfl⟩⟩)
      exact (mem_crossing G C S e).2 (Or.inr ⟨hs, h.2⟩)
  · intro he
    rcases (mem_crossing G C S e).1 he with h | h
    · exact (mem_ownerCut G C e).2 (Or.inl ⟨h.1, fun hd =>
        (Finset.mem_compl.1 (component_subset G hC hd)) h.2⟩)
    · exact (mem_ownerCut G C e).2 (Or.inr ⟨fun hs =>
        (Finset.mem_compl.1 (component_subset G hC hs)) h.1, h.2⟩)

theorem component_cuts_disjoint {S C D : Finset G.Vertex}
    (hC : C ∈ components G Sᶜ) (hD : D ∈ components G Sᶜ) (hne : C ≠ D) :
    Disjoint (ownerCut G C) (ownerCut G D) := by
  rw [component_ownerCut_eq G hC, component_ownerCut_eq G hD]
  apply Finset.disjoint_left.2
  intro e heC heD
  have hd := Finset.disjoint_left.1 (components_disjoint G hC hD hne)
  rcases (mem_crossing G C S e).1 heC with hc | hc <;>
    rcases (mem_crossing G D S e).1 heD with hd' | hd'
  · exact hd hc.1 hd'.1
  · exact (Finset.mem_compl.1 (component_subset G hC hc.1)) hd'.1
  · exact (Finset.mem_compl.1 (component_subset G hD hd'.1)) hc.1
  · exact hd hc.2 hd'.2

theorem component_subfamily_cut_sum_le (S : Finset G.Vertex)
    (F : Finset (Finset G.Vertex)) (hF : F ⊆ components G Sᶜ) :
    (∑ C ∈ F, cutSize G C) ≤ cutSize G S := by
  have hdis : (↑F : Set (Finset G.Vertex)).PairwiseDisjoint (ownerCut G) := by
    intro C hC D hD hne
    exact component_cuts_disjoint G (hF hC) (hF hD) hne
  have hsub : F.biUnion (ownerCut G) ⊆ ownerCut G S := by
    intro e he
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.1 he
    rw [component_ownerCut_eq G (hF hC)] at heC
    have he' := crossing_mono G (component_subset G (hF hC)) (Finset.Subset.refl S) heC
    simpa only [ownerCut, crossing_comm G Sᶜ S] using he'
  calc
    (∑ C ∈ F, cutSize G C) = (F.biUnion (ownerCut G)).card := by
      symm
      exact Finset.card_biUnion hdis
    _ ≤ cutSize G S := Finset.card_le_card hsub

/-- Actual vertices adjacent to a removed set, counted once each. -/
def outsideNeighbors (S : Finset G.Vertex) : Finset G.Vertex :=
  Sᶜ.filter fun v => ∃ u ∈ S, G.toSimpleGraph.Adj u v

@[simp] theorem mem_outsideNeighbors (S : Finset G.Vertex) (v : G.Vertex) :
    v ∈ outsideNeighbors G S ↔ v ∉ S ∧ ∃ u ∈ S, G.toSimpleGraph.Adj u v := by
  simp [outsideNeighbors]

private def outerEnd (S : Finset G.Vertex) (e : G.Edge) : G.Vertex :=
  if G.src e ∈ S then G.dst e else G.src e

theorem outsideNeighbors_card_le (S : Finset G.Vertex) :
    (outsideNeighbors G S).card ≤ cutSize G S := by
  have hsub : outsideNeighbors G S ⊆ (ownerCut G S).image (outerEnd G S) := by
    intro v hv
    obtain ⟨hvn, u, hu, e, _, he | he⟩ := (mem_outsideNeighbors G S v).1 hv
    · have hs : G.src e ∈ S := he.1.symm ▸ hu
      have hd : G.dst e ∉ S := he.2.symm ▸ hvn
      exact Finset.mem_image.2 ⟨e, (mem_ownerCut G S e).2 (Or.inl ⟨hs, hd⟩),
        by simp [outerEnd, hs, he.2]⟩
    · have hs : G.src e ∉ S := he.1.symm ▸ hvn
      have hd : G.dst e ∈ S := he.2.symm ▸ hu
      exact Finset.mem_image.2 ⟨e, (mem_ownerCut G S e).2 (Or.inr ⟨hs, hd⟩),
        by
          change outerEnd G S e = v
          change (if G.src e ∈ S then G.dst e else G.src e) = v
          rw [if_neg hs]
          exact he.1⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Distinct disjoint supports meeting a set consume distinct vertices of it. -/
theorem disjoint_meeting_card_le {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (S : ι → Finset G.Vertex) (A : Finset G.Vertex)
    (hdis : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hmeet : ∀ i ∈ F, ∃ v ∈ S i, v ∈ A) : F.card ≤ A.card := by
  let pick (i : {i // i ∈ F}) : G.Vertex := Classical.choose (hmeet i.1 i.2)
  have hp (i : {i // i ∈ F}) : pick i ∈ S i.1 ∧ pick i ∈ A :=
    Classical.choose_spec (hmeet i.1 i.2)
  let f (i : {i // i ∈ F}) : {v // v ∈ A} := ⟨pick i, (hp i).2⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    have hval : pick i = pick j := by
      simpa [f] using congrArg Subtype.val he
    exact Finset.disjoint_left.1 (hdis i.1 i.2 j.1 j.2 hn)
      (hp i).1 (hval.symm ▸ (hp j).1)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

end Erdos1016.CycleSupply
