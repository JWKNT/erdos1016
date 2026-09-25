import Erdos1016.Graph.Multigraph.Forest
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-! Actual induced-component regions and their labelled boundary cuts.
These definitions retain loops and parallel edges in the ambient graph;
only connectivity is read from its underlying simple graph. -/
noncomputable section
namespace Erdos1016.FiniteMultiGraph.ExteriorComponents
open SimpleGraph
open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (U : Finset G.Vertex)

abbrev Inside := {v : G.Vertex // v ∈ U}
abbrev graph := G.toSimpleGraph.induce (↑U : Set G.Vertex)
abbrev Component := (graph G U).ConnectedComponent

noncomputable instance componentFintype : Fintype (Component G U) :=
  Fintype.ofSurjective (graph G U).connectedComponentMk Quot.mk_surjective

def vertices (c : Component G U) : Finset G.Vertex :=
  c.supp.toFinset.image Subtype.val

@[simp] theorem mem_vertices (c : Component G U) (v : G.Vertex) :
    v ∈ vertices G U c ↔ ∃ hv : v ∈ U, (graph G U).connectedComponentMk ⟨v, hv⟩ = c := by
  simp only [vertices, Finset.mem_image, Set.mem_toFinset,
    ConnectedComponent.mem_supp_iff]
  constructor
  · rintro ⟨⟨w, hw⟩, hc, rfl⟩
    exact ⟨hw, hc⟩
  · rintro ⟨hv, hc⟩
    exact ⟨⟨v, hv⟩, hc, rfl⟩

theorem vertices_subset (c : Component G U) : vertices G U c ⊆ U := by
  intro v hv
  exact ((mem_vertices G U c v).mp hv).choose

theorem vertices_disjoint : Pairwise (fun c d => Disjoint (vertices G U c) (vertices G U d)) := by
  intro c d hne
  apply Finset.disjoint_left.mpr
  intro v hvc hvd
  obtain ⟨hv, hc⟩ := (mem_vertices G U c v).mp hvc
  obtain ⟨hv', hd⟩ := (mem_vertices G U d v).mp hvd
  exact hne (hc.symm.trans hd)

theorem adjacent_stays (c : Component G U) {v w : G.Vertex}
    (hv : v ∈ vertices G U c) (hw : w ∈ U) (hvw : G.toSimpleGraph.Adj v w) :
    w ∈ vertices G U c := by
  obtain ⟨hvU, hc⟩ := (mem_vertices G U c v).mp hv
  apply (mem_vertices G U c w).mpr
  refine ⟨hw, ?_⟩
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj
    (show (graph G U).Adj ⟨w, hw⟩ ⟨v, hvU⟩ from hvw.symm)).trans hc

/-- A labelled edge leaving an induced component must leave the entire
 induced region. Loops and parallel labels are handled without simplification. -/
theorem cut_subset (c : Component G U) : G.cutEdges (vertices G U c) ⊆ G.cutEdges U := by
  intro e he
  have he' : (G.src e ∈ vertices G U c ∧ G.dst e ∉ vertices G U c) ∨
      (G.src e ∉ vertices G U c ∧ G.dst e ∈ vertices G U c) := by
    simpa [cutEdges] using he
  have hout {v w : G.Vertex} (hv : v ∈ vertices G U c)
      (hw : w ∉ vertices G U c)
      (hedge : (G.src e = v ∧ G.dst e = w) ∨ (G.src e = w ∧ G.dst e = v)) : w ∉ U := by
    intro hwU
    apply hw
    apply adjacent_stays G U c hv hwU
    exact ⟨fun heq => hw (heq ▸ hv), e, hedge⟩
  rcases he' with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have htU := hout hs ht (Or.inl ⟨rfl, rfl⟩)
    simp [cutEdges, vertices_subset G U c hs, htU]
  · have hsU := hout ht hs (Or.inr ⟨rfl, rfl⟩)
    simp [cutEdges, vertices_subset G U c ht, hsU]

/-- The boundary cuts of different induced components have disjoint edge
 labels. An edge between the components would connect them. -/
theorem cuts_disjoint : Pairwise (fun c d =>
    Disjoint (G.cutEdges (vertices G U c)) (G.cutEdges (vertices G U d))) := by
  intro c d hne
  apply Finset.disjoint_left.mpr
  intro e hc hd
  have hc' : (G.src e ∈ vertices G U c ∧ G.dst e ∉ vertices G U c) ∨
      (G.src e ∉ vertices G U c ∧ G.dst e ∈ vertices G U c) := by simpa [cutEdges] using hc
  have hd' : (G.src e ∈ vertices G U d ∧ G.dst e ∉ vertices G U d) ∨
      (G.src e ∉ vertices G U d ∧ G.dst e ∈ vertices G U d) := by simpa [cutEdges] using hd
  have hU : (G.src e ∈ U ∧ G.dst e ∉ U) ∨ (G.src e ∉ U ∧ G.dst e ∈ U) := by
    simpa [cutEdges] using cut_subset G U c hc
  have hdis := Finset.disjoint_left.mp (vertices_disjoint G U hne)
  rcases hc' with hc' | hc' <;> rcases hd' with hd' | hd'
  · exact hdis hc'.1 hd'.1
  · rcases hU with hU | hU
    · exact hU.2 (vertices_subset G U d hd'.2)
    · exact hU.1 (vertices_subset G U c hc'.1)
  · rcases hU with hU | hU
    · exact hU.2 (vertices_subset G U c hc'.2)
    · exact hU.1 (vertices_subset G U d hd'.1)
  · exact hdis hc'.2 hd'.2

/-- Every component cut is charged to a distinct physical edge of the
 whole region's cut. -/
theorem sum_cut_card_le :
    (∑ c : Component G U, (G.cutEdges (vertices G U c)).card) ≤ (G.cutEdges U).card := by
  classical
  have hpair : (↑(Finset.univ : Finset (Component G U)) : Set (Component G U)).PairwiseDisjoint
      (fun c => G.cutEdges (vertices G U c)) := by
    intro c hc d hd hne
    exact cuts_disjoint G U hne
  rw [← Finset.card_biUnion hpair]
  apply Finset.card_le_card
  intro e he
  obtain ⟨c, hc, hec⟩ := Finset.mem_biUnion.mp he
  exact cut_subset G U c hec

/-- Each represented component is genuinely connected after returning
 to the ambient vertex labels. -/
theorem vertices_connected (c : Component G U) :
    (G.toSimpleGraph.induce (↑(vertices G U c) : Set G.Vertex)).Connected := by
  let H := (graph G U).induce c.supp
  let K := G.toSimpleGraph.induce (↑(vertices G U c) : Set G.Vertex)
  let f : H →g K := {
    toFun := fun v => ⟨v.1.1, (mem_vertices G U c v.1.1).mpr
      ⟨v.1.2, (ConnectedComponent.mem_supp_iff c v.1).mp v.2⟩⟩
    map_rel' := by intro a b h; exact h }
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨hv, hc⟩ := (mem_vertices G U c v.1).mp v.2
    exact ⟨⟨⟨v.1, hv⟩, (ConnectedComponent.mem_supp_iff c ⟨v.1, hv⟩).mpr hc⟩, Subtype.ext rfl⟩
  exact c.connected_induce_supp.map f hsurj

/-- A component touching a marked set contains an actual marked vertex. -/
def Touches (P : Finset G.Vertex) (c : Component G U) : Prop :=
  ∃ v ∈ P, v ∈ vertices G U c

abbrev TouchedComponent (P : Finset G.Vertex) := {c : Component G U // Touches G U P c}

/-- Marked connected components cannot split when embedded into the larger
 induced region. Thus the number of exterior components touching P is
 bounded by the actual number of induced marked components. -/
theorem touched_component_card_le (P : Finset G.Vertex) (hPU : P ⊆ U) :
    Fintype.card (TouchedComponent G U P) ≤ Fintype.card (Component G P) := by
  classical
  choose point hpointP hpointV using fun c : TouchedComponent G U P => c.2
  let f : TouchedComponent G U P → Component G P :=
    fun c => (graph G P).connectedComponentMk ⟨point c, hpointP c⟩
  let inc : graph G P →g graph G U :=
    (SimpleGraph.induceHomOfLE (G := G.toSimpleGraph)
      (show (↑P : Set G.Vertex) ⊆ ↑U from hPU)).toHom
  have hcomp (c : TouchedComponent G U P) :
      (graph G U).connectedComponentMk ⟨point c, hPU (hpointP c)⟩ = c.1 := by
    obtain ⟨hv, hc⟩ := (mem_vertices G U c.1 (point c)).mp (hpointV c)
    exact hc
  apply Fintype.card_le_of_injective f
  intro c d heq
  apply Subtype.ext
  have hmap := congrArg (fun k : Component G P => k.map inc) heq
  change (graph G U).connectedComponentMk ⟨point c, hPU (hpointP c)⟩ =
    (graph G U).connectedComponentMk ⟨point d, hPU (hpointP d)⟩ at hmap
  exact (hcomp c).symm.trans (hmap.trans (hcomp d))

/-- Large cuts consume disjoint physical boundary labels. The t+1
 denominator records that a large component has cut strictly greater than t. -/
theorem large_cut_card_mul_le (t : ℕ) :
    (Finset.univ.filter (fun c : Component G U =>
      t < (G.cutEdges (vertices G U c)).card)).card * (t + 1) ≤ (G.cutEdges U).card := by
  let S := Finset.univ.filter (fun c : Component G U =>
    t < (G.cutEdges (vertices G U c)).card)
  calc
    S.card * (t + 1) = ∑ c ∈ S, (t + 1) := by simp
    _ ≤ ∑ c ∈ S, (G.cutEdges (vertices G U c)).card :=
      Finset.sum_le_sum (fun c hc => Nat.succ_le_of_lt (Finset.mem_filter.mp hc).2)
    _ ≤ ∑ c : Component G U, (G.cutEdges (vertices G U c)).card :=
      Finset.sum_le_univ_sum_of_nonneg (fun c => Nat.zero_le _)
    _ ≤ _ := sum_cut_card_le G U

end Erdos1016.FiniteMultiGraph.ExteriorComponents
