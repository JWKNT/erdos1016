import Erdos1016.Decomposition.TwoCore.InducedDeficit
import Erdos1016.Cycles.Geometry.ContactGraph
import Erdos1016.Probability.Conditional.CycleFactorization
import Erdos1016.Nonbacktracking.Girth.InducedBoundaryContacts

set_option autoImplicit false

/-!
# Boundary geometry before shrinking complementary components

The contact graph makes the retained-cycle return exclusion usable before
we know the component is small enough to be a tree. Boundary tokens here
are the actual physical cut edges, so their number is exactly the cut size.
-/

noncomputable section

namespace Erdos1016.Proof.ConditionalComplementGeometry

open Erdos1016.SafeCore Erdos1016.BoundaryDecay
open Erdos1016.Proof.ConditionalContactGraph
open Erdos1016.Proof.ConditionalMoments
open Erdos1016.Proof.BreadthFirstLayers
open Erdos1016.Proof.InducedBoundaryContacts

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The endpoint of a physical boundary edge inside the region. -/
def boundaryBase (G : PhysicalGraph) (R : Finset G.Vertex)
    (e : ownerCut G R) : R :=
  if h : G.src e.1 ∈ R then ⟨G.src e.1, h⟩
  else ⟨G.dst e.1, by
    rcases (mem_ownerCut G R e.1).mp e.2 with h' | h'
    · exact (h h'.1).elim
    · exact h'.2⟩

/-- The endpoint outside the region of a physical boundary edge. -/
def boundaryTip (G : PhysicalGraph) (R : Finset G.Vertex)
    (e : ownerCut G R) : G.Vertex :=
  if G.src e.1 ∈ R then G.dst e.1 else G.src e.1

theorem boundary_endpoints (G : PhysicalGraph) (R : Finset G.Vertex)
    (e : ownerCut G R) :
    (G.src e.1 = (boundaryBase G R e).1 ∧ G.dst e.1 = boundaryTip G R e) ∨
    (G.src e.1 = boundaryTip G R e ∧ G.dst e.1 = (boundaryBase G R e).1) := by
  by_cases h : G.src e.1 ∈ R <;> simp [boundaryBase, boundaryTip, h]

theorem boundaryTip_not_mem (G : PhysicalGraph) (R : Finset G.Vertex)
    (e : ownerCut G R) : boundaryTip G R e ∉ R := by
  rcases (mem_ownerCut G R e.1).mp e.2 with h | h
  · simpa [boundaryTip, h.1] using h.2
  · simp [boundaryTip, h.1]

theorem boundary_adj (G : PhysicalGraph) (R : Finset G.Vertex)
    (e : ownerCut G R) :
    G.toSimpleGraph.Adj (boundaryBase G R e).1 (boundaryTip G R e) :=
  ⟨e.1, one_ne_zero, boundary_endpoints G R e⟩

theorem exists_boundary_at_neighbor (G : PhysicalGraph) (R : Finset G.Vertex)
    (v : R) (w : G.Vertex) (hvw : G.toSimpleGraph.Adj v.1 w) (hw : w ∉ R) :
    ∃ e : ownerCut G R, boundaryBase G R e = v ∧ boundaryTip G R e = w := by
  obtain ⟨e, _, he | he⟩ := hvw
  · have hecut : e ∈ ownerCut G R := (mem_ownerCut G R e).mpr
      (Or.inl ⟨he.1 ▸ v.2, he.2 ▸ hw⟩)
    refine ⟨⟨e, hecut⟩, ?_, ?_⟩
    · apply Subtype.ext
      simp [boundaryBase, he.1, v.2]
    · simp [boundaryTip, he.1, he.2, v.2]
  · have hecut : e ∈ ownerCut G R := (mem_ownerCut G R e).mpr
      (Or.inr ⟨he.1 ▸ hw, he.2 ▸ v.2⟩)
    refine ⟨⟨e, hecut⟩, ?_, ?_⟩
    · apply Subtype.ext
      simp [boundaryBase, he.1, he.2, hw]
    · simp [boundaryTip, he.1, hw]

private theorem exists_pos_of_sum_pos {α : Type*} (s : Finset α) (f : α → ℝ)
    (h : 0 < ∑ a ∈ s, f a) : ∃ a ∈ s, 0 < f a := by
  by_contra hnone
  push_neg at hnone
  have := Finset.sum_nonpos hnone
  linarith

/-- Cubic girth growth forces an actual outgoing incidence within distance
`r` of every vertex of a region with fewer than `2^r` vertices. -/
theorem boundary_radius_cover (G : PhysicalGraph) (R : Finset G.Vertex)
    (hreg : ∀ v ∈ R, G.degree v = 3)
    (hconn : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (D r : ℕ) (hno : Erdos1016.CycleSupply.NoShortCycles G R D)
    (hD : 2 * r + 1 ≤ D) (hsmall : (R.card : ℝ) < 2 ^ r) :
    ∀ v : R, ∃ e : ownerCut G R,
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).dist v (boundaryBase G R e) ≤ r := by
  intro root
  have hcontacts := physical_induced_target_three_contacts_of_small_order
    G R hreg hconn D r hno hD root hsmall
  have hpositive : 0 < ∑ k ∈ Finset.range r,
      ∑ v ∈ bfsLayer (G.toSimpleGraph.induce (↑R : Set G.Vertex)) root k,
        (((G.toSimpleGraph.neighborFinset v.1).filter
          (fun w => w ∉ R)).card : ℝ) := by linarith
  obtain ⟨k, hk, hpositive⟩ := exists_pos_of_sum_pos _ _ hpositive
  obtain ⟨v, hv, hpositive⟩ := exists_pos_of_sum_pos _ _ hpositive
  have hcard : 0 < ((G.toSimpleGraph.neighborFinset v.1).filter
      (fun w => w ∉ R)).card := by exact_mod_cast hpositive
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
  rcases Finset.mem_filter.mp hw with ⟨hvw, hw⟩
  obtain ⟨e, he, _⟩ := exists_boundary_at_neighbor G R v w
    (G.toSimpleGraph.mem_neighborFinset v.1 w |>.mp hvw) hw
  refine ⟨e, ?_⟩
  rw [he]
  have hd := (Finset.mem_filter.mp hv).2
  change (G.toSimpleGraph.induce (↑R : Set G.Vertex)).dist root v = k at hd
  rw [hd]
  exact (Finset.mem_range.mp hk).le

/-- A cycle supplies two distinct incidences inside its vertex support. -/
theorem cycle_traceInsideDegree_ge_two {G : PhysicalGraph}
    (C : G.CycleWord) (u : G.Vertex) (hu : u ∈ Cycle.vertices C) :
    2 ≤ G.traceInsideDegree (Cycle.vertices C) u := by
  have hsel : G.selectedDegree C.1 u = 2 := C.2.2.2.2 u hu
  have hsub : Finset.univ.filter
      (fun f : G.Edge => C.1 f ≠ 0 ∧ G.incident f u) ⊆
      G.traceInsideEdgesAt (Cycle.vertices C) u := by
    intro f hf
    rcases Finset.mem_filter.mp hf with ⟨_, hneF, hinc⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc,
      src_mem_used_of_ne_zero C.1 f hneF, dst_mem_used_of_ne_zero C.1 f hneF⟩
  calc
    2 = G.selectedDegree C.1 u := hsel.symm
    _ ≤ (G.traceInsideEdgesAt (Cycle.vertices C) u).card := Finset.card_le_card hsub

private theorem boundary_mem_cycleCut {G : PhysicalGraph}
    (R : Finset G.Vertex) (C : G.CycleWord) (e : ownerCut G R)
    (hdisj : Disjoint R (Cycle.vertices C))
    (htip : boundaryTip G R e ∈ Cycle.vertices C) :
    e.1 ∈ G.traceCutEdgesAt (Cycle.vertices C) (boundaryTip G R e) := by
  have hbase : (boundaryBase G R e).1 ∉ Cycle.vertices C :=
    fun h => Finset.disjoint_left.mp hdisj (boundaryBase G R e).2 h
  unfold PhysicalGraph.traceCutEdgesAt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, PhysicalGraph.incident]
  rcases boundary_endpoints G R e with h | h
  · exact ⟨Or.inr h.2, Or.inr ⟨h.1 ▸ hbase, h.2 ▸ htip⟩⟩
  · exact ⟨Or.inl h.1, Or.inl ⟨h.1 ▸ htip, h.2 ▸ hbase⟩⟩

/-- In a cubic graph two different incidences into a cycle have different
cycle endpoints: each cycle vertex has at most one spare incidence. -/
theorem distinct_boundary_tips {G : PhysicalGraph}
    (R : Finset G.Vertex) (C : G.CycleWord) (e d : ownerCut G R)
    (hed : e ≠ d) (hdisj : Disjoint R (Cycle.vertices C))
    (hregular : ∀ u ∈ Cycle.vertices C, G.degree u = 3)
    (he : boundaryTip G R e ∈ Cycle.vertices C)
    (hd : boundaryTip G R d ∈ Cycle.vertices C) :
    boundaryTip G R e ≠ boundaryTip G R d := by
  intro heq
  have hecut := boundary_mem_cycleCut R C e hdisj he
  have hdcut := boundary_mem_cycleCut R C d hdisj hd
  rw [← heq] at hdcut
  have hcard := G.traceCutDegree_le_one (Cycle.vertices C)
    (boundaryTip G R e) he (hregular _ he) (cycle_traceInsideDegree_ge_two C _ he)
  apply hed
  exact Subtype.ext ((Finset.card_le_one.mp hcard) _ hecut _ hdcut)

/-- A radius cover and the retained-cycle return exclusion make the cycle
labels of all physical boundary edges injective. Unlike the previous
component-order argument, this does not assume `R.card + 1 ≤ q`. -/
theorem boundary_labels_injective_of_cover
    {G : PhysicalGraph} {ι : Type*} [Fintype ι]
    (R : Finset G.Vertex) (C : ι → G.CycleWord) (r q : ℕ)
    (hconn : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (hcover : ∀ v : R, ∃ e : ownerCut G R,
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).dist v (boundaryBase G R e) ≤ r)
    (label : ownerCut G R → ι)
    (hlabel : ∀ e, boundaryTip G R e ∈ Cycle.vertices (C (label e)))
    (hdisj : ∀ i, Disjoint R (Cycle.vertices (C i)))
    (hregular : ∀ i, ∀ u ∈ Cycle.vertices (C i), G.degree u = 3)
    (hreturn : ∀ i, NoShortExternalReturnThrough G R (Cycle.vertices (C i)) q)
    (hq : Fintype.card ι * (2 * r + 1) + 2 ≤ q) :
    Function.Injective label := by
  by_contra hinj
  obtain ⟨e, d, hed, hsame, hclose⟩ := exists_close_equal_labels_of_cover
    (G.toSimpleGraph.induce (↑R : Set G.Vertex)) hconn
    (boundaryBase G R) label r hcover hinj
  have hd : boundaryTip G R d ∈ Cycle.vertices (C (label e)) := by
    rw [hsame]
    exact hlabel d
  have htips := distinct_boundary_tips R (C (label e)) e d hed
    (hdisj _) (hregular _) (hlabel e) hd
  obtain ⟨p, hp, hlen⟩ := hconn.exists_path_of_dist
    (boundaryBase G R e) (boundaryBase G R d)
  have hlong := hreturn (label e) _ _ _ _ (boundaryBase G R e).2
    (boundaryBase G R d).2 (hlabel e) hd htips
    (boundary_adj G R e) (boundary_adj G R d) p hp
  omega

/-- The actual cut has at most one edge for each retained-cycle label,
using cubic growth and the short-return filter before any tree reduction. -/
theorem cutSize_le_labels_of_small_order
    {G : PhysicalGraph} {ι : Type*} [Fintype ι]
    (R : Finset G.Vertex) (C : ι → G.CycleWord) (D r q : ℕ)
    (hreg : ∀ v ∈ R, G.degree v = 3)
    (hconn : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).Connected)
    (hno : Erdos1016.CycleSupply.NoShortCycles G R D)
    (hD : 2 * r + 1 ≤ D) (hsmall : (R.card : ℝ) < 2 ^ r)
    (label : ownerCut G R → ι)
    (hlabel : ∀ e, boundaryTip G R e ∈ Cycle.vertices (C (label e)))
    (hdisj : ∀ i, Disjoint R (Cycle.vertices (C i)))
    (hregular : ∀ i, ∀ u ∈ Cycle.vertices (C i), G.degree u = 3)
    (hreturn : ∀ i, NoShortExternalReturnThrough G R (Cycle.vertices (C i)) q)
    (hq : Fintype.card ι * (2 * r + 1) + 2 ≤ q) :
    cutSize G R ≤ Fintype.card ι := by
  have hinj := boundary_labels_injective_of_cover R C r q hconn
    (boundary_radius_cover G R hreg hconn D r hno hD hsmall)
    label hlabel hdisj hregular hreturn hq
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective label hinj

/-- Every boundary edge of a complementary component goes to a selected
cycle. This constructs the cycle labels used in the preceding theorem. -/
theorem component_cutSize_le_cycle_count
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (C : ι → G.CycleWord) (R : Finset G.Vertex) (D r q : ℕ)
    (hcomponent : R ∈ components G (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (hreg : ∀ v ∈ R, G.degree v = 3)
    (hno : Erdos1016.CycleSupply.NoShortCycles G R D)
    (hD : 2 * r + 1 ≤ D) (hsmall : (R.card : ℝ) < 2 ^ r)
    (hregular : ∀ i ∈ F, ∀ u ∈ Cycle.vertices (C i), G.degree u = 3)
    (hreturn : ∀ i ∈ F, NoShortExternalReturnThrough G R (Cycle.vertices (C i)) q)
    (hq : F.card * (2 * r + 1) + 2 ≤ q) :
    cutSize G R ≤ F.card := by
  let U := F.biUnion (fun i => Cycle.vertices (C i))
  have htip (e : ownerCut G R) : boundaryTip G R e ∈ U := by
    by_contra hout
    have hmem := component_closed G hcomponent _ (boundaryBase G R e).2
      _ (Finset.mem_compl.mpr hout) (boundary_adj G R e)
    exact boundaryTip_not_mem G R e hmem
  have hchoose : ∀ e : ownerCut G R,
      ∃ i : F, boundaryTip G R e ∈ Cycle.vertices (C i.1) := by
    intro e
    obtain ⟨i, hi, hmember⟩ := Finset.mem_biUnion.mp (htip e)
    exact ⟨⟨i, hi⟩, hmember⟩
  let label : ownerCut G R → F := fun e => Classical.choose (hchoose e)
  have hlabel : ∀ e, boundaryTip G R e ∈ Cycle.vertices (C (label e).1) :=
    fun e => Classical.choose_spec (hchoose e)
  have hdisj : ∀ i : F, Disjoint R (Cycle.vertices (C i.1)) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro v hvR hvC
    have hout := Finset.mem_compl.mp (component_subset G hcomponent hvR)
    exact hout (Finset.mem_biUnion.mpr ⟨i.1, i.2, hvC⟩)
  have hconn := (connectedRegion_iff_induce_connected G R).mp
    (component_connected G hcomponent)
  have hcut := cutSize_le_labels_of_small_order R (fun i : F => C i.1)
    D r q hreg hconn hno hD hsmall label hlabel hdisj
    (fun i => hregular i.1 i.2) (fun i => hreturn i.1 i.2)
    (by simpa only [Fintype.card_coe] using hq)
  simpa only [Fintype.card_coe] using hcut

/-- Excluding cycles through the order of the region makes it acyclic.
The girth assumption is local to this region. -/
theorem region_acyclic_of_no_short_cycles
    (G : PhysicalGraph) (R : Finset G.Vertex) (D : ℕ)
    (hcard : R.card ≤ D)
    (hno : Erdos1016.CycleSupply.NoShortCycles G R D) :
    (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic := by
  have hg := Erdos1016.Nonbacktracking.girthGreater_induce_of_noShortCycles G R D hno
  intro u p hp
  cases p with
  | nil => exact hp.ne_nil rfl
  | cons h p =>
    have htail := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hp |>.1
    have hcardInduced : Fintype.card (↑R : Set G.Vertex) = R.card :=
      Fintype.card_ofFinset R (by intro v; rfl)
    have htailLen : p.length < R.card := by simpa only [hcardInduced] using htail.length_lt
    have hgirth := hg _ (SimpleGraph.Walk.cons h p) hp
    simp only [SimpleGraph.Walk.length_cons] at hgirth
    omega

/-- The small-component conclusion of Lemma 5.1. Cubic growth first limits
the cut to one contact per selected-cycle label; the girth-deficit estimate
then shrinks the component to at most `4K`, hence to a tree. Its exact cubic
cut identity sharpens the order to `K-2`.

The explicit hypotheses are the pre-shrink order and parameter inequalities,
all independent of the asserted tree or contact conclusions. -/
theorem small_complement_component_isTree
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (C : ι → G.CycleWord) (R : Finset G.Vertex) (M budget D r q : ℕ)
    (hcomponent : R ∈ components G (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (hreg : ∀ v ∈ R, G.degree v = 3)
    (hno : Erdos1016.CycleSupply.NoShortCycles G R D)
    (hM : 2 ≤ M) (hRM : R.card ≤ M)
    (hcutBudget : cutSize G R ≤ budget)
    (hsmall : (4 * budget : ℝ) < 2 ^ r) (hD : 2 * r + 1 ≤ D)
    (hgap : (((D / 2 - 1 : ℕ) : ℝ) * (1 - 1 / ((4 : ℝ) - 1))) >
      Real.logb 2 ((M : ℝ) / 2))
    (hcardD : 4 * F.card ≤ D)
    (hregular : ∀ i ∈ F, ∀ u ∈ Cycle.vertices (C i), G.degree u = 3)
    (hreturn : ∀ i ∈ F, NoShortExternalReturnThrough G R (Cycle.vertices (C i)) q)
    (hq : F.card * (2 * r + 1) + 2 ≤ q) :
    (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsTree ∧
      R.card + 2 ≤ F.card ∧
      ∀ i ∈ F, ∀ e d,
        e ∈ crossing G R (Cycle.vertices (C i)) →
        d ∈ crossing G R (Cycle.vertices (C i)) → e = d := by
  have hg := Erdos1016.Nonbacktracking.girthGreater_induce_of_noShortCycles G R D hno
  have hshrink := Erdos1016.Proof.InducedCubicDeficit.region_order_le_constant_cutSize
    G R hreg M D hM hRM hg 4 (by norm_num) hgap
  have hRsmall : (R.card : ℝ) < 2 ^ r := by
    have hb : (cutSize G R : ℝ) ≤ budget := by exact_mod_cast hcutBudget
    nlinarith
  have hcut := component_cutSize_le_cycle_count F C R D r q hcomponent hreg hno hD
    hRsmall hregular hreturn hq
  have hshrinkNat : R.card ≤ 4 * cutSize G R := by exact_mod_cast hshrink
  have hRD : R.card ≤ D := (hshrinkNat.trans (Nat.mul_le_mul_left 4 hcut)).trans hcardD
  have hacyclic := region_acyclic_of_no_short_cycles G R D hRD hno
  have hconn := component_connected G hcomponent
  have htree : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsTree :=
    ⟨(connectedRegion_iff_induce_connected G R).mp hconn, hacyclic⟩
  have hsize : R.card + 2 ≤ F.card := by
    rw [cubic_tree_cut G hreg hconn hacyclic] at hcut
    exact hcut
  refine ⟨htree, hsize, ?_⟩
  intro i hi
  have hdisj : Disjoint R (Cycle.vertices (C i)) := by
    apply Finset.disjoint_left.mpr
    intro v hvR hvC
    exact (Finset.mem_compl.mp (component_subset G hcomponent hvR))
      (Finset.mem_biUnion.mpr ⟨i, hi, hvC⟩)
  have hsizeq : R.card + 1 ≤ q := by
    have hmult : F.card ≤ F.card * (2 * r + 1) := by nlinarith
    omega
  exact cubic_cycle_contact_edges_unique_of_no_short_external_return R (C i) q
    hconn hsizeq hdisj (hregular i hi) (hreturn i hi)

end Erdos1016.Proof.ConditionalComplementGeometry

end
