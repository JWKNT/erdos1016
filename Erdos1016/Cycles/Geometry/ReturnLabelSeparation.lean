import Erdos1016.Decomposition.TwoCore.PrunedAttachments
import Erdos1016.Cycles.Filtering.ReturnExclusion
import Erdos1016.Cycles.Geometry.SeparatedLabelCount

set_option autoImplicit false

/-!
# Geometric separation of equal degree-two labels

The label paths are the actual lost-incidence routes through pruned trees.
Two such routes have disjoint carriers. If their old-cycle labels coincide,
a segment of the new cycle joins them into an external return; the retained
return filter therefore forces the separation used in Lemma 5.2.
-/

noncomputable section
namespace Erdos1016.Proof.ConditionalLabelSeparation

open Erdos1016.SafeCore Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.PrunedCoreAttachments
open Erdos1016.Proof.ConditionalComplementGeometry
open Erdos1016.Proof.TwoCorePathGeometry
open Erdos1016.Proof.ExternalReturnFilter

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The carrier of a label route is its starting core vertex and its
possibly empty attached pruned tree. -/
theorem route_carriers_disjoint
    (G : PhysicalGraph) (U : Finset G.Vertex)
    {a b : G.Vertex} (hab : a ≠ b)
    (ha : a ∈ vertices G.toSimpleGraph Uᶜ) (hb : b ∈ vertices G.toSimpleGraph Uᶜ)
    (R S : Finset G.Vertex)
    (hR : R = ∅ ∨ R ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ) ∧
      ∃ w ∈ R, G.toSimpleGraph.Adj a w)
    (hS : S = ∅ ∨ S ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ) ∧
      ∃ w ∈ S, G.toSimpleGraph.Adj b w) :
    Disjoint (insert a R) (insert b S) := by
  have hRC : ∀ z ∈ R, z ∉ vertices G.toSimpleGraph Uᶜ := by
    intro z hz
    rcases hR with rfl | ⟨hR, _⟩
    · simp at hz
    · exact (Finset.mem_sdiff.mp (component_subset G hR hz)).2
  have hSC : ∀ z ∈ S, z ∉ vertices G.toSimpleGraph Uᶜ := by
    intro z hz
    rcases hS with rfl | ⟨hS, _⟩
    · simp at hz
    · exact (Finset.mem_sdiff.mp (component_subset G hS hz)).2
  have hRS : Disjoint R S := by
    rcases hR with rfl | ⟨hR, w, hw, haw⟩
    · simp
    rcases hS with rfl | ⟨hS, w', hw', hbw⟩
    · simp
    apply components_disjoint G hR hS
    intro hEq
    subst S
    exact hab (pruned_component_attachment_vertex_unique G U R hR ha hb hw hw' haw hbw)
  apply Finset.disjoint_left.mpr
  intro z hzR hzS
  rcases Finset.mem_insert.mp hzR with rfl | hzR
  · rcases Finset.mem_insert.mp hzS with heq | hzS
    · exact hab heq
    · exact hSC _ hzS ha
  · rcases Finset.mem_insert.mp hzS with rfl | hzS
    · exact hRC _ hzR hb
    · exact Finset.disjoint_left.mp hRS hzR hzS

/-- Remove the final incidence from a nontrivial simple path. -/
theorem trim_last_of_path
    {G : PhysicalGraph} {a u : G.Vertex} (hau : a ≠ u)
    (p : G.toSimpleGraph.Walk a u) (hp : p.IsPath) :
    ∃ r, ∃ t : G.toSimpleGraph.Walk a r, ∃ h : G.toSimpleGraph.Adj r u,
      p = t.concat h ∧ t.IsPath ∧ u ∉ t.support := by
  cases p with
  | nil => exact (hau rfl).elim
  | cons h p =>
    obtain ⟨r, t, hlast, heq⟩ := SimpleGraph.Walk.exists_cons_eq_concat h p
    rw [heq, SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_concat,
      List.concat_eq_append, List.nodup_append] at hp
    refine ⟨r, t, hlast, heq, (SimpleGraph.Walk.isPath_def t).mpr hp.1, ?_⟩
    intro hut
    exact (List.disjoint_left.mp hp.2.2) hut (by simp)

/-- A cubic cycle vertex has at most one outside neighbor. -/
theorem cycle_outside_neighbor_unique
    {G : PhysicalGraph} (C : G.CycleWord) (u r s : G.Vertex)
    (hu : u ∈ Cycle.vertices C) (hcubic : G.degree u = 3)
    (hr : r ∉ Cycle.vertices C) (hs : s ∉ Cycle.vertices C)
    (hru : G.toSimpleGraph.Adj r u) (hsu : G.toSimpleGraph.Adj s u) : r = s := by
  obtain ⟨e, _, he⟩ := hru
  obtain ⟨f, _, hf⟩ := hsu
  have memcut (e : G.Edge)
      (h : (G.src e = r ∧ G.dst e = u) ∨ (G.src e = u ∧ G.dst e = r)) :
      e ∈ G.traceCutEdgesAt (Cycle.vertices C) u := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h | h
    · exact ⟨Or.inr h.2, Or.inr ⟨h.1 ▸ hr, h.2 ▸ hu⟩⟩
    · exact ⟨Or.inl h.1, Or.inl ⟨h.1 ▸ hu, h.2 ▸ hr⟩⟩
  have hecut := memcut e he
  have hfcut : f ∈ G.traceCutEdgesAt (Cycle.vertices C) u := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hf with h | h
    · exact ⟨Or.inr h.2, Or.inr ⟨h.1 ▸ hs, h.2 ▸ hu⟩⟩
    · exact ⟨Or.inl h.1, Or.inl ⟨h.1 ▸ hu, h.2 ▸ hs⟩⟩
  have hcut := G.traceCutDegree_le_one (Cycle.vertices C) u hu hcubic
    (cycle_traceInsideDegree_ge_two C u hu)
  have hef := Finset.card_le_one.mp hcut e hecut f hfcut
  subst f
  rcases he with he | he <;> rcases hf with hf | hf
  · exact he.1.symm.trans hf.1
  · exact (hr (he.1 ▸ hf.1 ▸ hu)).elim
  · exact (hs (hf.1 ▸ he.1 ▸ hu)).elim
  · exact he.2.symm.trans hf.2

/-- Two label routes to one old cycle, joined along the new cycle, force a
long segment. The external path is explicitly concatenated and loop-erased
before applying the retained-cycle filter. -/
theorem same_label_segment_long
    {G : PhysicalGraph} (J U D : Finset G.Vertex) (C : G.CycleWord) (K q : ℕ)
    (hUD : Disjoint U D) (hCU : Cycle.vertices C ⊆ U)
    (hDJ : D ⊆ J) (hcubic : ∀ u ∈ Cycle.vertices C, G.degree u = 3)
    (hreturn : NoShortExternalReturnWithin G J (Cycle.vertices C) q)
    {a b u v : G.Vertex} (ha : a ∈ D) (hb : b ∈ D)
    (hu : u ∈ Cycle.vertices C) (hv : v ∈ Cycle.vertices C)
    (R S : Finset G.Vertex)
    (hcarriers : Disjoint (insert a R) (insert b S))
    (hRJ : R ⊆ J) (hSJ : S ⊆ J)
    (hRU : Disjoint R U) (hSU : Disjoint S U)
    (p : G.toSimpleGraph.Walk a u) (hp : p.IsPath) (hpK : p.length ≤ K - 1)
    (hpR : ∀ z ∈ p.support, z = a ∨ z = u ∨ z ∈ R)
    (p' : G.toSimpleGraph.Walk b v) (hp' : p'.IsPath) (hp'K : p'.length ≤ K - 1)
    (hp'S : ∀ z ∈ p'.support, z = b ∨ z = v ∨ z ∈ S)
    (seg : G.toSimpleGraph.Walk a b) (hseg : ∀ z ∈ seg.support, z ∈ D) :
    q < seg.length + 2 * K := by
  have hau : a ≠ u := fun h => Finset.disjoint_left.mp hUD (h ▸ hCU hu) ha
  have hbv : b ≠ v := fun h => Finset.disjoint_left.mp hUD (h ▸ hCU hv) hb
  obtain ⟨r, t, hru, hp_eq, ht, hut⟩ := trim_last_of_path hau p hp
  obtain ⟨s, t', hsv, hp'_eq, ht', hvt'⟩ := trim_last_of_path hbv p' hp'
  have htR : ∀ z ∈ t.support, z ∈ insert a R := by
    intro z hz
    have hzP : z ∈ p.support := by rw [hp_eq]; simp [hz, List.concat_eq_append]
    rcases hpR z hzP with rfl | heq | hzR
    · exact Finset.mem_insert_self _ _
    · exact (hut (heq ▸ hz)).elim
    · exact Finset.mem_insert_of_mem hzR
  have htS : ∀ z ∈ t'.support, z ∈ insert b S := by
    intro z hz
    have hzP : z ∈ p'.support := by rw [hp'_eq]; simp [hz, List.concat_eq_append]
    rcases hp'S z hzP with rfl | heq | hzS
    · exact Finset.mem_insert_self _ _
    · exact (hvt' (heq ▸ hz)).elim
    · exact Finset.mem_insert_of_mem hzS
  have hleftOutside : ∀ z ∈ insert a R, z ∉ U := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact fun hzU => Finset.disjoint_left.mp hUD hzU ha
    · exact fun hzU => Finset.disjoint_left.mp hRU hz hzU
  have hrightOutside : ∀ z ∈ insert b S, z ∉ U := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact fun hzU => Finset.disjoint_left.mp hUD hzU hb
    · exact fun hzU => Finset.disjoint_left.mp hSU hz hzU
  have huv : u ≠ v := by
    intro h
    have hrs := cycle_outside_neighbor_unique C u r s hu (hcubic u hu)
      (fun hrC => hleftOutside r (htR r t.end_mem_support) (hCU hrC))
      (fun hsC => hrightOutside s (htS s t'.end_mem_support) (hCU hsC))
      hru (h ▸ hsv)
    exact Finset.disjoint_left.mp hcarriers (htR r t.end_mem_support)
      (hrs ▸ htS s t'.end_mem_support)
  let w := t.reverse.append (seg.append t')
  have hwJ : ∀ z ∈ w.support, z ∈ J := by
    intro z hz
    simp only [w, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    rcases hz with hz | hz | hz
    · rcases Finset.mem_insert.mp (htR z hz) with rfl | hz
      · exact hDJ ha
      · exact hRJ hz
    · exact hDJ (hseg z hz)
    · rcases Finset.mem_insert.mp (htS z hz) with rfl | hz
      · exact hDJ hb
      · exact hSJ hz
  have hwC : ∀ z ∈ w.support, z ∉ Cycle.vertices C := by
    intro z hz hzC
    simp only [w, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    rcases hz with hz | hz | hz
    · exact hleftOutside z (htR z hz) (hCU hzC)
    · exact Finset.disjoint_left.mp hUD (hCU hzC) (hseg z hz)
    · exact hrightOutside z (htS z hz) (hCU hzC)
  have hlong := hreturn r s u v hu hv huv hru hsv w.bypass w.bypass_isPath
    (fun z hz => hwJ z (w.support_bypass_subset hz))
    (fun z hz => hwC z (w.support_bypass_subset hz))
  have hlen := w.length_bypass_le
  have hpLen : p.length = t.length + 1 := by simp [hp_eq]
  have hp'Len : p'.length = t'.length + 1 := by simp [hp'_eq]
  have hwLen : w.length = t.length + seg.length + t'.length := by simp [w, Nat.add_assoc]
  omega

end Erdos1016.Proof.ConditionalLabelSeparation

end
