import Erdos1016.CycleSpace.ForcedRegionCylinder
import Erdos1016.Decomposition.Regions.Basic

set_option autoImplicit false

/-!
# Literal cycle supports and selected-component events

Cycles are the existing `PhysicalGraph.CycleWord`, not formal bit labels.
We prove their edge/vertex identity, the forest obstruction, and the fact
that two distinct overlapping component events cannot coexist. The latter
uses actual support connectivity, not pairwise-independence assumptions.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

open BoundaryTrace SafeCore
local instance cycleGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {G : PhysicalGraph}

@[simp] theorem mem_usedVertices (x : G.Word) (v : G.Vertex) :
    v ∈ G.usedVertices x ↔ ∃ e, x e ≠ 0 ∧ G.incident e v := by
  simp [PhysicalGraph.usedVertices]

theorem src_mem_used_of_ne_zero (x : G.Word) (e : G.Edge) (he : x e ≠ 0) :
    G.src e ∈ G.usedVertices x :=
  (mem_usedVertices x _).2 ⟨e, he, Or.inl rfl⟩

theorem dst_mem_used_of_ne_zero (x : G.Word) (e : G.Edge) (he : x e ≠ 0) :
    G.dst e ∈ G.usedVertices x :=
  (mem_usedVertices x _).2 ⟨e, he, Or.inr rfl⟩

theorem word_zero_of_src_not_used (x : G.Word) (e : G.Edge)
    (he : G.src e ∉ G.usedVertices x) : x e = 0 := by
  by_contra hn
  exact he (src_mem_used_of_ne_zero x e hn)

theorem word_zero_of_dst_not_used (x : G.Word) (e : G.Edge)
    (he : G.dst e ∉ G.usedVertices x) : x e = 0 := by
  by_contra hn
  exact he (dst_mem_used_of_ne_zero x e hn)

theorem usedVertices_nonempty_of_ne_zero (x : G.Word) (hx : x ≠ 0) :
    (G.usedVertices x).Nonempty := by
  have he : ∃ e, x e ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨e, he⟩ := he
  exact ⟨G.src e, src_mem_used_of_ne_zero x e he⟩

theorem selectedDegree_zero_of_not_used (x : G.Word) (v : G.Vertex)
    (hv : v ∉ G.usedVertices x) : G.selectedDegree x v = 0 := by
  unfold PhysicalGraph.selectedDegree
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_not_mem.2
  intro e he
  obtain ⟨_, hne, hi⟩ := Finset.mem_filter.1 he
  exact hv ((mem_usedVertices x v).2 ⟨e, hne, hi⟩)

/-- The handshaking identity for a selected labelled edge word. -/
theorem sum_selectedDegree (x : G.Word) :
    (∑ v, G.selectedDegree x v) = 2 * G.wordLength x := by
  have hpoint (v : G.Vertex) (e : G.Edge) :
      (if x e ≠ 0 ∧ G.incident e v then (1 : ℕ) else 0) =
        (if x e ≠ 0 then
          (if G.src e = v then 1 else 0) +
          (if G.dst e = v then 1 else 0) else 0) := by
    by_cases hx : x e = 0 <;> by_cases hs : G.src e = v <;>
      by_cases hd : G.dst e = v
    all_goals try simp [hx, hs, hd, PhysicalGraph.incident]
    all_goals exact False.elim (G.noLoops e (hs.trans hd.symm))
  have hdegree (v : G.Vertex) :
      G.selectedDegree x v = ∑ e, if x e ≠ 0 then
        (if G.src e = v then 1 else 0) +
        (if G.dst e = v then 1 else 0) else 0 := by
    simp only [PhysicalGraph.selectedDegree, Finset.card_eq_sum_ones,
      Finset.sum_filter]
    exact Finset.sum_congr rfl fun e _ => hpoint v e
  simp_rw [hdegree]
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ v, if x e ≠ 0 then
        (if G.src e = v then 1 else 0) +
        (if G.dst e = v then 1 else 0) else 0) =
        ∑ e, if x e ≠ 0 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hx : x e = 0
      · simp [hx]
      · simp [hx, Finset.sum_add_distrib, eq_comm]
    _ = 2 * G.wordLength x := by
      have hcount : (∑ e, if x e ≠ 0 then (1 : ℕ) else 0) =
          G.wordLength x := by
        unfold PhysicalGraph.wordLength PhysicalGraph.edgeSupport
        rw [Finset.card_filter]
      calc
        (∑ e, if x e ≠ 0 then 2 else 0) =
            ∑ e, 2 * (if x e ≠ 0 then (1 : ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          split <;> simp
        _ = 2 * ∑ e, if x e ≠ 0 then (1 : ℕ) else 0 := by
          symm
          exact Finset.mul_sum Finset.univ (fun e : G.Edge =>
            if x e ≠ 0 then (1 : ℕ) else 0) 2
        _ = 2 * G.wordLength x := by rw [hcount]

namespace Cycle

abbrev vertices (C : G.CycleWord) := G.usedVertices C.1
abbrev edges (C : G.CycleWord) := G.edgeSupport C.1
abbrev length (C : G.CycleWord) := G.wordLength C.1

def seed (C : G.CycleWord) : G.CycleSpace := ⟨C.1, C.2.2.1⟩

def Event (C : G.CycleWord) (x : G.CycleSpace) : Prop :=
  ForcedRegion G.traceNetwork (vertices C) C.1 x.1

def probability (C : G.CycleWord) : ℝ := Finite.density (Event C)

theorem vertices_nonempty (C : G.CycleWord) : (vertices C).Nonempty :=
  usedVertices_nonempty_of_ne_zero C.1 C.2.1

theorem length_eq_vertices_card (C : G.CycleWord) : length C = (vertices C).card := by
  have hsum := sum_selectedDegree C.1
  have hdegree (v : G.Vertex) : G.selectedDegree C.1 v =
      if v ∈ vertices C then 2 else 0 := by
    by_cases hv : v ∈ vertices C
    · simp only [if_pos hv]
      exact C.2.2.2.2 v hv
    · simp only [if_neg hv]
      exact selectedDegree_zero_of_not_used C.1 v hv
  simp_rw [hdegree] at hsum
  have hcard : (∑ v : G.Vertex, if v ∈ vertices C then (2 : ℕ) else 0) =
      2 * (vertices C).card := by
    have hfilter : Finset.univ.filter (fun v : G.Vertex => v ∈ vertices C) =
        vertices C := by
      ext v
      simp
    calc
      (∑ v : G.Vertex, if v ∈ vertices C then (2 : ℕ) else 0) =
          ∑ v ∈ Finset.univ.filter (fun v : G.Vertex => v ∈ vertices C), (2 : ℕ) := by
        exact (Finset.sum_filter (s := Finset.univ)
          (p := fun v : G.Vertex => v ∈ vertices C) (f := fun _ => (2 : ℕ))).symm
      _ = 2 * (vertices C).card := by rw [hfilter]; simp [Nat.mul_comm]
  rw [hcard] at hsum
  change 2 * (vertices C).card = 2 * length C at hsum
  omega

theorem edges_subset_internal (C : G.CycleWord) :
    edges C ⊆ internalEdges G (vertices C) := by
  intro e he
  have hx : C.1 e ≠ 0 := (Finset.mem_filter.1 he).2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    src_mem_used_of_ne_zero C.1 e hx, dst_mem_used_of_ne_zero C.1 e hx⟩

theorem vertices_card_le_internal (C : G.CycleWord) :
    (vertices C).card ≤ (internalEdges G (vertices C)).card := by
  rw [← length_eq_vertices_card C]
  exact Finset.card_le_card (edges_subset_internal C)

/-- Selected cycle edges correspond bijectively to the edge set of its
connected two-regular support. This counts physical edges, not orientations. -/
theorem support_edge_card (C : G.CycleWord) :
    Nat.card ((G.selectedGraph C.1).induce (↑(vertices C) : Set G.Vertex)).edgeSet =
      length C := by
  let H := (G.selectedGraph C.1).induce (↑(vertices C) : Set G.Vertex)
  let f : {e // e ∈ edges C} → H.edgeSet := fun e =>
    ⟨s(⟨G.src e.1, src_mem_used_of_ne_zero C.1 e.1 (Finset.mem_filter.1 e.2).2⟩,
       ⟨G.dst e.1, dst_mem_used_of_ne_zero C.1 e.1 (Finset.mem_filter.1 e.2).2⟩), by
      exact ⟨e.1, (Finset.mem_filter.1 e.2).2, Or.inl ⟨rfl, rfl⟩⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e d hed
      apply Subtype.ext
      apply G.simple
      have h := congrArg Subtype.val hed
      rcases Sym2.eq_iff.1 h with h | h
      · exact Or.inl ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
      · exact Or.inr ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩
    · rintro ⟨a, ha⟩
      revert ha
      refine Sym2.inductionOn a ?_
      intro u v huv
      rcases huv with ⟨e, hx, h | h⟩
      · have he : e ∈ edges C := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
        refine ⟨⟨e, he⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_iff.2 (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
      · have he : e ∈ edges C := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
        refine ⟨⟨e, he⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_iff.2 (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h.symm

/-- A cycle word is proved non-acyclic; it is not merely called a cycle. -/
theorem support_not_acyclic (C : G.CycleWord) :
    ¬ ((G.selectedGraph C.1).induce (↑(vertices C) : Set G.Vertex)).IsAcyclic := by
  intro hforest
  have ht : ((G.selectedGraph C.1).induce
      (↑(vertices C) : Set G.Vertex)).IsTree := ⟨C.2.2.2.1, hforest⟩
  have hcard := ((SimpleGraph.isTree_iff_connected_and_card).1 ht).2
  rw [support_edge_card C] at hcard
  have hverts : Nat.card ↑↑(vertices C) = (vertices C).card := by
    change Nat.card {v : G.Vertex // v ∈ vertices C} = _
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  change length C + 1 = Nat.card {v : G.Vertex // v ∈ vertices C} at hcard
  rw [hverts, length_eq_vertices_card C] at hcard
  omega

/-- Every event fixes the full neighborhood of the cycle to that cycle. -/
theorem event_adj (C : G.CycleWord) (x : G.CycleSpace) (hx : Event C x)
    {u v : G.Vertex} (hu : u ∈ vertices C)
    (huv : (G.selectedGraph C.1).Adj u v) :
    (G.selectedGraph x.1).Adj u v := by
  rcases huv with ⟨e, he, h | h⟩
  · have hs : G.traceNetwork.src e ∈ vertices C := by
      change G.src e ∈ vertices C
      rw [h.1]
      exact hu
    have hxe := hx e (Or.inl hs)
    exact ⟨e, by rwa [hxe], Or.inl h⟩
  · have hs : G.traceNetwork.dst e ∈ vertices C := by
      change G.dst e ∈ vertices C
      rw [h.2]
      exact hu
    have hxe := hx e (Or.inr hs)
    exact ⟨e, by rwa [hxe], Or.inr h⟩

/-- Foresthood on any original region containing the whole cycle forbids its
component event. No hypothesis concerns degrees outside the cycle. -/
theorem event_not_forest_restriction (C : G.CycleWord) (x : G.CycleSpace)
    (hx : Event C x) (U : Finset G.Vertex) (hCU : vertices C ⊆ U) :
    ¬ ((G.selectedGraph x.1).induce (↑U : Set G.Vertex)).IsAcyclic := by
  let f : ((G.selectedGraph C.1).induce (↑(vertices C) : Set G.Vertex)) →g
      ((G.selectedGraph x.1).induce (↑U : Set G.Vertex)) := {
    toFun := fun v : (↑(vertices C) : Set G.Vertex) =>
      (⟨v.1, hCU (by simpa using v.2)⟩ : (↑U : Set G.Vertex)),
    map_rel' := by
      intro u v huv
      change (G.selectedGraph C.1).Adj u.1 v.1 at huv
      change (G.selectedGraph x.1).Adj u.1 v.1
      exact event_adj C x hx u.2 huv }
  have hf : Function.Injective f := by
    intro u v huv
    have hval : (f u).val = (f v).val := congrArg (fun w => w.1) huv
    apply Subtype.ext
    change u.1 = v.1
    simpa [f] using hval
  intro hforest
  apply support_not_acyclic C
  intro v p hp
  exact hforest (p.map f)
    ((SimpleGraph.Walk.map_isCycle_iff_of_injective hf).2 hp)

/-- A second component event closes its support under every selected owner edge. -/
theorem event_support_closed (C : G.CycleWord) (x : G.CycleSpace)
    (hx : Event C x) {u v : G.Vertex} (hu : u ∈ vertices C)
    (huv : (G.selectedGraph x.1).Adj u v) : v ∈ vertices C := by
  rcases huv with ⟨e, he, h | h⟩
  · have hs : G.traceNetwork.src e ∈ vertices C := by
      change G.src e ∈ vertices C
      rw [h.1]
      exact hu
    have hxe := hx e (Or.inl hs)
    have hce : C.1 e ≠ 0 := by simpa only [hxe] using he
    change v ∈ vertices C
    rw [← h.2]
    exact dst_mem_used_of_ne_zero C.1 e hce
  · have hs : G.traceNetwork.dst e ∈ vertices C := by
      change G.dst e ∈ vertices C
      rw [h.2]
      exact hu
    have hxe := hx e (Or.inr hs)
    have hce : C.1 e ≠ 0 := by simpa only [hxe] using he
    change v ∈ vertices C
    rw [← h.1]
    exact src_mem_used_of_ne_zero C.1 e hce

/-- Joint component events with an overlapping vertex have the same support. -/
theorem vertices_subset_of_joint_overlap (C D : G.CycleWord)
    (x : G.CycleSpace) (hC : Event C x) (hD : Event D x)
    (v₀ : G.Vertex) (hvC : v₀ ∈ vertices C) (hvD : v₀ ∈ vertices D) :
    vertices C ⊆ vertices D := by
  intro v hv
  obtain ⟨p⟩ := C.2.2.2.1 ⟨v₀, hvC⟩ ⟨v, hv⟩
  have hwalk : ∀ {u w : {v : G.Vertex // v ∈ vertices C}},
      ((G.selectedGraph C.1).induce (↑(vertices C) : Set G.Vertex)).Walk u w →
      u.1 ∈ vertices D → w.1 ∈ vertices D := by
    intro u w p
    induction p with
    | nil => exact fun h => h
    | @cons u v w huv p ih =>
      intro hu
      exact ih (event_support_closed D x hD hu (event_adj C x hC u.2 huv))
  exact hwalk p hvD

/-- Distinct intersecting cycles cannot be simultaneous selected components.
This is stronger than the subcubic version: isolation gives the result in
any simple owner, including owners with a high-degree boundary apex. -/
theorem eq_of_joint_overlap (C D : G.CycleWord) (x : G.CycleSpace)
    (hC : Event C x) (hD : Event D x)
    (hoverlap : ¬ Disjoint (vertices C) (vertices D)) : C = D := by
  obtain ⟨v₀, hvC, hvD⟩ := Finset.not_disjoint_iff.1 hoverlap
  have hCD := vertices_subset_of_joint_overlap C D x hC hD v₀ hvC hvD
  have hDC := vertices_subset_of_joint_overlap D C x hD hC v₀ hvD hvC
  have hvertices : vertices C = vertices D := Finset.Subset.antisymm hCD hDC
  apply Subtype.ext
  funext e
  by_cases hs : G.src e ∈ vertices C
  · have h₁ := hC e (Or.inl hs)
    have h₂ := hD e (Or.inl (hvertices ▸ hs))
    exact h₁.symm.trans h₂
  · have hzC := word_zero_of_src_not_used C.1 e hs
    have hzD := word_zero_of_src_not_used D.1 e (by
      change G.src e ∉ vertices D
      simpa [hvertices] using hs)
    rw [hzC, hzD]



end Cycle
end Erdos1016.BoundaryDecay
