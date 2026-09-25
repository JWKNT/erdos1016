import Erdos1016.Cycles.Geometry.ReturnLabelSeparation
import Erdos1016.Nonbacktracking.Walks.WindowPositions

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ConditionalDegreeTwoLabels

open Erdos1016.SafeCore Erdos1016.BoundaryDecay
open Erdos1016.Nonbacktracking.FiniteTwoCore
open Erdos1016.Proof.PrunedCoreAttachments
open Erdos1016.Proof.ConditionalLabelSeparation
open Erdos1016.Proof.ExternalReturnFilter
open Erdos1016.Proof.ConditionalDegreeTwoSpacing

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual path certificate constructed from a lost cubic incidence. -/
structure LabelRoute (G : PhysicalGraph) (U D : Finset G.Vertex) (K : ℕ) (v : G.Vertex) where
  endpoint : G.Vertex
  endpoint_mem : endpoint ∈ U
  region : Finset G.Vertex
  region_spec : region = ∅ ∨
    region ∈ components G (Uᶜ \ vertices G.toSimpleGraph Uᶜ) ∧
      ∃ w ∈ region, G.toSimpleGraph.Adj v w
  path : G.toSimpleGraph.Walk v endpoint
  isPath : path.IsPath
  length_le : path.length ≤ K - 1
  support : ∀ z ∈ path.support, z = v ∨ z = endpoint ∨ z ∈ region

theorem labelRoute_exists
    (G : PhysicalGraph) (U D B : Finset G.Vertex) (K : ℕ) (hK : 2 ≤ K)
    (hUD : Disjoint U D) (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    (v : G.Vertex) (hv : v ∈ D) (hcubic : G.degree v = 3)
    (hdegree : degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph Uᶜ) v = 2)
    (hexception : v ∉ exceptionalAttachments G U D B) :
    Nonempty (LabelRoute G U D K v) := by
  obtain ⟨u, hu, R, hR, p, hp, hlen, hsup⟩ :=
    degreeTwo_nonexceptional_has_short_route G U D B K hK hUD hDK hsmall
      v hv hcubic hdegree hexception
  exact ⟨⟨u, hu, R, hR, p, hp, hlen, hsup⟩⟩

namespace LabelRoute

variable {G : PhysicalGraph} {U D : Finset G.Vertex} {K : ℕ} {v : G.Vertex}

theorem region_disjoint_deleted (r : LabelRoute G U D K v) : Disjoint r.region U := by
  rcases r.region_spec with he | ⟨hR, _⟩
  · rw [he]; simp
  · apply Finset.disjoint_left.mpr
    intro z hzR hzU
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp (component_subset G hR hzR)).1 hzU

theorem region_subset_safe (r : LabelRoute G U D K v)
    (J B : Finset G.Vertex) (hDK : D ⊆ vertices G.toSimpleGraph Uᶜ) (hv : v ∈ D)
    (hexception : v ∉ exceptionalAttachments G U D B)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B → R ⊆ J) :
    r.region ⊆ J := by
  rcases r.region_spec with he | ⟨hR, w, hw, hvw⟩
  · rw [he]; exact Finset.empty_subset _
  · have hnew := pruned_attachment_is_new_component G U D r.region hDK hR hv hw hvw
    apply hsmall r.region hnew
    intro heq
    apply hexception
    apply Finset.mem_filter.mpr
    exact ⟨hv, heq ▸ hR, w, heq ▸ hw, hvw⟩

end LabelRoute

/-- Actual degree-two vertices on any injective sequence of successive
new-cycle vertices obey the manuscript's separated-label count. The route
labels and exceptional positions are constructed inside the proof. -/
theorem degreeTwo_positions_count
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (J : Finset G.Vertex) (F : Finset ι) (C : ι → G.CycleWord)
    (D B : Finset G.Vertex) (K q Δ m : ℕ)
    (hK : 2 ≤ K) (hΔ : 0 < Δ) (hΔq : Δ ≤ q - 2 * K + 1)
    (hUD : Disjoint (F.biUnion (fun i => Cycle.vertices (C i))) D)
    (hDK : D ⊆ vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (hDJ : D ⊆ J) (hDcubic : ∀ v ∈ D, G.degree v = 3)
    (hCcubic : ∀ i ∈ F, ∀ v ∈ Cycle.vertices (C i), G.degree v = 3)
    (hreturn : ∀ i ∈ F, NoShortExternalReturnWithin G J (Cycle.vertices (C i)) q)
    (hsmall : ∀ R ∈ components G ((F.biUnion (fun i => Cycle.vertices (C i))) ∪ D)ᶜ,
      R ≠ B → R ⊆ J ∧
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    (position : Fin m → G.Vertex) (hinj : Function.Injective position)
    (hpos : ∀ i, position i ∈ D)
    (hsegment : ∀ a b : Fin m, a.val < b.val →
      ∃ p : G.toSimpleGraph.Walk (position a) (position b),
        p.length ≤ b.val - a.val ∧ ∀ z ∈ p.support, z ∈ D) :
    (Finset.univ.filter (fun i : Fin m => degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
      (position i) = 2)).card ≤
      1 + F.card * Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  let U := F.biUnion (fun i => Cycle.vertices (C i))
  let marked := Finset.univ.filter (fun i : Fin m =>
    degreeWithin G.toSimpleGraph (vertices G.toSimpleGraph Uᶜ) (position i) = 2)
  let exceptional := Finset.univ.filter (fun i : Fin m =>
    position i ∈ exceptionalAttachments G U D B)
  have hexceptional : exceptional.card ≤ 1 := by
    have hmap : exceptional.image position ⊆ exceptionalAttachments G U D B := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    calc
      exceptional.card = (exceptional.image position).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (exceptionalAttachments G U D B).card := Finset.card_le_card hmap
      _ ≤ 1 := exceptionalAttachments_card_le_one G U D B hDK
  have hnonexc (i : ↥(marked \ exceptional)) :
      position i.1 ∉ exceptionalAttachments G U D B := by
    intro h
    exact (Finset.mem_sdiff.mp i.2).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  let route (i : ↥(marked \ exceptional)) : LabelRoute G U D K (position i.1) :=
    Classical.choice (labelRoute_exists G U D B K hK hUD hDK
      (fun R hR hRB => (hsmall R hR hRB).2) (position i.1) (hpos i.1)
      (hDcubic _ (hpos i.1)) (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.2).1).2
      (hnonexc i))
  have hexlabel (i : ↥(marked \ exceptional)) :
      ∃ c : F, (route i).endpoint ∈ Cycle.vertices (C c.1) := by
    obtain ⟨c, hc, hmem⟩ := Finset.mem_biUnion.mp (route i).endpoint_mem
    exact ⟨⟨c, hc⟩, hmem⟩
  let label : ↥(marked \ exceptional) → F := fun i => Classical.choose (hexlabel i)
  have hlabel (i : ↥(marked \ exceptional)) :
      (route i).endpoint ∈ Cycle.vertices (C (label i).1) := Classical.choose_spec (hexlabel i)
  have hseparated : ∀ a b : ↥(marked \ exceptional), a.1.val < b.1.val →
      label a = label b → a.1.val + Δ ≤ b.1.val := by
    intro a b hab hsame
    have habV : position a.1 ≠ position b.1 := by
      intro heq
      have := congrArg Fin.val (hinj heq)
      omega
    have hcarriers := route_carriers_disjoint G U habV (hDK (hpos a.1)) (hDK (hpos b.1))
      (route a).region (route b).region (route a).region_spec (route b).region_spec
    have hRJ := (route a).region_subset_safe J B hDK (hpos a.1) (hnonexc a)
      (fun R hR hRB => (hsmall R hR hRB).1)
    have hSJ := (route b).region_subset_safe J B hDK (hpos b.1) (hnonexc b)
      (fun R hR hRB => (hsmall R hR hRB).1)
    have hCU : Cycle.vertices (C (label a).1) ⊆ U := by
      intro v hv
      exact Finset.mem_biUnion.mpr ⟨(label a).1, (label a).2, hv⟩
    have hbLabel : (route b).endpoint ∈ Cycle.vertices (C (label a).1) := by
      rw [hsame]
      exact hlabel b
    obtain ⟨seg, hlen, hsup⟩ := hsegment a.1 b.1 hab
    have hlong := same_label_segment_long J U D (C (label a).1) K q
      hUD hCU hDJ (hCcubic _ (label a).2) (hreturn _ (label a).2)
      (hpos a.1) (hpos b.1) (hlabel a) hbLabel (route a).region (route b).region
      hcarriers hRJ hSJ (route a).region_disjoint_deleted (route b).region_disjoint_deleted
      (route a).path (route a).isPath (route a).length_le (route a).support
      (route b).path (route b).isPath (route b).length_le (route b).support seg hsup
    omega
  have hcount := card_le_exceptional_add_labels_mul_ceil marked exceptional label hΔ hseparated
  simp only [Fintype.card_coe] at hcount
  exact hcount.trans (Nat.add_le_add_right hexceptional _)

/-- Adding the last vertex of a short suffix costs at most one further
marked position, giving the exact `2+j ceil((s-1)/Δ)` budget. -/
theorem degreeTwo_positions_count_with_last
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (J : Finset G.Vertex) (F : Finset ι) (C : ι → G.CycleWord)
    (D B : Finset G.Vertex) (K q Δ m : ℕ)
    (hK : 2 ≤ K) (hΔ : 0 < Δ) (hΔq : Δ ≤ q - 2 * K + 1)
    (hUD : Disjoint (F.biUnion (fun i => Cycle.vertices (C i))) D)
    (hDK : D ⊆ vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (hDJ : D ⊆ J) (hDcubic : ∀ v ∈ D, G.degree v = 3)
    (hCcubic : ∀ i ∈ F, ∀ v ∈ Cycle.vertices (C i), G.degree v = 3)
    (hreturn : ∀ i ∈ F, NoShortExternalReturnWithin G J (Cycle.vertices (C i)) q)
    (hsmall : ∀ R ∈ components G ((F.biUnion (fun i => Cycle.vertices (C i))) ∪ D)ᶜ,
      R ≠ B → R ⊆ J ∧
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    (position : Fin (m + 1) → G.Vertex) (hinj : Function.Injective position)
    (hpos : ∀ i, position i ∈ D)
    (hsegment : ∀ a b : Fin (m + 1), a.val < b.val →
      ∃ p : G.toSimpleGraph.Walk (position a) (position b),
        p.length ≤ b.val - a.val ∧ ∀ z ∈ p.support, z ∈ D) :
    (Finset.univ.filter (fun i : Fin (m + 1) => degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
      (position i) = 2)).card ≤
      2 + F.card * Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  let reduced : Fin m → G.Vertex := fun i => position i.castSucc
  have hredinj : Function.Injective reduced := by
    intro i j h
    exact Fin.castSucc_injective _ (hinj h)
  have hred := degreeTwo_positions_count J F C D B K q Δ m hK hΔ hΔq
    hUD hDK hDJ hDcubic hCcubic hreturn hsmall reduced hredinj
    (fun i => hpos i.castSucc) (fun a b hab => hsegment a.castSucc b.castSucc hab)
  have hlast := Erdos1016.Proof.WalkWindowPositions.filter_fin_card_le_pred_add_one m
    (fun i => degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
      (position i) = 2)
  change (Finset.univ.filter (fun i : Fin m => degreeWithin G.toSimpleGraph
    (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (position i.castSucc) = 2)).card ≤ _ at hred
  have hlast' : (Finset.univ.filter (fun i : Fin (m + 1) => degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
      (position i) = 2)).card ≤
      (Finset.univ.filter (fun i : Fin m => degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
      (position i.castSucc) = 2)).card + 1 := by
    convert hlast using 3 <;> ext i <;> simp
  omega

/-- Actual internal vertices of a simple walk along the new cycle satisfy
the exact suffix degree-two budget, including the final position. -/
theorem degreeTwo_internal_walk_count
    {G : PhysicalGraph} {ι : Type*} [DecidableEq ι]
    (J : Finset G.Vertex) (F : Finset ι) (C : ι → G.CycleWord)
    (D B : Finset G.Vertex) (K q Δ m : ℕ)
    (hK : 2 ≤ K) (hΔ : 0 < Δ) (hΔq : Δ ≤ q - 2 * K + 1)
    (hUD : Disjoint (F.biUnion (fun i => Cycle.vertices (C i))) D)
    (hDK : D ⊆ vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (hDJ : D ⊆ J) (hDcubic : ∀ v ∈ D, G.degree v = 3)
    (hCcubic : ∀ i ∈ F, ∀ v ∈ Cycle.vertices (C i), G.degree v = 3)
    (hreturn : ∀ i ∈ F, NoShortExternalReturnWithin G J (Cycle.vertices (C i)) q)
    (hsmall : ∀ R ∈ components G ((F.biUnion (fun i => Cycle.vertices (C i))) ∪ D)ᶜ,
      R ≠ B → R ⊆ J ∧
      (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ z ∈ R, G.degree z = 3) ∧ R.card + 2 ≤ K ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    {a b : G.Vertex} (p : G.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hlen : p.length = m + 2) (hsupport : ∀ v ∈ p.support, v ∈ D) :
    p.support.tail.dropLast.countP (fun v => decide (degreeWithin G.toSimpleGraph
      (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ) v = 2)) ≤
      2 + F.card * Nat.ceil ((m : ℝ) / (Δ : ℝ)) := by
  let position : Fin (m + 1) → G.Vertex := fun i => p.getVert (1 + i.val)
  have hend : 1 + (m + 1) ≤ p.length + 1 := by omega
  have hinj := Erdos1016.Proof.WalkWindowPositions.window_positions_injective p hp 1 (m + 1) hend
  have hpos : ∀ i, position i ∈ D := fun i => hsupport _ (p.getVert_mem_support _)
  have hsegment : ∀ a b : Fin (m + 1), a.val < b.val →
      ∃ q : G.toSimpleGraph.Walk (position a) (position b),
        q.length ≤ b.val - a.val ∧ ∀ z ∈ q.support, z ∈ D := by
    intro a b hab
    obtain ⟨q, hlen, hsup⟩ := Erdos1016.Proof.WalkWindowPositions.window_segment
      p 1 (m + 1) hend a b hab
    exact ⟨q, hlen.le, fun z hz => hsupport z (hsup hz)⟩
  have hcount := degreeTwo_positions_count_with_last J F C D B K q Δ m hK hΔ hΔq
    hUD hDK hDJ hDcubic hCcubic hreturn hsmall position hinj hpos hsegment
  rw [Erdos1016.Proof.WalkWindowPositions.countP_bool_eq_filter_positions]
  simp only [decide_eq_true_eq]
  simp_rw [Erdos1016.Proof.WalkWindowPositions.internal_get_eq_getVert]
  have hllen : p.support.tail.dropLast.length = m + 1 := by
    simp only [List.length_dropLast, List.length_tail, SimpleGraph.Walk.length_support, hlen]
    omega
  have transport (a b : ℕ) (h : a = b) (P : ℕ → Prop) :
      (Finset.univ.filter (fun i : Fin a => P i.val)).card =
        (Finset.univ.filter (fun i : Fin b => P i.val)).card := by
    subst b
    rfl
  have ht := transport _ _ hllen (fun i => degreeWithin G.toSimpleGraph
    (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (p.getVert (i + 1)) = 2)
  have ht' : (Finset.univ.filter (fun i : Fin p.support.tail.dropLast.length =>
    degreeWithin G.toSimpleGraph
    (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (p.getVert (i.val + 1)) = 2)).card =
    (Finset.univ.filter (fun i : Fin (m+1) =>
    degreeWithin G.toSimpleGraph
    (vertices G.toSimpleGraph (F.biUnion (fun i => Cycle.vertices (C i)))ᶜ)
    (position i) = 2)).card := by
    convert ht using 2 <;> ext i <;> simp [position, Nat.add_comm]
  rw [ht']
  exact hcount

end Erdos1016.Proof.ConditionalDegreeTwoLabels

end
