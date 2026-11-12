import Erdos1016.Cycles.Selection.RetainedHighGirth
import Erdos1016.Cycles.Selection.ShortRegionObstructions
import Erdos1016.ExactMaximumSupport.LargeGirth.GirthRaiseBounds

set_option autoImplicit false

/-!
# Nested maximal packings at increasing girth scales

The construction uses actual labelled multigraph regions and retains every
region selected at an earlier stage. Its maximality is unconditional. The
quantitative recurrence explicitly requires the fixed-probability packing
inequality, which remains a separate graph theorem.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence

open FiniteMultiGraph

local instance regionPackingSequenceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem weaken_region (G : FiniteMultiGraph) {P Q U : Finset G.Vertex} {D E : ℕ}
    (h : G.ShortCyclicRegion P D U) (hQP : Q ⊆ P) (hDE : D ≤ E) :
    G.ShortCyclicRegion Q E U := by
  refine ⟨?_, h.size.trans hDE, h.connected, h.cyclic, h.cut.trans hDE⟩
  intro v hv
  exact Finset.mem_compl.mpr (fun hvQ => (Finset.mem_compl.mp (h.outside hv)) (hQP hvQ))

theorem exists_maximal (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ) :
    ∃ F : Finset (Finset G.Vertex),
      (∀ U ∈ F, G.ShortCyclicRegion P D U) ∧
      (∀ U ∈ F, ∀ V ∈ F, U ≠ V → Disjoint U V) ∧
      ∀ U, G.ShortCyclicRegion P D U → ((F.biUnion id) ∩ U).Nonempty := by
  have hne : ∀ U ∈ G.shortCyclicRegions P D, (id U).Nonempty := by
    intro U hU
    obtain ⟨v⟩ := (Finset.mem_filter.mp hU).2.connected.nonempty
    exact ⟨v.1, v.2⟩
  obtain ⟨F, hF, hd, hh⟩ := PackingCover.exists_maximal_disjoint_family
    (G.shortCyclicRegions P D) id hne
  exact ⟨F, fun U hU => (Finset.mem_filter.mp (hF hU)).2, hd,
    fun U hU => hh U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)⟩

def selected (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ) :
    Finset (Finset G.Vertex) := Classical.choose (exists_maximal G P D)

theorem selected_spec (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ) :
    (∀ U ∈ selected G P D, G.ShortCyclicRegion P D U) ∧
    (∀ U ∈ selected G P D, ∀ V ∈ selected G P D, U ≠ V → Disjoint U V) ∧
    ∀ U, G.ShortCyclicRegion P D U → (((selected G P D).biUnion id) ∩ U).Nonempty :=
  Classical.choose_spec (exists_maximal G P D)

def families (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) :
    ℕ → Finset (Finset G.Vertex)
  | 0 => ∅
  | n + 1 => families G P D n ∪
      selected G (P ∪ (families G P D n).biUnion id) (D n)

def vertices (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) (n : ℕ) :
    Finset G.Vertex := (families G P D n).biUnion id

@[simp] theorem vertices_zero (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) :
    vertices G P D 0 = ∅ := by simp [vertices, families]

theorem families_mono (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) :
    Monotone (families G P D) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Finset.subset_union_left

theorem vertices_mono (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) :
    Monotone (vertices G P D) := by
  intro i j hij v hv
  obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨U, families_mono G P D hij hU, hv⟩

theorem families_spec (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (hD : Monotone D) (n : ℕ) :
    ∀ U ∈ families G P D (n + 1), G.ShortCyclicRegion P (D n) U := by
  induction n with
  | zero =>
    intro U hU
    have hU' : U ∈ selected G (P ∪ ∅) (D 0) := by
      simpa only [families, Finset.biUnion_empty, Finset.empty_union] using hU
    exact weaken_region G ((selected_spec G (P ∪ ∅) (D 0)).1 U hU')
      Finset.subset_union_left le_rfl
  | succ n ih =>
    intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · exact weaken_region G (ih U hU) (fun _ h => h) (hD (by omega))
    · exact weaken_region G ((selected_spec G _ _).1 U hU) Finset.subset_union_left le_rfl

theorem vertices_outside (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (hD : Monotone D) (n : ℕ) : vertices G P D n ⊆ Pᶜ := by
  cases n with
  | zero => simp
  | succ n =>
    intro v hv
    obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
    exact (families_spec G P D hD n U hU).outside hv

theorem families_disjoint (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (n : ℕ) :
    ∀ U ∈ families G P D n, ∀ V ∈ families G P D n, U ≠ V → Disjoint U V := by
  induction n with
  | zero => simp [families]
  | succ n ih =>
    have hcross (U) (hU : U ∈ families G P D n) (V)
        (hV : V ∈ selected G (P ∪ vertices G P D n) (D n)) : Disjoint U V := by
      apply Finset.disjoint_left.mpr
      intro v hvU hvV
      have hvS : v ∈ vertices G P D n := Finset.mem_biUnion.mpr ⟨U, hU, hvU⟩
      have hout := ((selected_spec G _ _).1 V hV).outside hvV
      exact (Finset.mem_compl.mp hout) (Finset.mem_union_right P hvS)
    intro U hU V hV hUV
    rcases Finset.mem_union.mp hU with hU | hU <;>
      rcases Finset.mem_union.mp hV with hV | hV
    · exact ih U hU V hV hUV
    · exact hcross U hU V hV
    · exact (hcross V hV U hU).symm
    · exact (selected_spec G _ _).2.1 U hU V hV hUV

/-- Each stage hits every eligible region at its current scale. -/
theorem hits (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ) (n : ℕ)
    (U : Finset G.Vertex) (hU : G.ShortCyclicRegion P (D n) U) :
    (vertices G P D (n + 1) ∩ U).Nonempty := by
  by_cases hh : (vertices G P D n ∩ U).Nonempty
  · obtain ⟨v, hv⟩ := hh
    exact ⟨v, Finset.mem_inter.mpr
      ⟨vertices_mono G P D (Nat.le_succ n) (Finset.mem_inter.mp hv).1,
        (Finset.mem_inter.mp hv).2⟩⟩
  · have hout : U ⊆ (P ∪ vertices G P D n)ᶜ := by
      intro v hv
      apply Finset.mem_compl.mpr
      intro hvin
      rcases Finset.mem_union.mp hvin with hvP | hvS
      · exact (Finset.mem_compl.mp (hU.outside hv)) hvP
      · exact hh ⟨v, Finset.mem_inter.mpr ⟨hvS, hv⟩⟩
    have hnew : G.ShortCyclicRegion (P ∪ vertices G P D n) (D n) U :=
      ⟨hout, hU.size, hU.connected, hU.cyclic, hU.cut⟩
    obtain ⟨v, hv⟩ := (selected_spec G _ _).2.2 U hnew
    obtain ⟨V, hV, hvV⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).1
    exact ⟨v, Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨V, Finset.mem_union_right _ hV, hvV⟩,
        (Finset.mem_inter.mp hv).2⟩⟩

theorem vertices_step_card (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (n : ℕ) :
    (vertices G P D (n + 1)).card ≤ (vertices G P D n).card +
      (selected G (P ∪ vertices G P D n) (D n)).card * D n := by
  have heq : vertices G P D (n + 1) = vertices G P D n ∪
      (selected G (P ∪ vertices G P D n) (D n)).biUnion id := by
    ext v
    simp only [vertices, families, Finset.mem_biUnion, Finset.mem_union]
    aesop
  rw [heq]
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ U ∈ selected G (P ∪ vertices G P D n) (D n), U.card := Finset.card_biUnion_le
    _ ≤ ∑ _U ∈ selected G (P ∪ vertices G P D n) (D n), D n :=
      Finset.sum_le_sum fun U hU => ((selected_spec G _ _).1 U hU).size
    _ = _ := by simp

/-- A single quantitative packing estimate gives the deletion-size recurrence. -/
theorem vertices_step_bound (G : FiniteMultiGraph) (P : Finset G.Vertex) (D : ℕ → ℕ)
    (n : ℕ) (hD : 1 ≤ D n)
    (hpack : (selected G (P ∪ vertices G P D n) (D n)).card ≤
      1551 * D n * ((vertices G P D n).card + 1) * 2 ^ D n) :
    (vertices G P D (n + 1)).card + 1 ≤
      1552 * (D n) ^ 2 * 2 ^ D n * ((vertices G P D n).card + 1) := by
  have hc := vertices_step_card G P D n
  have hm := Nat.mul_le_mul_right (D n) hpack
  have ht : 1 ≤ (D n) ^ 2 * 2 ^ D n := by
    apply Nat.one_le_iff_ne_zero.mpr
    have hp : 0 < D n := by omega
    positivity
  have hs := Nat.mul_le_mul_right ((vertices G P D n).card + 1) ht
  nlinarith

/-- Conditional only on the explicit cardinality bound for each newly selected
family, the actual nested sets satisfy the dyadic deletion budget. -/
theorem vertices_size_bound (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ) (hD : 7 ≤ D)
    (hpack : ∀ n,
      (selected G (P ∪ vertices G P (GirthRaiseBounds.scale D) n)
        (GirthRaiseBounds.scale D n)).card ≤
      1551 * GirthRaiseBounds.scale D n *
        ((vertices G P (GirthRaiseBounds.scale D) n).card + 1) *
          2 ^ GirthRaiseBounds.scale D n) (j : ℕ) :
    (vertices G P (GirthRaiseBounds.scale D) (j + 1)).card + 1 ≤
      2 ^ (2 * GirthRaiseBounds.scale D j +
        6 * (Nat.clog 2 (GirthRaiseBounds.scale D j)) ^ 2) := by
  apply GirthRaiseBounds.size_bound D hD
    (fun n => (vertices G P (GirthRaiseBounds.scale D) n).card) (by simp)
  intro n
  apply vertices_step_bound G P (GirthRaiseBounds.scale D) n ?_ (hpack n)
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  dsimp [GirthRaiseBounds.scale]
  nlinarith

/-- The selected vertices remove all loops, parallel pairs, and ordinary cycles
of length at most the current scale. No packing-size bound is needed. -/
theorem retained_high_girth (G : FiniteMultiGraph) (P : Finset G.Vertex)
    (D : ℕ → ℕ) (n : ℕ) (hD : 2 ≤ D n) (hmax : ∀ v, G.degree v ≤ 3) :
    ∃ hloop : ∀ e ∈ G.internalEdges (P ∪ vertices G P D (n + 1))ᶜ,
        G.src e ≠ G.dst e,
    ∃ hsimple : ∀ e ∈ G.internalEdges (P ∪ vertices G P D (n + 1))ᶜ,
        ∀ f ∈ G.internalEdges (P ∪ vertices G P D (n + 1))ᶜ,
        ((G.src e = G.src f ∧ G.dst e = G.dst f) ∨
          (G.src e = G.dst f ∧ G.dst e = G.src f)) → e = f,
    Nonbacktracking.ShortWalks.GirthGreater
      (InducedSimpleRealization.graph G (P ∪ vertices G P D (n + 1))ᶜ
        hloop hsimple).toSimpleGraph (D n) := by
  have hhit := hits G P D n
  have hloop := G.retained_no_loops P (vertices G P D (n + 1)) (D n) (by omega)
    hmax hhit
  have hsimple := G.retained_simple P (vertices G P D (n + 1)) (D n) hD hmax hhit
  exact ⟨hloop, hsimple, G.retained_girth P (vertices G P D (n + 1)) (D n)
    hloop hsimple hmax hhit⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.RegionPackingSequence
