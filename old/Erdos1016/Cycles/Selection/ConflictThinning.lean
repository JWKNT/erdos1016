import Erdos1016.Probability.Avoidance.FiniteCycleBounds

set_option autoImplicit false

/-!
# Exact finite conflict thinning

The independent subfamily is constructed by maximizing a finite cardinality.
The bound is integer-valued: |F| <= |I| (J+1). No asymptotic extraction oracle
or unproved graph-coloring statement is used. The application below takes an
actual geometric conflict relation whose bounded degree is still to be
proved by the separator-nesting part of the manuscript.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.BoundaryDecay

local instance conflictThinningDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {ι : Type*}

def Independent (R : ι → ι → Prop) (s : Finset ι) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ R i j

def closedNeighbors (R : ι → ι → Prop) (s : Finset ι) (i : ι) : Finset ι :=
  s.filter fun j => j = i ∨ R i j

/-- A cardinality-maximal independent subfamily covers the original family
by its closed conflict neighborhoods. -/
theorem exists_independent_dominating (R : ι → ι → Prop) (hR : Symmetric R)
    (s : Finset ι) :
    ∃ t ⊆ s, Independent R t ∧ s ⊆ t.biUnion (closedNeighbors R s) := by
  classical
  let candidates := s.powerset.filter (Independent R)
  have hempty : (∅ : Finset ι) ∈ candidates := by
    simp [candidates, Independent]
  let sizes := candidates.image Finset.card
  have hne : sizes.Nonempty := (show candidates.Nonempty from ⟨∅, hempty⟩).image _
  obtain ⟨t, ht, hsize⟩ := Finset.mem_image.1 (Finset.max'_mem sizes hne)
  have hts : t ⊆ s := Finset.mem_powerset.1 (Finset.mem_filter.1 ht).1
  have hind : Independent R t := (Finset.mem_filter.1 ht).2
  have hmax : ∀ u ∈ candidates, u.card ≤ t.card := by
    intro u hu
    rw [hsize]
    exact Finset.le_max' sizes u.card (Finset.mem_image.2 ⟨u, hu, rfl⟩)
  refine ⟨t, hts, hind, ?_⟩
  intro b hb
  by_contra hcover
  have haway : ∀ a ∈ t, b ≠ a ∧ ¬ R a b := by
    intro a ha
    constructor
    · intro hba
      exact hcover (Finset.mem_biUnion.2 ⟨a, ha,
        Finset.mem_filter.2 ⟨hb, Or.inl hba⟩⟩)
    · intro hab
      exact hcover (Finset.mem_biUnion.2 ⟨a, ha,
        Finset.mem_filter.2 ⟨hb, Or.inr hab⟩⟩)
  have hbnot : b ∉ t := by
    intro hbt
    exact (haway b hbt).1 rfl
  have hins : Independent R (insert b t) := by
    intro i hi j hj hij
    rcases Finset.mem_insert.1 hi with hIb | hiT
    · subst i
      rcases Finset.mem_insert.1 hj with hJb | hjT
      · subst j
        exact False.elim (hij rfl)
      · exact fun h => (haway j hjT).2 (hR h)
    · rcases Finset.mem_insert.1 hj with hJb | hjT
      · subst j
        exact (haway i hiT).2
      · exact hind i hiT j hjT hij
  have hmem : insert b t ∈ candidates := by
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_powerset.2 ?_, hins⟩
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hb
    · exact hts hu
  have h := hmax (insert b t) hmem
  rw [Finset.card_insert_of_not_mem hbnot] at h
  omega

theorem closedNeighbors_card_le (R : ι → ι → Prop) (s : Finset ι)
    (i : ι) (J : ℕ) (hJ : (s.filter (R i)).card ≤ J) :
    (closedNeighbors R s i).card ≤ J + 1 := by
  classical
  have hsub : closedNeighbors R s i ⊆ insert i (s.filter (R i)) := by
    intro j hj
    obtain ⟨hjs, hji | hij⟩ := Finset.mem_filter.1 hj
    · exact Finset.mem_insert.2 (Or.inl hji)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_filter.2 ⟨hjs, hij⟩))
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))

/-- Integer form of the standard K/(J+1) thinning bound. -/
theorem exists_large_independent (R : ι → ι → Prop) (hR : Symmetric R)
    (s : Finset ι) (J : ℕ) (hJ : ∀ i ∈ s, (s.filter (R i)).card ≤ J) :
    ∃ t ⊆ s, Independent R t ∧ s.card ≤ t.card * (J + 1) := by
  obtain ⟨t, hts, hind, hcover⟩ := exists_independent_dominating R hR s
  refine ⟨t, hts, hind, ?_⟩
  calc
    s.card ≤ (t.biUnion (closedNeighbors R s)).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ t, (closedNeighbors R s i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ t, (J + 1) := by
      exact Finset.sum_le_sum fun i hi => closedNeighbors_card_le R s i J (hJ i (hts hi))
    _ = t.card * (J + 1) := by simp

/-- The complete MANY probability estimate, with finite conflict extraction
performed inside the theorem. The remaining hypotheses are stated on the
original graph and the actual geometric conflict relation. -/
theorem forest_fraction_le_conflict_bound {G : PhysicalGraph} (hG : G.IsConnected)
    (U : Finset G.Vertex) (F : Finset G.CycleWord) (hne : F.Nonempty)
    (hFU : ∀ C ∈ F, Cycle.vertices C ⊆ U)
    (D J : ℕ) (hD : ∀ C ∈ F, Cycle.length C ≤ D)
    (hc : ∀ C ∈ F, ∀ v ∈ Cycle.vertices C, G.degree v = 3)
    (v₀ : G.Vertex) (hv₀ : ∀ C ∈ F, v₀ ∉ Cycle.vertices C)
    (R : G.CycleWord → G.CycleWord → Prop) (hR : Symmetric R)
    (hdegree : ∀ C ∈ F, (F.filter (R C)).card ≤ J)
    (hgood : ∀ C ∈ F, ∀ C' ∈ F, C ≠ C' → ¬ R C C' →
      Disjoint (Cycle.vertices C) (Cycle.vertices C') ∧
      SafeCore.crossSize G (Cycle.vertices C) (Cycle.vertices C') = 0 ∧
      G.originalExteriorComponents (Cycle.vertices C ∪ Cycle.vertices C') + 1 =
        G.originalExteriorComponents (Cycle.vertices C) +
          G.originalExteriorComponents (Cycle.vertices C')) :
    G.originalForestFraction U ≤ (2 : ℝ) ^ D * (J + 1) / F.card := by
  obtain ⟨I, hIF, hIind, hcard⟩ := exists_large_independent R hR F J hdegree
  have hIne : I.Nonempty := by
    apply Finset.card_pos.1
    have hFpos := Finset.card_pos.2 hne
    by_contra hI
    have hz : I.card = 0 := by omega
    rw [hz, zero_mul] at hcard
    omega
  have hbound := forest_fraction_le_many hG U I hIne
    (fun C hC => hFU C (hIF hC)) D (fun C hC => hD C (hIF hC))
    (fun C hC => hc C (hIF hC)) v₀ (fun C hC => hv₀ C (hIF hC))
    (fun C hC C' hC' hCC' => hgood C (hIF hC) C' (hIF hC') hCC'
      (hIind C hC C' hC' hCC'))
  have hIp : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.2 hIne
  have hFp : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.2 hne
  have hcard' : (F.card : ℝ) ≤ (I.card : ℝ) * (J + 1) := by exact_mod_cast hcard
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ D := by positivity
  have hrat : (2 : ℝ) ^ D / I.card ≤ (2 : ℝ) ^ D * (J + 1) / F.card := by
    apply (div_le_div_iff₀ hIp hFp).2
    nlinarith [mul_le_mul_of_nonneg_left hcard' hpow]
  exact hbound.trans hrat

end Erdos1016.BoundaryDecay
