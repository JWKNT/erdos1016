import Erdos1016.Cycles.Selection.ProtectedPacking

set_option autoImplicit false

/-!
# Expansion transfers to the literal boundary-average apex

Every old edge remains present with its own physical label. The extra apex
may have arbitrarily high degree. This is a finite cut proof, not a spectral
comparison. The harmless explicit h <= 2 hypothesis holds for the normalized
h <= 1 used in manuscript §9.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay BoundaryTrace
local instance cycleSupplyApexExpansionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (H : PhysicalGraph)

def coreVertexLift (v : H.Vertex) : (coreApexGraph H).Vertex :=
  Fintype.equivFin (H.Vertex ⊕ Unit) (Sum.inl v)

def coreEdgeLift (e : H.Edge) : (coreApexGraph H).Edge :=
  Fintype.equivFin (H.Edge ⊕ CorePin H) (Sum.inl e)

def apexSpoke (p : CorePin H) : (coreApexGraph H).Edge :=
  Fintype.equivFin (H.Edge ⊕ CorePin H) (Sum.inr p)

theorem coreVertexLift_injective : Function.Injective (coreVertexLift H) := by
  intro u v h
  exact Sum.inl.inj ((Fintype.equivFin (H.Vertex ⊕ Unit)).injective h)

theorem coreEdgeLift_injective : Function.Injective (coreEdgeLift H) := by
  intro e f h
  exact Sum.inl.inj ((Fintype.equivFin (H.Edge ⊕ CorePin H)).injective h)

@[simp] theorem coreEdgeLift_src (e : H.Edge) :
    (coreApexGraph H).src (coreEdgeLift H e) = coreVertexLift H (H.src e) := by
  simp [coreApexGraph, physicalize, coreEdgeLift, coreVertexLift,
    coreApexNetwork, Ported.apex, corePorts, PhysicalGraph.traceNetwork]

@[simp] theorem coreEdgeLift_dst (e : H.Edge) :
    (coreApexGraph H).dst (coreEdgeLift H e) = coreVertexLift H (H.dst e) := by
  simp [coreApexGraph, physicalize, coreEdgeLift, coreVertexLift,
    coreApexNetwork, Ported.apex, corePorts, PhysicalGraph.traceNetwork]

@[simp] theorem apexSpoke_src (p : CorePin H) :
    (coreApexGraph H).src (apexSpoke H p) = coreVertexLift H p.1 := by
  simp [coreApexGraph, physicalize, apexSpoke, coreVertexLift,
    coreApexNetwork, Ported.apex, corePorts]

@[simp] theorem apexSpoke_dst (p : CorePin H) :
    (coreApexGraph H).dst (apexSpoke H p) = coreApexVertex H := by
  simp [coreApexGraph, physicalize, apexSpoke, coreApexVertex,
    coreApexNetwork, Ported.apex, corePorts]

@[simp] theorem apex_order : (coreApexGraph H).vertexCount = H.vertexCount + 1 := by
  simp [coreApexGraph, physicalize, Fintype.card_sum, PhysicalGraph.Vertex]

theorem coreVertex_ne_apex (v : H.Vertex) : coreVertexLift H v ≠ coreApexVertex H := by
  intro h
  have he := (Fintype.equivFin (H.Vertex ⊕ Unit)).injective h
  exact Sum.noConfusion he

theorem apex_vertex_cases (v : (coreApexGraph H).Vertex) :
    (∃ u : H.Vertex, coreVertexLift H u = v) ∨ v = coreApexVertex H := by
  have h := (Fintype.equivFin (H.Vertex ⊕ Unit)).apply_symm_apply v
  cases he : (Fintype.equivFin (H.Vertex ⊕ Unit)).symm v with
  | inl u =>
      left
      exact ⟨u, by simpa only [he, coreVertexLift] using h⟩
  | inr u =>
      cases u
      right
      have h' : coreApexVertex H = v := by
        simpa only [he, coreApexVertex] using h
      exact h'.symm

def coreShore (S : Finset (coreApexGraph H).Vertex) : Finset H.Vertex :=
  Finset.univ.filter fun v => coreVertexLift H v ∈ S

@[simp] theorem mem_coreShore (S : Finset (coreApexGraph H).Vertex) (v : H.Vertex) :
    v ∈ coreShore H S ↔ coreVertexLift H v ∈ S := by simp [coreShore]

theorem apex_free_shore_image (S : Finset (coreApexGraph H).Vertex)
    (hz : coreApexVertex H ∉ S) : (coreShore H S).image (coreVertexLift H) = S := by
  ext v
  constructor
  · rintro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    exact (mem_coreShore H S u).1 hu
  · intro hv
    rcases apex_vertex_cases H v with ⟨u, rfl⟩ | rfl
    · exact Finset.mem_image.2 ⟨u, (mem_coreShore H S u).2 hv, rfl⟩
    · exact False.elim (hz hv)

theorem apex_free_shore_card (S : Finset (coreApexGraph H).Vertex)
    (hz : coreApexVertex H ∉ S) : (coreShore H S).card = S.card := by
  have hcard := congrArg Finset.card (apex_free_shore_image H S hz)
  rw [Finset.card_image_of_injective _ (coreVertexLift_injective H)] at hcard
  exact hcard

/-- The cut in H injects into the cut in Q by its original edge labels. -/
theorem core_cut_le_apex_cut (S : Finset (coreApexGraph H).Vertex) :
    cutSize H (coreShore H S) ≤ cutSize (coreApexGraph H) S := by
  have hmap : ∀ e ∈ ownerCut H (coreShore H S),
      coreEdgeLift H e ∈ ownerCut (coreApexGraph H) S := by
    intro e he
    rw [mem_ownerCut] at he ⊢
    simpa only [coreEdgeLift_src, coreEdgeLift_dst, mem_coreShore] using he
  let f : {e // e ∈ ownerCut H (coreShore H S)} →
      {e // e ∈ ownerCut (coreApexGraph H) S} := fun e => ⟨coreEdgeLift H e.1, hmap e.1 e.2⟩
  have hf : Function.Injective f := by
    intro e d he
    apply Subtype.ext
    exact coreEdgeLift_injective H (congrArg Subtype.val he)
  simpa only [cutSize, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- A proper nonempty old shore pays at most a factor two in its smaller-side
order when one apex is added. -/
theorem apex_smaller_side_le_twice (S : Finset (coreApexGraph H).Vertex)
    (hz : coreApexVertex H ∉ S) (hA : (coreShore H S).Nonempty)
    (hAc : (coreShore H S)ᶜ.Nonempty) :
    min S.card Sᶜ.card ≤ 2 * min (coreShore H S).card (coreShore H S)ᶜ.card := by
  have he := apex_free_shore_card H S hz
  have hH := card_compl_add H (coreShore H S)
  have hQ := card_compl_add (coreApexGraph H) S
  have hQ' : S.card + Sᶜ.card = H.vertexCount + 1 := by
    simpa only [apex_order] using hQ
  have hpos := Finset.card_pos.2 hAc
  rcases le_total (coreShore H S).card (coreShore H S)ᶜ.card with h | h
  · rw [min_eq_left h]
    have hm := Nat.min_le_left S.card Sᶜ.card
    omega
  · rw [min_eq_right h]
    have hm := Nat.min_le_right S.card Sᶜ.card
    omega

private theorem apex_free_cut_expansion
    (h : ℝ) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hExp : HasExpansion H Finset.univ h) (p₀ : CorePin H)
    (S : Finset (coreApexGraph H).Vertex) (hz : coreApexVertex H ∉ S) :
    h / 2 * (min S.card Sᶜ.card : ℕ) ≤ (cutSize (coreApexGraph H) S : ℝ) := by
  by_cases hA : (coreShore H S).Nonempty
  · by_cases hAc : (coreShore H S)ᶜ.Nonempty
    · have hmin := apex_smaller_side_le_twice H S hz hA hAc
      have hmin' : ((min S.card Sᶜ.card : ℕ) : ℝ) ≤
          2 * ((min (coreShore H S).card (coreShore H S)ᶜ.card : ℕ) : ℝ) := by
        exact_mod_cast hmin
      have hbase := hExp (coreShore H S) (Finset.subset_univ _)
      rw [relativeCut_univ, ← Finset.compl_eq_univ_sdiff (coreShore H S)] at hbase
      have hc : (cutSize H (coreShore H S) : ℝ) ≤ cutSize (coreApexGraph H) S := by
        exact_mod_cast core_cut_le_apex_cut H S
      have hmul := mul_le_mul_of_nonneg_left hmin' (div_nonneg hh (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith
    · have he : coreShore H S = Finset.univ := by
        have hempty := Finset.not_nonempty_iff_eq_empty.1 hAc
        ext v
        simp only [Finset.mem_univ, iff_true]
        by_contra hv
        have hc := Finset.mem_compl.2 hv
        simpa only [hempty, Finset.not_mem_empty] using hc
      have hcard : Sᶜ.card = 1 := by
        have hs := apex_free_shore_card H S hz
        have ht := card_compl_add (coreApexGraph H) S
        have hs' : H.vertexCount = S.card := by
          simpa only [he, Finset.card_univ, Fintype.card_fin] using hs
        have ht' : S.card + Sᶜ.card = H.vertexCount + 1 := by
          simpa only [apex_order] using ht
        omega
      have hpin : coreVertexLift H p₀.1 ∈ S := by
        apply (mem_coreShore H S p₀.1).1
        rw [he]
        exact Finset.mem_univ _
      have hed : apexSpoke H p₀ ∈ ownerCut (coreApexGraph H) S := by
        rw [mem_ownerCut, apexSpoke_src, apexSpoke_dst]
        exact Or.inl ⟨hpin, hz⟩
      have hcutNat : 1 ≤ cutSize (coreApexGraph H) S := by
        have hp : 0 < (ownerCut (coreApexGraph H) S).card :=
          Finset.card_pos.2 ⟨apexSpoke H p₀, hed⟩
        change 1 ≤ (ownerCut (coreApexGraph H) S).card
        omega
      have hcut : (1 : ℝ) ≤ cutSize (coreApexGraph H) S := by
        exact_mod_cast hcutNat
      have hm : ((min S.card Sᶜ.card : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast (show min S.card Sᶜ.card ≤ 1 by rw [hcard]; exact Nat.min_le_right _ _)
      have hmul := mul_le_mul_of_nonneg_left hm (div_nonneg hh (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith
  · have he := Finset.not_nonempty_iff_eq_empty.1 hA
    have hs : S = ∅ := by
      rw [← apex_free_shore_image H S hz, he, Finset.image_empty]
    rw [hs, Finset.card_empty, Nat.zero_min, Nat.cast_zero, mul_zero]
    positivity

/-- Source Lemma 3.1 for the normalized expansion range, including the one-pin
case where the apex is a leaf. -/
theorem coreApex_hasExpansion (h : ℝ) (hh : 0 ≤ h) (hh2 : h ≤ 2)
    (hExp : HasExpansion H Finset.univ h) (p₀ : CorePin H) :
  HasExpansion (coreApexGraph H) Finset.univ (h / 2) := by
  intro S _
  rw [relativeCut_univ, ← Finset.compl_eq_univ_sdiff S]
  by_cases hz : coreApexVertex H ∈ S
  · have hb := apex_free_cut_expansion H h hh hh2 hExp p₀ Sᶜ (by simpa using hz)
    simpa only [compl_compl, cutSize_compl, min_comm] using hb
  · exact apex_free_cut_expansion H h hh hh2 hExp p₀ S hz

end Erdos1016.CycleSupply
