import Erdos1016.Probability.Cylinders.FeasibleSelection
import Erdos1016.Graph.Multigraph.EvenForest
import Erdos1016.Probability.Finite.Conditioning

set_option autoImplicit false

/-!
# Nonzero internal words on zero cuts

On the zero-cut subspace, restriction to a region is a surjective linear map
onto its actual internal cycle space. For disjoint regions the two restrictions
are jointly surjective. Thus requiring nonzero internal words multiplies the
single and joint zero-cut probabilities by the same internal factors.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.FiniteMultiGraph
open BoundaryTrace BoundaryDecay

local instance regionCycleDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Even words supported entirely on the actual internal edge labels. -/
def internalCycleSpace (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    Submodule F₂ G.CycleSpace where
  carrier := {x | ∀ e, e ∉ G.internalEdges U → x.1 e = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy e he; simp [hx e he, hy e he]
  smul_mem' := by intro a x hx e he; simp [hx e he]

/-- The actual zero-cut constraint, retaining all internal cycle coordinates. -/
def zeroCutSpace (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    Submodule F₂ G.CycleSpace := LinearMap.ker (G.observeEdges (G.cutEdges U))

theorem mem_zeroCutSpace_iff (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.CycleSpace) : x ∈ G.zeroCutSpace U ↔ ∀ e ∈ G.cutEdges U, x.1 e = 0 := by
  constructor
  · intro h e he
    exact congrFun h ⟨e, he⟩
  · intro h
    funext e
    exact h e.1 e.2

theorem internal_le_zeroCut (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    G.internalCycleSpace U ≤ G.zeroCutSpace U := by
  intro x hx
  rw [G.mem_zeroCutSpace_iff]
  intro e he
  apply hx e
  simp only [internalEdges, cutEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  tauto

theorem restrictInternal_boundary (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.CycleSpace) (hx : x ∈ G.zeroCutSpace U) :
    G.boundary (G.restrictEdges (G.internalEdges U) x.1) = 0 := by
  have hcut := (G.mem_zeroCutSpace_iff U x).mp hx
  funext v
  by_cases hv : v ∈ U
  · calc
      _ = G.boundary x.1 v := by
        change (∑ e : G.Edge, _) = ∑ e : G.Edge, _
        apply Finset.sum_congr rfl
        intro e he
        by_cases hs : G.src e ∈ U <;> by_cases hd : G.dst e ∈ U
        · simp [restrictEdges, internalEdges, hs, hd]
        · have hz := hcut e (by simp [cutEdges, hs, hd])
          simp [restrictEdges, internalEdges, hs, hd, hz]
        · have hz := hcut e (by simp [cutEdges, hs, hd])
          simp [restrictEdges, internalEdges, hs, hd, hz]
        · have hsv : G.src e ≠ v := by intro h; exact hs (h ▸ hv)
          have hdv : G.dst e ≠ v := by intro h; exact hd (h ▸ hv)
          simp [restrictEdges, internalEdges, hs, hd, hsv, hdv]
      _ = 0 := congrFun x.2 v
  · change (∑ e : G.Edge, _) = 0
    apply Finset.sum_eq_zero
    intro e he
    by_cases h : e ∈ G.internalEdges U
    · have hh := (Finset.mem_filter.mp h).2
      have hsv : G.src e ≠ v := by intro h; exact hv (h ▸ hh.1)
      have hdv : G.dst e ≠ v := by intro h; exact hv (h ▸ hh.2)
      simp [hsv, hdv]
    · simp [restrictEdges, h]

/-- Internal restriction is well-defined precisely on the zero-cut subspace. -/
def restrictInternal (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    G.zeroCutSpace U →ₗ[F₂] G.internalCycleSpace U where
  toFun x := ⟨⟨G.restrictEdges (G.internalEdges U) x.1.1,
      G.restrictInternal_boundary U x.1 x.2⟩, by
    intro e he
    simp [restrictEdges, he]⟩
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext; funext e
    change G.restrictEdges _ (x.1.1 + y.1.1) e =
      G.restrictEdges _ x.1.1 e + G.restrictEdges _ y.1.1 e
    simp only [restrictEdges, Pi.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    apply Subtype.ext; apply Subtype.ext; funext e
    change G.restrictEdges _ (a • x.1.1) e = a • G.restrictEdges _ x.1.1 e
    simp only [restrictEdges, Pi.smul_apply]
    split_ifs <;> simp

theorem restrictInternal_self (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.internalCycleSpace U) :
    G.restrictInternal U ⟨x.1, G.internal_le_zeroCut U x.2⟩ = x := by
  apply Subtype.ext; apply Subtype.ext; funext e
  change (if e ∈ G.internalEdges U then x.1.1 e else 0) = x.1.1 e
  split_ifs with he
  · rfl
  · exact (x.2 e he).symm

theorem restrictInternal_surjective (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    Function.Surjective (G.restrictInternal U) :=
  fun x => ⟨⟨x.1, G.internal_le_zeroCut U x.2⟩, G.restrictInternal_self U x⟩

/-- A zero cut accompanied by a nonzero internal even word. -/
def RegionCycleEvent (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.CycleSpace) : Prop :=
  x ∈ G.zeroCutSpace U ∧ G.restrictEdges (G.internalEdges U) x.1 ≠ 0

theorem regionCycleEvent_not_forest (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.CycleSpace) (hx : G.RegionCycleEvent U x) :
    ¬ G.IsForestWord (G.restrictEdges (G.internalEdges U) x.1) := by
  intro hf
  exact hx.2 (G.word_eq_zero_of_boundary_zero_of_forest _
    (G.restrictInternal_boundary U x hx.1) hf)

theorem restrictInternal_ne_zero_iff (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (x : G.zeroCutSpace U) :
    G.restrictInternal U x ≠ 0 ↔ G.restrictEdges (G.internalEdges U) x.1.1 ≠ 0 := by
  apply not_congr
  constructor
  · exact fun h => congrArg (fun z : G.internalCycleSpace U => z.1.1) h
  · intro h
    apply Subtype.ext; apply Subtype.ext
    exact h

/-- Fraction of nonzero words in the region's internal cycle space. -/
def internalCycleFactor (G : FiniteMultiGraph) (U : Finset G.Vertex) : ℝ :=
  1 - 1 / (Fintype.card (G.internalCycleSpace U) : ℝ)

theorem regionCycleEvent_density (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    Finite.density (G.RegionCycleEvent U) = G.internalCycleFactor U *
      Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) := by
  unfold RegionCycleEvent
  rw [Finite.density_and_eq_density_subtype]
  have he : (fun x : G.zeroCutSpace U =>
      G.restrictEdges (G.internalEdges U) x.1.1 ≠ 0) =
      fun x => G.restrictInternal U x ≠ 0 := by
    funext x
    exact propext (G.restrictInternal_ne_zero_iff U x).symm
  rw [he, density_surjective_linear (G.restrictInternal U)
    (G.restrictInternal_surjective U) (fun y => y ≠ 0), Finite.density_ne_zero]
  exact mul_comm _ _

theorem internal_vanish_on_disjoint (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) (x : G.internalCycleSpace U)
    (e : G.Edge) (he : e ∈ G.internalEdges V) : x.1.1 e = 0 := by
  apply x.2 e
  intro hu
  exact (Finset.disjoint_left.mp hUV) (Finset.mem_filter.mp hu).2.1
    (Finset.mem_filter.mp he).2.1

theorem internal_le_zeroCut_disjoint (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) : G.internalCycleSpace U ≤ G.zeroCutSpace V := by
  intro x hx
  rw [G.mem_zeroCutSpace_iff]
  intro e he
  apply hx e
  intro hu
  have hu' := (Finset.mem_filter.mp hu).2
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact (Finset.disjoint_left.mp hUV) hu'.1 h.1
  · exact (Finset.disjoint_left.mp hUV) hu'.2 h.2

/-- On two zero cuts, both internal restrictions are jointly uniform. -/
def restrictInternalPair (G : FiniteMultiGraph) (U V : Finset G.Vertex) :
    ↥(G.zeroCutSpace U ⊓ G.zeroCutSpace V) →ₗ[F₂]
      (G.internalCycleSpace U × G.internalCycleSpace V) :=
  ((G.restrictInternal U).comp (Submodule.inclusion inf_le_left)).prod
    ((G.restrictInternal V).comp (Submodule.inclusion inf_le_right))

theorem restrictInternalPair_surjective (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) : Function.Surjective (G.restrictInternalPair U V) := by
  rintro ⟨a, b⟩
  have haU := G.internal_le_zeroCut U a.2
  have hbV := G.internal_le_zeroCut V b.2
  have haV := G.internal_le_zeroCut_disjoint U V hUV a.2
  have hbU := G.internal_le_zeroCut_disjoint V U hUV.symm b.2
  refine ⟨⟨a.1 + b.1, (G.zeroCutSpace U).add_mem haU hbU,
    (G.zeroCutSpace V).add_mem haV hbV⟩, ?_⟩
  apply Prod.ext
  · apply Subtype.ext; apply Subtype.ext; funext e
    change (if e ∈ G.internalEdges U then a.1.1 e + b.1.1 e else 0) = a.1.1 e
    by_cases he : e ∈ G.internalEdges U
    · simp [he, G.internal_vanish_on_disjoint V U hUV.symm b e he]
    · simp [he, a.2 e he]
  · apply Subtype.ext; apply Subtype.ext; funext e
    change (if e ∈ G.internalEdges V then a.1.1 e + b.1.1 e else 0) = b.1.1 e
    by_cases he : e ∈ G.internalEdges V
    · simp [he, G.internal_vanish_on_disjoint U V hUV a e he]
    · simp [he, b.2 e he]

/-- The same two internal factors occur in the joint law. They therefore
cancel exactly from the correlation ratio. -/
theorem regionCycleEvent_pair_density (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) :
    Finite.density (fun x => G.RegionCycleEvent U x ∧ G.RegionCycleEvent V x) =
      G.internalCycleFactor U * G.internalCycleFactor V *
        Finite.density (fun x : G.CycleSpace =>
          x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V) := by
  have he : (fun x => G.RegionCycleEvent U x ∧ G.RegionCycleEvent V x) =
      fun x : G.CycleSpace => x ∈ G.zeroCutSpace U ⊓ G.zeroCutSpace V ∧
        (G.restrictEdges (G.internalEdges U) x.1 ≠ 0 ∧
         G.restrictEdges (G.internalEdges V) x.1 ≠ 0) := by
    funext x
    apply propext
    simp only [RegionCycleEvent, Submodule.mem_inf]
    tauto
  rw [he, Finite.density_and_eq_density_subtype]
  have hrestr : (fun x : ↥(G.zeroCutSpace U ⊓ G.zeroCutSpace V) =>
      G.restrictEdges (G.internalEdges U) x.1.1 ≠ 0 ∧
      G.restrictEdges (G.internalEdges V) x.1.1 ≠ 0) =
      fun x => (G.restrictInternalPair U V x).1 ≠ 0 ∧
        (G.restrictInternalPair U V x).2 ≠ 0 := by
    funext x
    exact propext (and_congr (G.restrictInternal_ne_zero_iff U ⟨x.1, x.2.1⟩).symm
      (G.restrictInternal_ne_zero_iff V ⟨x.1, x.2.2⟩).symm)
  rw [hrestr, density_surjective_linear (G.restrictInternalPair U V)
    (G.restrictInternalPair_surjective U V hUV) (fun y => y.1 ≠ 0 ∧ y.2 ≠ 0),
    Finite.density_prod_and (fun a : G.internalCycleSpace U => a ≠ 0)
      (fun b : G.internalCycleSpace V => b ≠ 0),
    Finite.density_ne_zero, Finite.density_ne_zero]
  change _ = (1 - 1 / _) * (1 - 1 / _) * _
  have hpred : (Membership.mem (G.zeroCutSpace U ⊓ G.zeroCutSpace V) : G.CycleSpace → Prop) =
      fun x => x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V := rfl
  rw [hpred]
  ring

theorem internalCycleFactor_nonneg (G : FiniteMultiGraph) (U : Finset G.Vertex) :
    0 ≤ G.internalCycleFactor U := by
  have h := Finite.density_nonneg (fun x : G.internalCycleSpace U => x ≠ 0)
  simpa only [Finite.density_ne_zero, internalCycleFactor] using h

theorem internalCycleFactor_ge_half (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (hcyc : ∃ x : G.internalCycleSpace U, x ≠ 0) :
    (1 / 2 : ℝ) ≤ G.internalCycleFactor U := by
  obtain ⟨x, hx⟩ := hcyc
  have hcard : 2 ≤ Fintype.card (G.internalCycleSpace U) := by
    have hsub : ({0, x} : Finset (G.internalCycleSpace U)).card ≤
        Fintype.card (G.internalCycleSpace U) := Finset.card_le_univ _
    simpa [hx, hx.symm] using hsub
  have hr : (2 : ℝ) ≤ Fintype.card (G.internalCycleSpace U) := by exact_mod_cast hcard
  have hdiv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hr
  unfold internalCycleFactor
  linarith

/-- A cyclic region with at most `d` cut edges has event probability at least
`2^(-d-1)`, including all internal and exterior cycles. -/
theorem regionCycleEvent_probability_ge (G : FiniteMultiGraph) (U : Finset G.Vertex)
    (hcyc : ∃ x : G.internalCycleSpace U, x ≠ 0) (d : ℕ)
    (hcut : (G.cutEdges U).card ≤ d) :
    1 / (2 : ℝ) ^ (d + 1) ≤ Finite.density (G.RegionCycleEvent U) := by
  have hzero : 1 / (2 : ℝ) ^ d ≤
      Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) := by
    have he : (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) =
        fun x => ∀ e ∈ G.cutEdges U, x.1 e = 0 := by
      funext x
      exact propext (G.mem_zeroCutSpace_iff U x)
    rw [he]
    exact (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcut)).trans
        (G.zeroCoordinates_probability_ge (G.cutEdges U))
  rw [G.regionCycleEvent_density]
  have h := mul_le_mul (G.internalCycleFactor_ge_half U hcyc) hzero
    (by positivity) (G.internalCycleFactor_nonneg U)
  calc
    _ = (1 / 2 : ℝ) * (1 / (2 : ℝ) ^ d) := by rw [pow_succ]; ring
    _ ≤ _ := h

/-- Multiplying by independent internal factors preserves every zero-cut
correlation upper bound. -/
theorem regionCycleEvent_pair_le (G : FiniteMultiGraph) (U V : Finset G.Vertex)
    (hUV : Disjoint U V) (a : ℝ)
    (hcut : Finite.density (fun x : G.CycleSpace =>
      x ∈ G.zeroCutSpace U ∧ x ∈ G.zeroCutSpace V) ≤
        a * Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace U) *
          Finite.density (fun x : G.CycleSpace => x ∈ G.zeroCutSpace V)) :
    Finite.density (fun x => G.RegionCycleEvent U x ∧ G.RegionCycleEvent V x) ≤
      a * Finite.density (G.RegionCycleEvent U) * Finite.density (G.RegionCycleEvent V) := by
  rw [G.regionCycleEvent_pair_density U V hUV, G.regionCycleEvent_density U,
    G.regionCycleEvent_density V]
  have h := mul_le_mul_of_nonneg_left hcut
    (mul_nonneg (G.internalCycleFactor_nonneg U) (G.internalCycleFactor_nonneg V))
  nlinarith only [h]

end Erdos1016.FiniteMultiGraph
