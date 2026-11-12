import Erdos1016.ExactMaximumSupport.LargeGirth.PoleProductWords
import Erdos1016.ExactMaximumSupport.LargeGirth.AffinePole
import Erdos1016.ExactMaximumSupport.Product

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The product bound for actual induced poles

Restriction of an ambient even word gives a demand supported on the induced
pole ports. The exact affine law is proved from labelled word transport.
Two disjoint induced poles then force the ambient forest probability below 2/5.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
open FiniteMultiGraph PieceCore.Induced Probability.PoleMarker

local instance poleProductLawDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph) (X : Finset G.Vertex)

/-- Incidence counts in the induced graph retain both incidences of a loop. -/
theorem induced_degree_sum (v : (graph G X).Vertex) :
    (graph G X).degree v = ∑ e ∈ G.internalEdges X,
      ((if G.src e = vertex G X v then 1 else 0) +
       (if G.dst e = vertex G X v then 1 else 0)) := by
  unfold degree
  rw [(graph G X).selectedDegree_eq_sum_endpoints, ← sum_edges]
  apply Finset.sum_congr rfl
  intro e _
  change (if (1 : F₂) ≠ 0 then
    (if (graph G X).src e = v then 1 else 0) + (if (graph G X).dst e = v then 1 else 0)
    else 0) = _
  rw [if_pos (show (1 : F₂) ≠ 0 from one_ne_zero), ← vertex_src, ← vertex_dst]
  simp only [(vertex_injective G X).eq_iff]

/-- A cubic induced vertex has no omitted incident label in a subcubic ambient graph. -/
theorem incident_internal_of_cubic (hmax : ∀ v, G.degree v ≤ 3)
    (v : (graph G X).Vertex) (hv : (graph G X).degree v = 3)
    (e : G.Edge) (he : G.src e = vertex G X v ∨ G.dst e = vertex G X v) :
    e ∈ G.internalEdges X := by
  by_contra hout
  let f : G.Edge → ℕ := fun e =>
    (if G.src e = vertex G X v then 1 else 0) +
    (if G.dst e = vertex G X v then 1 else 0)
  have hf : 0 < f e := by rcases he with he | he <;> simp [f,he]
  have hs : ∑ e ∈ G.internalEdges X, f e < ∑ e : G.Edge, f e :=
    Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ e) hout hf
      (fun _ _ _ => Nat.zero_le _)
  have hind : (graph G X).degree v = ∑ e ∈ G.internalEdges X, f e := induced_degree_sum G X v
  have hamb : G.degree (vertex G X v) = ∑ e : G.Edge, f e := by
    unfold degree
    rw [G.selectedDegree_eq_sum_endpoints]
    simp [f]
  rw [← hind, ← hamb, hv] at hs
  exact (hmax _).not_lt hs

/-- The actual demand induced by an ambient even word. -/
def inducedDemand (x : G.CycleSpace) : (graph G X).Demand :=
  (graph G X).boundary (projectWord G X x.1)

theorem inducedDemand_zero_at_cubic (hmax : ∀ v, G.degree v ≤ 3)
    (x : G.CycleSpace) (v : (graph G X).Vertex) (hv : (graph G X).degree v = 3) :
    inducedDemand G X x v = 0 := by
  unfold inducedDemand
  rw [← boundary_extend_at, extend_project]
  calc
    _ = G.boundary x.1 (vertex G X v) := by
      change (∑ e : G.Edge, _) = ∑ e : G.Edge, _
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : G.src e = vertex G X v ∨ G.dst e = vertex G X v
      · have hm := incident_internal_of_cubic G X hmax v hv e he
        simp [restrictEdges, hm]
      · push_neg at he
        simp [he.1, he.2]
    _ = 0 := congrFun x.2 _

/-- The internal shifts and the complete induced parity fiber have the same law. -/
theorem internal_affine_forest_density (x : G.CycleSpace) :
    Finite.density (fun z : G.internalCycleSpace X =>
      G.IsForestWord (G.restrictEdges (G.internalEdges X) (x.1 + z.1.1))) =
      affineForestProbability (graph G X) (inducedDemand G X x) := by
  let base : Parity.Fiber (graph G X).boundary (inducedDemand G X x) :=
    ⟨projectWord G X x.1, rfl⟩
  let e : Parity.Fiber (graph G X).boundary (inducedDemand G X x) ≃ G.internalCycleSpace X :=
    (Parity.fiberEquivKernel (graph G X).boundary base).trans (cycleEquiv G X).toEquiv
  have hw (z : G.internalCycleSpace X) :
      extendWord G X (e.symm z).1 = G.restrictEdges (G.internalEdges X) (x.1+z.1.1) := by
    change extendWord G X (projectWord G X z.1.1 + projectWord G X x.1) = _
    rw [← map_add, add_comm z.1.1 x.1, extend_project]
  apply Finite.density_equiv e.symm
  intro z
  rw [← forest_extend_iff, hw]

/-- Supported-demand bounds on an actual induced graph supply the precise
per-shift hypothesis used by the existing product theorem. -/
theorem internal_affine_bound (hmax : ∀ v, G.degree v ≤ 3) (a : ℝ)
    (hbound : ∀ b : (graph G X).Demand,
      (∀ v, (graph G X).degree v = 3 → b v = 0) →
      affineForestProbability (graph G X) b ≤ a) :
    ∀ x : G.CycleSpace, Finite.density (fun z : G.internalCycleSpace X =>
      G.IsForestWord (G.restrictEdges (G.internalEdges X) (x.1 + z.1.1))) ≤ a := by
  intro x
  rw [internal_affine_forest_density]
  exact hbound _ (inducedDemand_zero_at_cubic G X hmax x)

/-- Two disjoint labelled induced poles multiply, including adjacent poles. -/
theorem forest_density_le_nine_twenty_fifths (hmax : ∀ v, G.degree v ≤ 3)
    (U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (E : Finset G.Edge) (hE₁ : G.internalEdges U₁ ⊆ E) (hE₂ : G.internalEdges U₂ ⊆ E)
    (h₁ : ∀ b : (graph G U₁).Demand,
      (∀ v, (graph G U₁).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₁) b ≤ (3/5:ℝ))
    (h₂ : ∀ b : (graph G U₂).Demand,
      (∀ v, (graph G U₂).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₂) b ≤ (3/5:ℝ)) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) ≤ 9/25 := by
  have hh := PolynomialBound.Product.forest_density_le_mul G U₁ U₂ hdisj E hE₁ hE₂
    (3/5) (3/5) (internal_affine_bound G U₁ hmax _ h₁) (internal_affine_bound G U₂ hmax _ h₂)
  norm_num at hh ⊢
  exact hh

theorem forest_density_lt_two_fifths (hmax : ∀ v, G.degree v ≤ 3)
    (U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (E : Finset G.Edge) (hE₁ : G.internalEdges U₁ ⊆ E) (hE₂ : G.internalEdges U₂ ⊆ E)
    (h₁ : ∀ b : (graph G U₁).Demand,
      (∀ v, (graph G U₁).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₁) b ≤ (3/5:ℝ))
    (h₂ : ∀ b : (graph G U₂).Demand,
      (∀ v, (graph G U₂).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₂) b ≤ (3/5:ℝ)) :
    Finite.density (fun x : G.CycleSpace => G.IsForestWord (G.restrictEdges E x.1)) < 2/5 := by
  have hh := forest_density_le_nine_twenty_fifths G hmax U₁ U₂ hdisj E hE₁ hE₂ h₁ h₂
  linarith


theorem region_density_eq (R : Finset G.Vertex) :
    G.regionForestProbability R = Finite.density (fun x : G.CycleSpace =>
      G.IsForestWord (G.restrictEdges (G.internalEdges R) x.1)) := by
  simp only [regionForestProbability, Finite.density, Finite.count, G.cycleSpace_card,
    Nat.cast_pow, Nat.cast_ofNat, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- The ambient forest probability outside the marker is at most 9/25.
No assumption about connectedness of the common complement is needed. -/
theorem region_product (hmax : ∀ v, G.degree v ≤ 3)
    (P U₁ U₂ : Finset G.Vertex) (hdisj : Disjoint U₁ U₂)
    (hU₁ : U₁ ⊆ Pᶜ) (hU₂ : U₂ ⊆ Pᶜ)
    (h₁ : ∀ b : (graph G U₁).Demand,
      (∀ v, (graph G U₁).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₁) b ≤ (3/5:ℝ))
    (h₂ : ∀ b : (graph G U₂).Demand,
      (∀ v, (graph G U₂).degree v = 3 → b v = 0) →
      affineForestProbability (graph G U₂) b ≤ (3/5:ℝ)) :
    G.regionForestProbability Pᶜ ≤ 9/25 ∧ G.regionForestProbability Pᶜ < 2/5 := by
  have hE (U : Finset G.Vertex) (hU : U ⊆ Pᶜ) :
      G.internalEdges U ⊆ G.internalEdges Pᶜ := by
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hU hh.1, hU hh.2⟩
  rw [region_density_eq]
  exact ⟨forest_density_le_nine_twenty_fifths G hmax U₁ U₂ hdisj _ (hE U₁ hU₁) (hE U₂ hU₂) h₁ h₂,
    forest_density_lt_two_fifths G hmax U₁ U₂ hdisj _ (hE U₁ hU₁) (hE U₂ hU₂) h₁ h₂⟩

/-- Full numerical application to two actual induced poles. All local affine
hypotheses are discharged by the proved large-girth pole theorem. -/
theorem exists_two_pole_constants :
    ∃ D : ℕ, ∃ C : ℝ, 256 ≤ D ∧ 0 < C ∧
    ∀ (G : FiniteMultiGraph) (P : Finset G.Vertex) (U : Fin 2 → Finset G.Vertex)
      (g : Fin 2 → ℕ), (∀ v, G.degree v ≤ 3) →
      Disjoint (U 0) (U 1) → (∀ i, U i ⊆ Pᶜ) →
      (∀ i, (graph G (U i)).toSimpleGraph.Connected) →
      (∀ i v, 2 ≤ (graph G (U i)).degree v) →
      (∀ i, ¬ (graph G (U i)).HasCycleShorterThan (g i)) →
      (∀ i, (256 ≤ (graph G (U i)).cycleRank ∧
          (graph G (U i)).cubicDeficit ≤ 4*g i ∧ D ≤ g i) ∨
        ∃ l : ℝ, 4 ≤ l ∧ l ≤ (graph G (U i)).cycleRank ∧
          ((graph G (U i)).cubicDeficit : ℝ) ≤ 2*l ∧ C*Real.logb 2 (l+2) ≤ g i) →
      G.regionForestProbability Pᶜ ≤ 9/25 ∧ G.regionForestProbability Pᶜ < 2/5 := by
  obtain ⟨D, C, hD, hC, hAffine⟩ := AffinePole.exists_constants_real
  refine ⟨D, C, hD, hC, ?_⟩
  intro G P U g hmax hdisj hU hconn hmin hshort hcase
  have hlocal (i : Fin 2) : ∀ b : (graph G (U i)).Demand,
      (∀ v, (graph G (U i)).degree v = 3 → b v = 0) →
      affineForestProbability (graph G (U i)) b ≤ (3/5:ℝ) := by
    apply hAffine (graph G (U i)) (g i) (hconn i) (hmin i)
    · intro v
      exact (degree_le G (U i) v).trans (hmax _)
    · exact hshort i
    · exact hcase i
  exact region_product G hmax P (U 0) (U 1) hdisj (hU 0) (hU 1) (hlocal 0) (hlocal 1)

end Erdos1016.ExactMaximumSupport.LargeGirth.PoleProduct
