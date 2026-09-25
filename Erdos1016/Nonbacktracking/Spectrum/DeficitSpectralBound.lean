import Erdos1016.Nonbacktracking.Spectrum.NonrealSpectrum
import Erdos1016.Nonbacktracking.Spectrum.DeficitContinuity

set_option autoImplicit false

/-! The positive nonbacktracking eigenvalue obtained from the full cubic
 degree deficit. Leaves, isolated vertices, and disconnected graphs are
 permitted; no minimum-degree hypothesis is imposed. -/

noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance deficitDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The ordinary undirected adjacency matrix, with the two incidences of
 each physical edge recorded explicitly. -/
def vertexAdjacencyMatrix (G : PhysicalGraph) : Matrix G.Vertex G.Vertex ℝ :=
  fun v w => ∑ e : G.Edge,
    ((if G.src e = v ∧ G.dst e = w then 1 else 0) +
      (if G.dst e = v ∧ G.src e = w then 1 else 0))

/-- The real sum of all deficits from cubic degree. -/
def degreeDeficit (G : PhysicalGraph) : ℝ :=
  ∑ v, (3 - (G.degree v : ℝ))

/-- The vertex matrix polynomial whose nontrivial roots lift to the dart
 nonbacktracking operator. -/
def deficitMatrix (G : PhysicalGraph) (t : ℝ) : Matrix G.Vertex G.Vertex ℝ :=
  Matrix.diagonal (fun v => t ^ 2 + (G.degree v : ℝ) - 1) -
    t • vertexAdjacencyMatrix G

theorem vertexAdjacencyMatrix_mulVec (G : PhysicalGraph) (u : G.Vertex → ℝ) :
    (vertexAdjacencyMatrix G).mulVec u = adjacency G u := by
  funext v
  unfold vertexAdjacencyMatrix Matrix.mulVec dotProduct adjacency outgoing
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_bool, tail, head,
    Bool.false_eq_true, ↓reduceIte, if_true]
  simp only [ite_mul, one_mul, zero_mul]
  by_cases hs : G.src e = v <;> by_cases hd : G.dst e = v <;>
    simp [hs, hd, add_comm]

theorem vertexAdjacencyMatrix_isHermitian (G : PhysicalGraph) :
    (vertexAdjacencyMatrix G).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro v w
  simp only [star_trivial, vertexAdjacencyMatrix]
  apply Finset.sum_congr rfl
  intro e _
  simp only [and_comm]
  ring

theorem deficitMatrix_mulVec (G : PhysicalGraph) (t : ℝ) (u : G.Vertex → ℝ) :
    (deficitMatrix G t).mulVec u =
      fun v => t ^ 2 * u v - t * adjacency G u v +
        ((G.degree v : ℝ) - 1) * u v := by
  unfold deficitMatrix
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, vertexAdjacencyMatrix_mulVec]
  funext v
  simp only [Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem deficitMatrix_isHermitian (G : PhysicalGraph) (t : ℝ) :
    (deficitMatrix G t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro v w
  have h := (vertexAdjacencyMatrix_isHermitian G).apply v w
  simp only [star_trivial] at h ⊢
  simp only [deficitMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h]
  congr 1
  by_cases hvw : v = w
  · subst w; rfl
  · simp [Matrix.diagonal_apply, hvw, Ne.symm hvw]

theorem deficitMatrix_continuous (G : PhysicalGraph) :
    Continuous (deficitMatrix G) := by
  apply continuous_pi
  intro v
  apply continuous_pi
  intro w
  simp only [deficitMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem degreeDeficit_nonneg (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) : 0 ≤ degreeDeficit G := by
  apply Finset.sum_nonneg
  intro v _
  have h : (G.degree v : ℝ) ≤ 3 := by exact_mod_cast hmax v
  linarith

private theorem degree_square_sum (G : PhysicalGraph) (u : G.Vertex → ℝ) :
    (∑ v, (G.degree v : ℝ) * (u v) ^ 2) =
      ∑ e : G.Edge, ((u (G.src e)) ^ 2 + (u (G.dst e)) ^ 2) := by
  rw [← sum_heads G (fun v => (u v) ^ 2), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp [Fintype.sum_bool, head, add_comm]

private theorem adjacency_quadratic (G : PhysicalGraph) (u : G.Vertex → ℝ) :
    (∑ v, u v * adjacency G u v) =
      ∑ e : G.Edge, 2 * u (G.src e) * u (G.dst e) := by
  unfold adjacency outgoing
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool, head, tail, Bool.false_eq_true, ↓reduceIte, if_true,
    Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

/-- The full deficit agrees with the natural deficit when degrees are at
 most three. -/
theorem degreeDeficit_eq_nat_sum (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) :
    degreeDeficit G = ((∑ v, (3 - G.degree v) : ℕ) : ℝ) := by
  unfold degreeDeficit
  push_cast
  apply Finset.sum_congr rfl
  intro v _
  rw [Nat.cast_sub (hmax v)]
  norm_num

/-- Handshaking expressed in the full cubic deficit. -/
theorem degreeDeficit_eq_counts (G : PhysicalGraph) :
    degreeDeficit G = 3 * (G.vertexCount : ℝ) - 2 * G.edgeCount := by
  have h := degree_square_sum G (fun _ => 1)
  simp only [one_pow, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, PhysicalGraph.Edge, Fintype.card_fin] at h
  norm_num at h
  unfold degreeDeficit
  rw [Finset.sum_sub_distrib, h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    PhysicalGraph.Vertex, Fintype.card_fin]
  ring

/-- At t=2 the quadratic form is twice the graph's Dirichlet energy plus
 the nonnegative degree-deficit diagonal. -/
theorem deficitMatrix_two_quadratic (G : PhysicalGraph) (u : G.Vertex → ℝ) :
    dotProduct u ((deficitMatrix G 2).mulVec u) =
      2 * ∑ e : G.Edge, (u (G.src e) - u (G.dst e)) ^ 2 +
        ∑ v, (3 - (G.degree v : ℝ)) * (u v) ^ 2 := by
  rw [deficitMatrix_mulVec]
  unfold dotProduct
  have hterm (v : G.Vertex) :
      u v * ((2 : ℝ) ^ 2 * u v - 2 * adjacency G u v +
        ((G.degree v : ℝ) - 1) * u v) =
      2 * ((G.degree v : ℝ) * (u v) ^ 2) -
        2 * (u v * adjacency G u v) +
        (3 - (G.degree v : ℝ)) * (u v) ^ 2 := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, degree_square_sum, adjacency_quadratic]
  congr 1
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem deficitMatrix_two_posSemidef (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) : (deficitMatrix G 2).PosSemidef := by
  refine ⟨deficitMatrix_isHermitian G 2, ?_⟩
  intro u
  simp only [star_trivial, deficitMatrix_two_quadratic]
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro v _
    have h : (G.degree v : ℝ) ≤ 3 := by exact_mod_cast hmax v
    exact mul_nonneg (sub_nonneg.mpr h) (sq_nonneg _)

/-- The constant-vector Rayleigh value is exactly the polynomial used in
 the deficit argument, including vertices of degree zero or one. -/
theorem deficitMatrix_constant_quadratic (G : PhysicalGraph) (t : ℝ) :
    dotProduct (fun _ : G.Vertex => (1 : ℝ))
      ((deficitMatrix G t).mulVec (fun _ => 1)) =
      (t - 1) * ((G.vertexCount : ℝ) * (t - 2) + degreeDeficit G) := by
  rw [deficitMatrix_mulVec]
  have hadj (v : G.Vertex) : adjacency G (fun _ => (1 : ℝ)) v = G.degree v :=
    outgoing_one G v
  simp_rw [hadj, dotProduct, one_mul, mul_one]
  unfold degreeDeficit
  have hterm (v : G.Vertex) :
      t ^ 2 - t * (G.degree v : ℝ) + ((G.degree v : ℝ) - 1) =
      (t - 1) * (t - 2) + (t - 1) * (3 - (G.degree v : ℝ)) := by ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    PhysicalGraph.Vertex, Fintype.card_fin]
  ring

/-- The vertex-to-dart lift associated with the quadratic pencil. -/
def quadraticEigenLift (G : PhysicalGraph) (z : ℂ) (u : G.Vertex → ℂ) :
    Dart G → ℂ := fun d => z * u (head G d) - u (tail G d)

theorem quadraticEigenLift_outgoing (G : PhysicalGraph) (z : ℂ)
    (u : G.Vertex → ℂ) (v : G.Vertex) :
    outgoing G (quadraticEigenLift G z u) v =
      z * adjacency G u v - (G.degree v : ℂ) * u v := by
  exact (outgoing_sub G _ _ v).trans (by
    rw [outgoing_mul, outgoing_tail]
    rfl)

/-- A nontrivial root of the actual vertex pencil gives an actual dart
 eigenvector. This argument also covers isolated vertices. -/
theorem isEigenvector_quadraticEigenLift (G : PhysicalGraph) (z : ℂ)
    (u : G.Vertex → ℂ) (hu : u ≠ 0) (hz : z ^ 2 - 1 ≠ 0)
    (hq : ∀ v, z ^ 2 * u v - z * adjacency G u v +
      ((G.degree v : ℂ) - 1) * u v = 0) :
    IsEigenvector G z (quadraticEigenLift G z u) := by
  constructor
  · intro hf
    apply hu
    funext v
    have hzero : outgoing G (quadraticEigenLift G z u) v = 0 := by
      rw [hf]
      exact outgoing_zero G v
    rw [quadraticEigenLift_outgoing] at hzero
    have heq : (z ^ 2 - 1) * u v = 0 := by
      linear_combination hq v + hzero
    exact (mul_eq_zero.mp heq).resolve_left hz
  · intro d
    unfold step
    rw [quadraticEigenLift_outgoing]
    simp only [quadraticEigenLift, head_reverse, tail_reverse]
    linear_combination -(hq (head G d))

private theorem adjacency_ofReal (G : PhysicalGraph) (u : G.Vertex → ℝ)
    (v : G.Vertex) :
    adjacency G (fun w => (u w : ℂ)) v = (adjacency (K := ℝ) G u v : ℂ) := by
  unfold adjacency outgoing
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- Every singular graph pencil parameter greater than one is a real
 nonbacktracking eigenvalue, with an explicitly constructed eigenvector. -/
theorem exists_eigenvector_of_deficitMatrix_kernel (G : PhysicalGraph)
    {t : ℝ} (ht : 1 < t) {u : G.Vertex → ℝ} (hu : u ≠ 0)
    (hker : (deficitMatrix G t).mulVec u = 0) :
    ∃ f : Dart G → ℂ, IsEigenvector G (t : ℂ) f := by
  refine ⟨quadraticEigenLift G (t : ℂ) (fun v => (u v : ℂ)),
    isEigenvector_quadraticEigenLift G (t : ℂ) _ ?_ ?_ ?_⟩
  · intro h
    apply hu
    funext v
    have hv := congrFun h v
    change (u v : ℂ) = 0 at hv
    change u v = 0
    exact_mod_cast hv
  · intro h
    have hr : t ^ 2 - 1 = 0 := by exact_mod_cast h
    nlinarith
  · intro v
    have hv := congrFun hker v
    rw [deficitMatrix_mulVec] at hv
    change t ^ 2 * u v - t * adjacency G u v +
      ((G.degree v : ℝ) - 1) * u v = 0 at hv
    rw [adjacency_ofReal]
    exact_mod_cast hv

/-- Deficit lower bound for an actual positive real nonbacktracking
 eigenvalue. Neither minimum degree nor connectedness is required. -/
theorem exists_real_eigenvector_ge_two_sub_deficit (G : PhysicalGraph)
    (hmax : ∀ v, G.degree v ≤ 3) (hn : 0 < G.vertexCount)
    (hd : degreeDeficit G < G.vertexCount) :
    ∃ t : ℝ, 2 - degreeDeficit G / G.vertexCount ≤ t ∧ t ≤ 2 ∧
      1 < t ∧ ∃ f : Dart G → ℂ, IsEigenvector G (t : ℂ) f := by
  let a : ℝ := 2 - degreeDeficit G / G.vertexCount
  have hnR : 0 < (G.vertexCount : ℝ) := by exact_mod_cast hn
  have ha2 : a ≤ 2 := by
    dsimp [a]
    exact sub_le_self _ (div_nonneg (degreeDeficit_nonneg G hmax) hnR.le)
  have ha1 : 1 < a := by
    have hdiv : degreeDeficit G / G.vertexCount < 1 :=
      (div_lt_one hnR).mpr hd
    dsimp [a]
    linarith
  have hone : (fun _ : G.Vertex => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h (⟨0, hn⟩ : G.Vertex)
    norm_num at this
  have htest : dotProduct (fun _ : G.Vertex => (1 : ℝ))
      ((deficitMatrix G a).mulVec (fun _ => 1)) ≤ 0 := by
    rw [deficitMatrix_constant_quadratic]
    dsimp [a]
    have hnne : (G.vertexCount : ℝ) ≠ 0 := hnR.ne'
    have hz : (G.vertexCount : ℝ) *
        (2 - degreeDeficit G / G.vertexCount - 2) + degreeDeficit G = 0 := by
      field_simp
      ring
    rw [hz, mul_zero]
  obtain ⟨t, ht, u, hu, hker⟩ := exists_kernel_on_continuous_symmetric_path
    (deficitMatrix G) (deficitMatrix_continuous G) (deficitMatrix_isHermitian G)
    ha2 (deficitMatrix_two_posSemidef G hmax) (fun _ => 1) hone htest
  have ht1 : 1 < t := ha1.trans_le ht.1
  exact ⟨t, ht.1, ht.2, ht1, exists_eigenvector_of_deficitMatrix_kernel G ht1 hu hker⟩

end Erdos1016.Nonbacktracking
