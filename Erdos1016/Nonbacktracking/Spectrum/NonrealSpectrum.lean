import Mathlib.Analysis.Complex.Basic
import Erdos1016.Nonbacktracking.Spectrum.Operator

set_option autoImplicit false

/-!
# The nonreal nonbacktracking spectrum is bounded by sqrt(2)

Source Lemma 5.1, the quadratic eigenvector argument. The theorem is for the
actual operator, not a supplied polynomial or supplied spectral bound.
Perron existence, entropy growth, and the trace/multiplicity step are separate
remaining obligations; they are NOT assumed as hypotheses of this lemma.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance nonrealSpectrumDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Nonzero right eigenvector of the literal dart operator. -/
def IsEigenvector (G : PhysicalGraph) (z : ℂ) (f : Dart G → ℂ) : Prop :=
  f ≠ 0 ∧ ∀ d, step G f d = z * f d

theorem eigen_edge_equation (G : PhysicalGraph) {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) (d : Dart G) :
    z * f d + f (reverse G d) = outgoing G f (head G d) := by
  have h := hf.2 d
  unfold step at h
  linear_combination -h

theorem eigen_edge_solved (G : PhysicalGraph) {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) (d : Dart G) :
    (z ^ 2 - 1) * f d =
      z * outgoing G f (head G d) - outgoing G f (tail G d) := by
  have hd := eigen_edge_equation G hf d
  have hr := eigen_edge_equation G hf (reverse G d)
  simp only [reverse_reverse, head_reverse] at hr
  linear_combination z * hd - hr

theorem eigen_vertex_quadratic (G : PhysicalGraph) {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) (u : G.Vertex) :
    z ^ 2 * outgoing G f u - z * adjacency G (outgoing G f) u +
      ((G.degree u : ℂ) - 1) * outgoing G f u = 0 := by
  have hall : (fun d => (z ^ 2 - 1) * f d) =
      (fun d => z * outgoing G f (head G d) - outgoing G f (tail G d)) :=
    funext (eigen_edge_solved G hf)
  have hsum := congrArg (fun a : Dart G → ℂ => outgoing G a u) hall
  change outgoing G (fun d => (z ^ 2 - 1) * f d) u =
    outgoing G (fun d => z * outgoing G f (head G d) -
      outgoing G f (tail G d)) u at hsum
  rw [outgoing_mul, outgoing_sub, outgoing_mul, outgoing_tail] at hsum
  change (z ^ 2 - 1) * outgoing G f u =
    z * adjacency G (outgoing G f) u - (G.degree u : ℂ) * outgoing G f u at hsum
  linear_combination hsum

theorem outgoing_ne_zero_of_nonreal (G : PhysicalGraph) {z : ℂ}
    {f : Dart G → ℂ} (hf : IsEigenvector G z f) (hz : z.im ≠ 0) :
    outgoing G f ≠ 0 := by
  have hz1 : z ≠ 1 := by intro h; apply hz; simp [h]
  have hzm : z ≠ -1 := by intro h; apply hz; simp [h]
  have hprod : z ^ 2 - 1 ≠ 0 := by
    have h₁ : z - 1 ≠ 0 := sub_ne_zero.2 hz1
    have h₂ : z + 1 ≠ 0 := by
      intro h
      apply hzm
      linear_combination h
    have h := mul_ne_zero h₁ h₂
    convert h using 1 <;> ring
  intro hs
  apply hf.1
  funext d
  have h := eigen_edge_solved G hf d
  rw [hs] at h
  simp only [Pi.zero_apply, mul_zero, sub_zero] at h
  exact (mul_eq_zero.1 h).resolve_left hprod

private theorem conjugate_pair (a b : ℂ) :
    star a * b + star b * a = (2 * (star a * b).re : ℝ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

def mass (G : PhysicalGraph) (s : G.Vertex → ℂ) : ℝ :=
  ∑ u, Complex.normSq (s u)

def adjacencyForm (G : PhysicalGraph) (s : G.Vertex → ℂ) : ℝ :=
  ∑ e, 2 * (star (s (G.src e)) * s (G.dst e)).re

def excessForm (G : PhysicalGraph) (s : G.Vertex → ℂ) : ℝ :=
  ∑ u, ((G.degree u : ℝ) - 1) * Complex.normSq (s u)

theorem mass_pos (G : PhysicalGraph) (s : G.Vertex → ℂ) (hs : s ≠ 0) :
    0 < mass G s := by
  have hex : ∃ u, s u ≠ 0 := by
    by_contra h
    apply hs
    funext u
    by_contra hu
    exact h ⟨u, hu⟩
  obtain ⟨u, hu⟩ := hex
  have hle : Complex.normSq (s u) ≤ mass G s :=
    Finset.single_le_sum (fun v _ => Complex.normSq_nonneg (s v)) (Finset.mem_univ u)
  exact (Complex.normSq_pos.2 hu).trans_le hle

theorem mass_cast (G : PhysicalGraph) (s : G.Vertex → ℂ) :
    (mass G s : ℂ) = ∑ u, star (s u) * s u := by
  unfold mass
  push_cast
  apply Finset.sum_congr rfl
  intro u _
  exact Complex.normSq_eq_conj_mul_self

/-- Reality is obtained by pairing the two directions of each physical edge. -/
theorem adjacencyForm_cast (G : PhysicalGraph) (s : G.Vertex → ℂ) :
    (adjacencyForm G s : ℂ) = ∑ u, star (s u) * adjacency G s u := by
  have hswap : (∑ u, star (s u) * adjacency G s u) =
      ∑ d : Dart G, star (s (tail G d)) * s (head G d) := by
    unfold adjacency outgoing
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    simp
  rw [hswap, Fintype.sum_prod_type]
  unfold adjacencyForm
  push_cast
  apply Finset.sum_congr rfl
  intro e _
  simpa [tail, head, Fintype.sum_bool] using
    (conjugate_pair (s (G.src e)) (s (G.dst e))).symm

theorem excessForm_cast (G : PhysicalGraph) (s : G.Vertex → ℂ) :
    (excessForm G s : ℂ) =
      ∑ u, ((G.degree u : ℂ) - 1) * (star (s u) * s u) := by
  unfold excessForm
  push_cast
  apply Finset.sum_congr rfl
  intro u _
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem excessForm_le_two_mass (G : PhysicalGraph) (s : G.Vertex → ℂ)
    (hdeg : ∀ u, G.degree u ≤ 3) : excessForm G s ≤ 2 * mass G s := by
  unfold excessForm mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg (s u))
  have h : (G.degree u : ℝ) ≤ 3 := by exact_mod_cast hdeg u
  linarith

/-- The graph eigenvector gives a genuine real-coefficient quadratic. -/
theorem eigen_scalar_quadratic (G : PhysicalGraph) {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) :
    (mass G (outgoing G f) : ℂ) * z ^ 2 -
      (adjacencyForm G (outgoing G f) : ℂ) * z +
      (excessForm G (outgoing G f) : ℂ) = 0 := by
  let s := outgoing G f
  rw [mass_cast, adjacencyForm_cast, excessForm_cast,
    Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro u _
  have h := eigen_vertex_quadratic G hf u
  change z ^ 2 * s u - z * adjacency G s u +
    ((G.degree u : ℂ) - 1) * s u = 0 at h
  linear_combination star (s u) * h

/-- Elementary real/imaginary part calculation, without selecting a quadratic root. -/
theorem nonreal_quadratic_normSq_le_two
    {α β γ : ℝ} {z : ℂ} (hα : 0 < α) (hz : z.im ≠ 0)
    (hγ : γ ≤ 2 * α)
    (heq : (α : ℂ) * z ^ 2 - (β : ℂ) * z + (γ : ℂ) = 0) :
    Complex.normSq z ≤ 2 := by
  have hi := congrArg Complex.im heq
  have hr := congrArg Complex.re heq
  simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
    Complex.add_re, Complex.sub_re, Complex.zero_re, mul_zero, zero_mul,
    add_zero, sub_zero, zero_sub] at hi hr
  have hf : (2 * α * z.re - β) * z.im = 0 := by nlinarith only [hi]
  have hβ : β = 2 * α * z.re := by
    have h := (mul_eq_zero.1 hf).resolve_right hz
    linarith
  rw [hβ] at hr
  have hn : α * Complex.normSq z = γ := by
    change α * (z.re * z.re + z.im * z.im) = γ
    nlinarith only [hr]
  apply (mul_le_mul_left hα).1
  rw [hn]
  nlinarith [hγ]

/-- SOURCE LEMMA 5.1, nonreal part. No min-degree or connectedness hypothesis
is needed for this bound. The owner's degree bound is essential: this lemma
is never applied to the high-degree boundary apex. -/
theorem nonreal_nonbacktracking_normSq_le_two (G : PhysicalGraph)
    (hdeg : ∀ u, G.degree u ≤ 3) {z : ℂ} {f : Dart G → ℂ}
    (hf : IsEigenvector G z f) (hz : z.im ≠ 0) :
    Complex.normSq z ≤ 2 := by
  exact nonreal_quadratic_normSq_le_two
    (mass_pos G _ (outgoing_ne_zero_of_nonreal G hf hz)) hz
    (excessForm_le_two_mass G _ hdeg) (eigen_scalar_quadratic G hf)

end Erdos1016.Nonbacktracking
