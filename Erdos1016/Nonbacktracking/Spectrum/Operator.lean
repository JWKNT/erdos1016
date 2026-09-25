import Mathlib.Data.Matrix.Mul
import Erdos1016.Decomposition.Regions.Cuts

set_option autoImplicit false

/-!
# The actual finite nonbacktracking operator

Darts are an individually labelled physical edge and an orientation bit.
No quotient, suppressed graph or high-degree apex is introduced. The operator
is proved equal to the 0/1 nonbacktracking transition matrix.
-/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance operatorDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Dart (G : PhysicalGraph) := G.Edge × Bool

def tail (G : PhysicalGraph) (d : Dart G) : G.Vertex :=
  if d.2 then G.src d.1 else G.dst d.1

def head (G : PhysicalGraph) (d : Dart G) : G.Vertex :=
  if d.2 then G.dst d.1 else G.src d.1

def reverse (G : PhysicalGraph) (d : Dart G) : Dart G := (d.1, !d.2)

@[simp] theorem reverse_reverse (G : PhysicalGraph) (d : Dart G) :
    reverse G (reverse G d) = d := by cases d with | mk e b => cases b <;> rfl

@[simp] theorem tail_reverse (G : PhysicalGraph) (d : Dart G) :
    tail G (reverse G d) = head G d := by cases d with | mk e b => cases b <;> rfl

@[simp] theorem head_reverse (G : PhysicalGraph) (d : Dart G) :
    head G (reverse G d) = tail G d := by cases d with | mk e b => cases b <;> rfl

def reverseEquiv (G : PhysicalGraph) : Dart G ≃ Dart G where
  toFun := reverse G
  invFun := reverse G
  left_inv := reverse_reverse G
  right_inv := reverse_reverse G

@[simp] theorem card_dart (G : PhysicalGraph) : Fintype.card (Dart G) = 2 * G.edgeCount := by
  simp [Dart, Nat.mul_comm]

def Next (G : PhysicalGraph) (d e : Dart G) : Prop :=
  head G d = tail G e ∧ e ≠ reverse G d

theorem next_reverse (G : PhysicalGraph) (d e : Dart G) :
    Next G d e ↔ Next G (reverse G e) (reverse G d) := by
  simp only [Next, head_reverse, tail_reverse, reverse_reverse]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, Ne.symm hn⟩
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, Ne.symm hn⟩

/-- The 0/1 dart matrix works over any semiring, including natural counts. -/
def matrix {K : Type*} [Semiring K] (G : PhysicalGraph) :
    Matrix (Dart G) (Dart G) K :=
  fun d e => if Next G d e then 1 else 0

section Algebra
variable {K : Type*} [CommRing K]

/-- Sum of a dart function on darts leaving an actual vertex. -/
def outgoing (G : PhysicalGraph) (f : Dart G → K) (v : G.Vertex) : K :=
  ∑ d, if tail G d = v then f d else 0

/-- Head-forward convention, exactly the source convention. -/
def step (G : PhysicalGraph) (f : Dart G → K) (d : Dart G) : K :=
  outgoing G f (head G d) - f (reverse G d)

@[simp] theorem outgoing_zero (G : PhysicalGraph) (v : G.Vertex) :
    outgoing G (fun _ => (0 : K)) v = 0 := by simp [outgoing]



theorem outgoing_sub (G : PhysicalGraph) (f g : Dart G → K) (v : G.Vertex) :
    outgoing G (fun d => f d - g d) v = outgoing G f v - outgoing G g v := by
  simp only [outgoing, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

theorem outgoing_mul (G : PhysicalGraph) (a : K) (f : Dart G → K) (v : G.Vertex) :
    outgoing G (fun d => a * f d) v = a * outgoing G f v := by
  simp only [outgoing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- Each actual incidence corresponds to exactly one outgoing orientation. -/
theorem outgoing_one (G : PhysicalGraph) (v : G.Vertex) :
    outgoing G (fun _ => (1 : K)) v = (G.degree v : K) := by
  have h := congrArg (fun n : ℕ => (n : K)) (SafeCore.degree_eq_endpoint_sum G v)
  push_cast at h
  rw [h]
  unfold outgoing
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  have hterm :
      (∑ b : Bool, if tail G (e, b) = v then (1 : K) else 0) =
        (if G.src e = v then 1 else 0) + (if G.dst e = v then 1 else 0) := by
    rw [Fintype.sum_bool]
    simp [tail]
  exact hterm

theorem outgoing_const (G : PhysicalGraph) (a : K) (v : G.Vertex) :
    outgoing G (fun _ => a) v = (G.degree v : K) * a := by
  have h := outgoing_mul G a (fun _ => (1 : K)) v
  simpa only [mul_one, outgoing_one, mul_comm] using h

theorem outgoing_tail (G : PhysicalGraph) (s : G.Vertex → K) (v : G.Vertex) :
    outgoing G (fun d => s (tail G d)) v = (G.degree v : K) * s v := by
  calc
    _ = outgoing G (fun _ => s v) v := by
      unfold outgoing
      apply Finset.sum_congr rfl
      intro d _
      by_cases h : tail G d = v <;> simp [h]
    _ = _ := outgoing_const G (s v) v

/-- Reversal accounts for exactly the one forbidden backtrack. -/
theorem step_eq_sum_next (G : PhysicalGraph) (f : Dart G → K) (d : Dart G) :
    step G f d = ∑ e, if Next G d e then f e else 0 := by
  have hsplit : outgoing G f (head G d) =
      (∑ e, if Next G d e then f e else 0) + f (reverse G d) := by
    have hterm (e : Dart G) :
        (if tail G e = head G d then f e else 0) =
        (if Next G d e then f e else 0) +
        (if e = reverse G d then f e else 0) := by
      by_cases he : e = reverse G d
      · subst e
        simp [Next]
      · by_cases ht : tail G e = head G d
        · rw [if_pos ht, if_pos ⟨ht.symm, he⟩, if_neg he]
          simp
        · rw [if_neg ht]
          have hnot : ¬ Next G d e := fun h => ht h.1.symm
          rw [if_neg hnot, if_neg he]
          simp
    unfold outgoing
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp
  unfold step
  rw [hsplit]
  abel

/-- The matrix used later really acts on the individually labelled darts. -/
theorem matrix_mulVec (G : PhysicalGraph) (f : Dart G → K) :
    (matrix G).mulVec f = step G f := by
  funext d
  rw [step_eq_sum_next]
  simp [Matrix.mulVec, dotProduct, matrix, ite_mul]

def adjacency (G : PhysicalGraph) (s : G.Vertex → K) (u : G.Vertex) : K :=
  outgoing G (fun d => s (head G d)) u

/-- Endpoint incidence sums, with every physical edge counted exactly twice. -/
theorem sum_heads (G : PhysicalGraph) (f : G.Vertex → K) :
    (∑ d : Dart G, f (head G d)) = ∑ v, (G.degree v : K) * f v := by
  have hswap : (∑ v : G.Vertex, outgoing G (fun d => f (tail G d)) v) =
      ∑ d : Dart G, f (tail G d) := by
    unfold outgoing
    rw [Finset.sum_comm]
    simp
  simp_rw [outgoing_tail] at hswap
  rw [hswap]
  apply Fintype.sum_equiv (reverseEquiv G)
  intro d
  simp [reverseEquiv]

end Algebra
end Erdos1016.Nonbacktracking
