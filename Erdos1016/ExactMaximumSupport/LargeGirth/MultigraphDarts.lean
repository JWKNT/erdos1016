import Erdos1016.ExactMaximumSupport.LargeGirth.WeightedRuns
import Erdos1016.ExactMaximum.Cycles

set_option autoImplicit false

/-!
# Labelled nonbacktracking darts of cubic multigraphs

A loop has two distinct orientations. Only the reverse orientation is
excluded at a transition. Thus loops and parallel labels require no
simplicity assumption in the binary-run count.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.LargeGirth.MultigraphDarts

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (G : FiniteMultiGraph)

abbrev Dart := G.Edge × Bool

def tail (d : Dart G) : G.Vertex := if d.2 then G.src d.1 else G.dst d.1
def head (d : Dart G) : G.Vertex := if d.2 then G.dst d.1 else G.src d.1
def reverse (d : Dart G) : Dart G := (d.1, !d.2)

@[simp] theorem reverse_reverse (d : Dart G) : reverse G (reverse G d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

@[simp] theorem tail_reverse (d : Dart G) : tail G (reverse G d) = head G d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

@[simp] theorem head_reverse (d : Dart G) : head G (reverse G d) = tail G d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

def reverseEquiv : Dart G ≃ Dart G where
  toFun := reverse G
  invFun := reverse G
  left_inv := reverse_reverse G
  right_inv := reverse_reverse G

@[simp] theorem card_dart : Fintype.card (Dart G) = 2 * G.edgeCount := by
  simp [Dart, Nat.mul_comm]

def Next (d e : Dart G) : Prop := head G d = tail G e ∧ e ≠ reverse G d

theorem next_reverse (d e : Dart G) :
    Next G d e ↔ Next G (reverse G e) (reverse G d) := by
  simp only [Next, head_reverse, tail_reverse, reverse_reverse]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, hn.symm⟩
  · rintro ⟨h, hn⟩
    exact ⟨h.symm, hn.symm⟩

def outgoing (v : G.Vertex) : Finset (Dart G) := Finset.univ.filter fun d => tail G d = v

theorem outgoing_card (v : G.Vertex) : (outgoing G v).card = G.degree v := by
  unfold outgoing
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  change (∑ e : G.Edge, ∑ b : Bool, if tail G (e, b) = v then 1 else 0) =
    G.selectedDegree (fun _ => 1) v
  rw [G.selectedDegree_eq_sum_endpoints]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  simp [tail, Nat.add_comm]

theorem successors_eq_erase (d : Dart G) :
    Finset.univ.filter (Next G d) = (outgoing G (head G d)).erase (reverse G d) := by
  ext e
  simp [Next, outgoing, and_comm, eq_comm]

theorem successors_card (d : Dart G) :
    Fintype.card {e // Next G d e} = G.degree (head G d) - 1 := by
  rw [Fintype.card_subtype, successors_eq_erase, Finset.card_erase_of_mem]
  · rw [outgoing_card]
  · simp [outgoing]

def predecessorEquiv (e : Dart G) : {d // Next G d e} ≃
    {d // Next G (reverse G e) d} where
  toFun d := ⟨reverse G d.1, (next_reverse G d.1 e).1 d.2⟩
  invFun d := ⟨reverse G d.1, by
    have h := (next_reverse G (reverse G e) d.1).1 d.2
    simpa only [reverse_reverse] using h⟩
  left_inv d := by apply Subtype.ext; exact reverse_reverse G d.1
  right_inv d := by apply Subtype.ext; exact reverse_reverse G d.1

theorem predecessors_card (e : Dart G) :
    Fintype.card {d // Next G d e} = G.degree (tail G e) - 1 := by
  rw [Fintype.card_congr (predecessorEquiv G e), successors_card, head_reverse]

/-- Cubic incidence degree gives two successors and two predecessors, even at loops. -/
def binarySystem (hcub : G.IsCubic) : WeightedRuns.BinarySystem (Dart G) where
  next := Next G
  row_card d := by rw [successors_card, hcub]
  column_card d := by rw [predecessors_card, hcub]

theorem cubic_run_count (hcub : G.IsCubic) (k : ℕ) :
    Fintype.card ((binarySystem G hcub).AllRuns k) = 2 * G.edgeCount * 2 ^ k := by
  rw [WeightedRuns.BinarySystem.card_allRuns, card_dart]

theorem cubic_run_total_weight (hcub : G.IsCubic) (w : G.Edge → ℕ) (k : ℕ) :
    (binarySystem G hcub).totalCost (fun d => w d.1) k =
      2 ^ k * (k + 1) * (2 * ∑ e, w e) := by
  rw [WeightedRuns.BinarySystem.totalCost_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool, Finset.sum_add_distrib, two_mul]

end Erdos1016.ExactMaximumSupport.LargeGirth.MultigraphDarts
