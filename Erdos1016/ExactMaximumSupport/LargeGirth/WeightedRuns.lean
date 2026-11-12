import Mathlib

set_option autoImplicit false

/-!
# Additive weights on finite binary runs

Each state has two successors and two predecessors. The statements count
actual finite runs and their total weight. They do not assume a graph,
girth, or a correspondence between runs and paths.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximumSupport.LargeGirth.WeightedRuns

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {ι : Type} [Fintype ι]

/-- At least half the states have cost at most twice the given exact mean. -/
theorem half_cost_bound {Ω : Type} [Fintype Ω] (c : Ω → ℕ) (n B : ℕ)
    (hmean : n * (∑ x, c x) = Fintype.card Ω * B) :
    Fintype.card Ω ≤ 2 * (Finset.univ.filter fun x => n * c x ≤ 2 * B).card := by
  classical
  let good := Finset.univ.filter fun x => n * c x ≤ 2 * B
  let bad := Finset.univ.filter fun x => ¬ n * c x ≤ 2 * B
  have hsplit : good.card + bad.card = Fintype.card Ω := by
    exact Finset.filter_card_add_filter_neg_card_eq_card (fun x => n * c x ≤ 2 * B)
  have hbound : bad.card * (2 * B + 1) ≤ Fintype.card Ω * B := by
    calc
      _ = ∑ _x ∈ bad, (2 * B + 1) := by simp
      _ ≤ ∑ x ∈ bad, n * c x := by
        apply Finset.sum_le_sum
        intro x hx
        have h := (Finset.mem_filter.mp hx).2
        omega
      _ ≤ ∑ x, n * c x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = _ := by rw [← Finset.mul_sum, hmean]
  have hhalf : 2 * bad.card ≤ Fintype.card Ω := by
    by_contra hn
    have hgap : Fintype.card Ω + 1 ≤ 2 * bad.card := by omega
    have hpos : 1 ≤ bad.card := by omega
    have hmul := Nat.mul_le_mul_right B hgap
    nlinarith
  change Fintype.card Ω ≤ 2 * good.card
  omega

structure BinarySystem (ι : Type) [Fintype ι] where
  next : ι → ι → Prop
  row_card : ∀ i, Fintype.card {j // next i j} = 2
  column_card : ∀ j, Fintype.card {i // next i j} = 2

namespace BinarySystem

variable (S : BinarySystem ι)

/-- A run has `k` transitions and `k+1` visited states. -/
def Run : ℕ → ι → Type _
  | 0, _ => Unit
  | k + 1, i => Σ j : {j // S.next i j}, Run k j.1

instance runFintype : (k : ℕ) → (i : ι) → Fintype (S.Run k i)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | k + 1, i => by
    change Fintype (Σ j : {j // S.next i j}, S.Run k j.1)
    letI : ∀ j : {j // S.next i j}, Fintype (S.Run k j.1) := fun j => runFintype k j.1
    infer_instance

theorem card_run (k : ℕ) (i : ι) : Fintype.card (S.Run k i) = 2 ^ k := by
  induction k generalizing i with
  | zero => change Fintype.card Unit = 2 ^ 0; simp
  | succ k ih =>
    have he : Fintype.card (S.Run (k + 1) i) =
        ∑ j : {j // S.next i j}, Fintype.card (S.Run k j.1) := by
      change Fintype.card (Σ j : {j // S.next i j}, S.Run k j.1) = _
      exact Fintype.card_sigma
    rw [he]
    simp [ih, S.row_card, pow_succ, Nat.mul_comm]

abbrev AllRuns (k : ℕ) := Σ i : ι, S.Run k i

def states : (k : ℕ) → (i : ι) → S.Run k i → List ι
  | 0, i, _ => [i]
  | k + 1, i, r => i :: states k r.1.1 r.2

@[simp] theorem states_length (k : ℕ) (i : ι) (r : S.Run k i) :
    (S.states k i r).length = k + 1 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [states, ih]

@[simp] theorem states_head (k : ℕ) (i : ι) (r : S.Run k i) :
    (S.states k i r).head? = some i := by cases k <;> rfl

theorem states_chain (k : ℕ) (i : ι) (r : S.Run k i) :
    List.Chain' S.next (S.states k i r) := by
  induction k generalizing i with
  | zero => simp [states]
  | succ k ih =>
    have ht := ih r.1.1 r.2
    have hn := r.1.2
    cases k <;> simpa only [states, List.chain'_cons, List.chain'_singleton,
      and_true] using And.intro hn ht

theorem states_injective (k : ℕ) :
    Function.Injective (fun r : S.AllRuns k => S.states k r.1 r.2) := by
  induction k with
  | zero =>
    rintro ⟨i, r⟩ ⟨j, s⟩ he
    have hij : i = j := by simpa [states] using he
    subst j
    cases r
    cases s
    rfl
  | succ k ih =>
    rintro ⟨i, ⟨j, r⟩⟩ ⟨i', ⟨j', r'⟩⟩ he
    have heq := List.cons.inj he
    have hii : i = i' := heq.1
    subst i'
    have ht : (⟨j.1, r⟩ : S.AllRuns k) = ⟨j'.1, r'⟩ := ih heq.2
    rcases j with ⟨j, hj⟩
    rcases j' with ⟨j', hj'⟩
    cases ht
    rfl

theorem card_allRuns (k : ℕ) : Fintype.card (S.AllRuns k) = Fintype.card ι * 2 ^ k := by
  rw [Fintype.card_sigma]
  simp [S.card_run]

/-- Sum the weight of every visited state, including the first state. -/
def cost (w : ι → ℕ) : (k : ℕ) → (i : ι) → S.Run k i → ℕ
  | 0, i, _ => w i
  | k + 1, i, r => w i + cost w k r.1.1 r.2

def totalCost (w : ι → ℕ) (k : ℕ) : ℕ :=
  ∑ i, ∑ r : S.Run k i, S.cost w k i r

theorem sum_successors (f : ι → ℕ) :
    (∑ i, ∑ j : {j // S.next i j}, f j.1) = 2 * ∑ j, f j := by
  have he (i : ι) : (∑ j : {j // S.next i j}, f j.1) =
      ∑ j, if S.next i j then f j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (S.next i)) (by intro j; simp),
      Finset.sum_filter]
  simp_rw [he]
  rw [Finset.sum_comm]
  have he' (i j : ι) : (if S.next i j then f j else 0) =
      (if S.next i j then 1 else 0) * f j := by split_ifs <;> simp
  simp_rw [he', ← Finset.sum_mul]
  have hc (j : ι) : (∑ i, if S.next i j then 1 else 0) = 2 := by
    simpa only [Fintype.card_subtype, Finset.sum_boole] using S.column_card j
  simp_rw [hc]
  rw [Finset.mul_sum]

theorem totalCost_succ (w : ι → ℕ) (k : ℕ) :
    S.totalCost w (k + 1) = 2 ^ (k + 1) * (∑ i, w i) + 2 * S.totalCost w k := by
  have hrow (i : ι) :
      (∑ r : S.Run (k + 1) i, S.cost w (k + 1) i r) =
        2 ^ (k + 1) * w i +
          ∑ j : {j // S.next i j}, ∑ r : S.Run k j.1, S.cost w k j.1 r := by
    change (∑ r : (Σ j : {j // S.next i j}, S.Run k j.1),
      (w i + S.cost w k r.1.1 r.2)) = _
    have hc : Fintype.card (Σ j : {j // S.next i j}, S.Run k j.1) = 2 ^ (k + 1) :=
      S.card_run (k + 1) i
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, hc]
    congr 1
    exact Fintype.sum_sigma _
  unfold totalCost
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  exact S.sum_successors (fun j => ∑ r : S.Run k j, S.cost w k j r)

/-- Uniform starting states make every position uniform, as an exact integer identity. -/
theorem totalCost_eq (w : ι → ℕ) (k : ℕ) :
    S.totalCost w k = 2 ^ k * (k + 1) * ∑ i, w i := by
  induction k with
  | zero => simp [totalCost, cost, Run]
  | succ k ih =>
    rw [S.totalCost_succ, ih, pow_succ]
    ring

/-- At least half of the actual runs have cost at most twice their exact mean. -/
theorem half_runs_low_cost (w : ι → ℕ) (k : ℕ) :
    Fintype.card (S.AllRuns k) ≤
      2 * (Finset.univ.filter fun r : S.AllRuns k =>
        Fintype.card ι * S.cost w k r.1 r.2 ≤ 2 * (k + 1) * ∑ i, w i).card := by
  have hm : Fintype.card ι * (∑ r : S.AllRuns k, S.cost w k r.1 r.2) =
      Fintype.card (S.AllRuns k) * ((k + 1) * ∑ i, w i) := by
    rw [Fintype.sum_sigma, ← totalCost, S.totalCost_eq, S.card_allRuns]
    ring
  simpa only [mul_assoc] using half_cost_bound
    (fun r : S.AllRuns k => S.cost w k r.1 r.2) (Fintype.card ι) ((k + 1) * ∑ i, w i) hm

/-- More than twice as many runs as endpoint labels force two short runs
with the same endpoint label. The graph interpretation is a later step. -/
theorem exists_two_low_cost (w : ι → ℕ) (k : ℕ) {ν : Type} [Fintype ν]
    (endpoint : S.AllRuns k → ν)
    (hsize : 2 * Fintype.card ν < Fintype.card (S.AllRuns k)) :
    ∃ p q : S.AllRuns k, p ≠ q ∧ endpoint p = endpoint q ∧
      Fintype.card ι * S.cost w k p.1 p.2 ≤ 2 * (k + 1) * ∑ i, w i ∧
      Fintype.card ι * S.cost w k q.1 q.2 ≤ 2 * (k + 1) * ∑ i, w i := by
  classical
  let good := Finset.univ.filter fun r : S.AllRuns k =>
    Fintype.card ι * S.cost w k r.1 r.2 ≤ 2 * (k + 1) * ∑ i, w i
  have hcard : Fintype.card ν < good.card := by
    have hh := S.half_runs_low_cost w k
    change Fintype.card (S.AllRuns k) ≤ 2 * good.card at hh
    omega
  have hn : ¬ Function.Injective (fun r : good => endpoint r.1) := by
    intro hinj
    have hh := Fintype.card_le_of_injective (fun r : good => endpoint r.1) hinj
    simp only [Fintype.card_coe] at hh
    omega
  rw [Function.Injective] at hn
  push_neg at hn
  obtain ⟨p, q, heq, hne⟩ := hn
  exact ⟨p.1, q.1, (fun h => hne (Subtype.ext h)), heq,
    (Finset.mem_filter.mp p.2).2, (Finset.mem_filter.mp q.2).2⟩

end BinarySystem
end Erdos1016.ExactMaximumSupport.LargeGirth.WeightedRuns
