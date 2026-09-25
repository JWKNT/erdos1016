import Erdos1016.Nonbacktracking.Trace.WalkTrace

set_option autoImplicit false

/-! Successor sets and finite run types, without minimum degree or entropy. -/
noncomputable section
namespace Erdos1016.Nonbacktracking
open scoped BigOperators
local instance runCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

def successors (d : Dart G) : Finset (Dart G) :=
  Finset.univ.filter (fun e => Next G d e)

@[simp] theorem mem_successors (d e : Dart G) : e ∈ successors G d ↔ Next G d e := by
  simp [successors]

/-- The reversal removes exactly one of the actual outgoing incidences. -/
theorem successors_card (d : Dart G) :
    (successors G d).card = G.degree (head G d) - 1 := by
  have hr := step_eq_sum_next (K := ℤ) G (fun _ => 1) d
  have hc : (∑ e : Dart G, if Next G d e then (1 : ℤ) else 0) =
      ((successors G d).card : ℤ) := by
    simpa [successors] using
      (Finset.sum_boole (fun e : Dart G => Next G d e) Finset.univ :
        (∑ e ∈ Finset.univ, if Next G d e then (1 : ℤ) else 0) = _)
  rw [hc] at hr
  simp only [step, outgoing_one] at hr
  have hle : 1 ≤ G.degree (head G d) := by omega
  exact_mod_cast (show ((successors G d).card : ℤ) =
      ((G.degree (head G d) - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub hle]
    simpa using hr.symm)

/-- Total count for k transitions: the two dart endpoints are unrestricted. -/
def allRunCount (k : ℕ) : ℕ := ∑ d : Dart G, ∑ e : Dart G, Fintype.card (Run G k d e)

/-- A literal finite type of all k-transition runs. -/
abbrev AllRuns (k : ℕ) := Σ d : Dart G, Σ e : Dart G, Run G k d e

theorem card_allRuns (k : ℕ) : Fintype.card (AllRuns G k) = allRunCount G k := by
  simp [AllRuns, allRunCount, Fintype.card_sigma]

def endpoints (k : ℕ) (p : AllRuns G k) : G.Vertex × G.Vertex :=
  (tail G p.1, head G p.2.1)


end Erdos1016.Nonbacktracking
