import Erdos1016.ExactMaximumSupport.LargeGirth.CorridorDarts
import Erdos1016.ExactMaximumSupport.LargeGirth.CorridorLedger

set_option autoImplicit false

/-!
# Weighted Moore counting on the actual suppressed corridors

The finite binary runs are expanded through the recorded corridor partition.
Their physical dart words are injective and nonbacktracking. Ordinary graph
girth therefore supplies the collision contradiction in the weighted count.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.CorridorMoore

open FiniteMultiGraph Proof.PhysicalPartition Proof.SingleCorridorRoute
open Proof.CompressedRouteDecomposition Proof.PartitionRouteDecomposition
open Proof.PhysicalDegreeTwoCoreComponents Nonbacktracking

theorem flatMap_ne_nil {ι α : Type*} (c : ι → List α) (hc : ∀ i, c i ≠ [])
    (l : List ι) (hl : l ≠ []) : l.flatMap c ≠ [] := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l =>
    intro h
    exact hc i (List.append_eq_nil_iff.mp h).1

theorem flatMap_head {ι α : Type*} (c : ι → List α) (hc : ∀ i, c i ≠ [])
    (l : List ι) (hl : l ≠ []) :
    (l.flatMap c).head (flatMap_ne_nil c hc l hl) = (c (l.head hl)).head (hc _) := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l => exact List.head_append_left (hc i)

theorem flatMap_last {ι α : Type*} (c : ι → List α) (hc : ∀ i, c i ≠ [])
    (l : List ι) (hl : l ≠ []) :
    (l.flatMap c).getLast (flatMap_ne_nil c hc l hl) =
      (c (l.getLast hl)).getLast (hc _) := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons i l ih =>
    cases l with
    | nil => simp
    | cons j l =>
      change (c i ++ (j :: l).flatMap c).getLast _ = _
      rw [List.getLast_append_of_ne_nil _
        (flatMap_ne_nil c hc (j :: l) (List.cons_ne_nil _ _))]
      exact ih (List.cons_ne_nil _ _)

variable {G : PhysicalGraph} {P : Finset G.Vertex} {W : Finset G.Edge}
  (D : CorridorPartition G P W)
  (hne : ∀ C ∈ D.corridors, C.edges ≠ [])
  (hend : ∀ C ∈ D.corridors,
    corridorStart C ∈ protectedOrBranch G P ∧ corridorFinish C ∈ protectedOrBranch G P)
  (hcub : (CorridorDarts.Core D hend).IsCubic)

abbrev system := MultigraphDarts.binarySystem (CorridorDarts.Core D hend) hcub

def weight (e : (CorridorDarts.Core D hend).Edge) : ℕ := (corridorAt D e).edges.length

def expanded (k : ℕ) (r : (system D hend hcub).AllRuns k) : List (Dart G) :=
  ((system D hend hcub).states k r.1 r.2).flatMap (CorridorDarts.code D hend)

theorem states_ne_nil (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    (system D hend hcub).states k r.1 r.2 ≠ [] := by
  intro h
  have hh := (system D hend hcub).states_length k r.1 r.2
  rw [h] at hh
  simp at hh

include hne in
theorem expanded_ne_nil (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    expanded D hend hcub k r ≠ [] :=
  flatMap_ne_nil _ (CorridorDarts.code_ne_nil D hne hend) _ (states_ne_nil D hend hcub k r)

include hne in
theorem expanded_chain (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    List.Chain' (Next G) (expanded D hend hcub k r) :=
  CorridorDarts.codes_chain D hne hend _ ((system D hend hcub).states_chain k r.1 r.2)

include hne in
theorem expanded_injective (k : ℕ) : Function.Injective (expanded D hend hcub k) :=
  (CorridorDarts.codes_injective D hne hend).comp
    ((system D hend hcub).states_injective k)

theorem expanded_length (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    (expanded D hend hcub k r).length =
      (system D hend hcub).cost (fun d => weight D hend d.1) k r.1 r.2 := by
  rcases r with ⟨d, r⟩
  induction k generalizing d with
  | zero => simp [expanded, WeightedRuns.BinarySystem.states, WeightedRuns.BinarySystem.cost,
      CorridorDarts.code_length, weight]
  | succ k ih =>
    change ((CorridorDarts.code D hend d) ++
      expanded D hend hcub k ⟨r.1.1, r.2⟩).length = _
    rw [List.length_append, ih]
    simp only [CorridorDarts.code_length, WeightedRuns.BinarySystem.cost, weight]

def endpoints (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    (CorridorDarts.Core D hend).Vertex × (CorridorDarts.Core D hend).Vertex :=
  (MultigraphDarts.tail _ r.1, MultigraphDarts.head _
    (((system D hend hcub).states k r.1 r.2).getLast (states_ne_nil D hend hcub k r)))

theorem expanded_first_tail (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    tail G ((expanded D hend hcub k r).head (expanded_ne_nil D hne hend hcub k r)) =
      compressedCorridorVertexMap D hend (endpoints D hend hcub k r).1 := by
  unfold expanded
  rw [flatMap_head _ (CorridorDarts.code_ne_nil D hne hend) _ (states_ne_nil D hend hcub k r),
    CorridorDarts.code_first_tail D hne hend]
  congr 2
  have hh := (system D hend hcub).states_head k r.1 r.2
  simpa only [List.head?_eq_head (states_ne_nil D hend hcub k r), Option.some.injEq] using hh

theorem expanded_last_head (k : ℕ) (r : (system D hend hcub).AllRuns k) :
    head G ((expanded D hend hcub k r).getLast (expanded_ne_nil D hne hend hcub k r)) =
      compressedCorridorVertexMap D hend (endpoints D hend hcub k r).2 := by
  unfold expanded
  rw [flatMap_last _ (CorridorDarts.code_ne_nil D hne hend) _ (states_ne_nil D hend hcub k r),
    CorridorDarts.code_last_head D hne hend]
  rfl

include hne hcub in
/-- Exact weighted collision bound. The girth premise concerns ordinary
cycles of the physical graph; the compressed core may have loops or digons. -/
theorem weighted_girth_bound (g k : ℕ)
    (hg : ∀ v (p : G.toSimpleGraph.Walk v v), p.IsCycle → g ≤ p.length)
    (hcount : 2 * (CorridorDarts.Core D hend).vertexCount ^ 2 <
      2 * (CorridorDarts.Core D hend).edgeCount * 2 ^ k) :
    g * (CorridorDarts.Core D hend).edgeCount ≤ 4 * (k + 1) * ∑ e, weight D hend e := by
  classical
  let M := CorridorDarts.Core D hend
  let S := system D hend hcub
  have hmpos : 0 < M.edgeCount := by
    by_contra hn
    have hz : M.edgeCount = 0 := Nat.eq_zero_of_not_pos hn
    change 2 * M.vertexCount ^ 2 < 2 * M.edgeCount * 2 ^ k at hcount
    rw [hz] at hcount
    simp at hcount
  obtain ⟨p, q, hpq, he, hp, hq⟩ := S.exists_two_low_cost (fun d => weight D hend d.1) k
    (endpoints D hend hcub k) (by
      simpa only [Fintype.card_prod, Fintype.card_fin, pow_two,
        MultigraphDarts.cubic_run_count, S, system] using hcount)
  have hsum : (∑ d : MultigraphDarts.Dart M, weight D hend d.1) = 2 * ∑ e, weight D hend e := by
    rw [Fintype.sum_prod_type]
    simp [Fintype.sum_bool, Finset.sum_add_distrib, two_mul]
    rfl
  rw [MultigraphDarts.card_dart, hsum] at hp hq
  by_contra hbad
  have hgl : 4 * (k + 1) * (∑ e, weight D hend e) < g * M.edgeCount := by
    exact Nat.lt_of_not_ge hbad
  obtain ⟨wp, hwp, hlp, hrp⟩ := DartWords.exists_walk G (expanded D hend hcub k p)
    (expanded_ne_nil D hne hend hcub k p) (expanded_chain D hne hend hcub k p)
  obtain ⟨wq, hwq, hlq, hrq⟩ := DartWords.exists_walk G (expanded D hend hcub k q)
    (expanded_ne_nil D hne hend hcub k q) (expanded_chain D hne hend hcub k q)
  have ht : tail G ((expanded D hend hcub k p).head (expanded_ne_nil D hne hend hcub k p)) =
      tail G ((expanded D hend hcub k q).head (expanded_ne_nil D hne hend hcub k q)) := by
    rw [expanded_first_tail D hne hend hcub k p, expanded_first_tail D hne hend hcub k q, he]
  have hh : head G ((expanded D hend hcub k p).getLast (expanded_ne_nil D hne hend hcub k p)) =
      head G ((expanded D hend hcub k q).getLast (expanded_ne_nil D hne hend hcub k q)) := by
    rw [expanded_last_head D hne hend hcub k p, expanded_last_head D hne hend hcub k q, he]
  have hshort : wp.length + wq.length < g := by
    rw [hlp, hlq, expanded_length, expanded_length]
    have hp' : M.edgeCount * S.cost (fun d => weight D hend d.1) k p.1 p.2 ≤
        2 * (k + 1) * ∑ e, weight D hend e := by nlinarith [hp]
    have hq' : M.edgeCount * S.cost (fun d => weight D hend d.1) k q.1 q.2 ≤
        2 * (k + 1) * ∑ e, weight D hend e := by nlinarith [hq]
    nlinarith
  have hgg : ShortWalks.GirthGreater G.toSimpleGraph (g - 1) := by
    intro v w hw
    have hh := hg v w hw
    omega
  have heq : wp = wq.copy ht.symm hh.symm :=
    ShortWalks.reduced_walk_unique_of_girth (g - 1) hgg wp (wq.copy ht.symm hh.symm)
      hrp ((ShortWalks.reduced_copy _ _ _).2 hrq) (by simp only [SimpleGraph.Walk.length_copy]; omega)
  apply hpq
  apply expanded_injective D hne hend hcub k
  have hwords := congrArg (fun w => walkDarts G w) heq
  simpa only [hwp, hwq, walkDarts_copy] using hwords

end Erdos1016.ExactMaximumSupport.LargeGirth.CorridorMoore
