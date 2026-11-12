import Erdos1016.Nonbacktracking.Walks.PrefixCounts
import Erdos1016.Nonbacktracking.Girth.CollisionGeometry
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

/-!
# Exact nonbacktracking counts inside a locally cubic ball

Only the vertices strictly inside the radius need degree three. The walks
are the existing labelled physical runs, and the endpoint injection is the
existing ordinary-girth uniqueness theorem.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.BallRuns

open Nonbacktracking Proof.WalkPrefix

variable (G : PhysicalGraph)

def ball (w : G.Vertex) (s : ℕ) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v => G.toSimpleGraph.dist w v ≤ s

@[simp] theorem mem_ball (w v : G.Vertex) (s : ℕ) :
    v ∈ ball G w s ↔ G.toSimpleGraph.dist w v ≤ s := by simp [ball]

theorem next_distance_le (hconn : G.IsConnected) (w : G.Vertex) {d e : Dart G}
    (h : Next G d e) :
    G.toSimpleGraph.dist w (head G e) ≤ G.toSimpleGraph.dist w (head G d) + 1 := by
  calc
    _ ≤ G.toSimpleGraph.dist w (head G d) +
        G.toSimpleGraph.dist (head G d) (head G e) := hconn.dist_triangle
    _ = _ := by
      rw [h.1, SimpleGraph.dist_eq_one_iff_adj.mpr (dart_adj G e)]

theorem runCount_eq_of_cubic_ball (hconn : G.IsConnected) (w : G.Vertex) (s : ℕ)
    (hcubic : ∀ v, G.toSimpleGraph.dist w v < s → G.degree v = 3)
    (k : ℕ) (d : Dart G) (hd : G.toSimpleGraph.dist w (head G d) + k ≤ s) :
    (∑ e : Dart G, Fintype.card (Run G k d e)) = 2 ^ k := by
  classical
  induction k generalizing d with
  | zero => simp_rw [card_run]; simp [pow_zero, Matrix.one_apply]
  | succ k ih =>
    have hrec : (∑ e : Dart G, Fintype.card (Run G (k + 1) d e)) =
        ∑ j ∈ successors G d, ∑ e : Dart G, Fintype.card (Run G k j e) := by
      simp_rw [card_run, pow_succ', Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp [matrix, successors, Finset.sum_filter, ite_mul]
    rw [hrec]
    have hhead : G.degree (head G d) = 3 := hcubic _ (by omega)
    calc
      _ = ∑ _j ∈ successors G d, 2 ^ k := by
        apply Finset.sum_congr rfl
        intro j hj
        have hn := (mem_successors G d j).mp hj
        have hdist := next_distance_le G hconn w hn
        exact ih j (by omega)
      _ = (successors G d).card * 2 ^ k := by simp
      _ = 2 ^ (k + 1) := by rw [successors_card, hhead, pow_succ]; simp [Nat.mul_comm]

theorem startingRuns_card_of_cubic_ball (hconn : G.IsConnected) (w : G.Vertex) (s : ℕ)
    (hs : 0 < s)
    (hcubic : ∀ v, G.toSimpleGraph.dist w v < s → G.degree v = 3) :
    Fintype.card (StartingRuns G (s - 1) w) = 3 * 2 ^ (s - 1) := by
  classical
  simp only [StartingRuns, Fintype.card_sigma]
  have hroot : G.degree w = 3 := hcubic w (by simpa only [SimpleGraph.dist_self] using hs)
  calc
    _ = ∑ _d : {d : Dart G // tail G d = w}, 2 ^ (s - 1) := by
      apply Finset.sum_congr rfl
      intro d _
      apply runCount_eq_of_cubic_ball G hconn w s hcubic
      have hdist : G.toSimpleGraph.dist w (head G d.1) ≤ 1 := by
        have hh := SimpleGraph.dist_le (dart_adj G d.1).toWalk
        simpa only [d.2, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil,
          Nat.zero_add] using hh
      omega
    _ = 3 * 2 ^ (s - 1) := by simp [card_starting_darts, hroot]

def forgetStart (k : ℕ) (w : G.Vertex) (p : StartingRuns G k w) : AllRuns G k :=
  ⟨p.1.1, p.2⟩

theorem forgetStart_injective (k : ℕ) (w : G.Vertex) :
    Function.Injective (forgetStart G k w) := by
  rintro ⟨⟨d, hd⟩, e, p⟩ ⟨⟨d', hd'⟩, e', p'⟩ he
  change (⟨d, e, p⟩ : AllRuns G k) = ⟨d', e', p'⟩ at he
  cases he
  rfl

def endVertex (k : ℕ) (w : G.Vertex) (p : StartingRuns G k w) : G.Vertex := head G p.2.1

theorem endVertex_injective_of_girth (k D : ℕ) (w : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) (hshort : 2 * (k + 1) ≤ D) :
    Function.Injective (endVertex G k w) := by
  intro p q hpq
  apply forgetStart_injective G k w
  apply endpoints_injective_of_girth G D k hg hshort
  apply Prod.ext
  · exact p.1.2.trans q.1.2.symm
  · exact hpq

theorem endVertex_dist_le (k : ℕ) (w : G.Vertex) (p : StartingRuns G k w) :
    G.toSimpleGraph.dist w (endVertex G k w p) ≤ k + 1 := by
  have hw := SimpleGraph.dist_le (runWalk G k p.2.2)
  rw [runWalk_length, p.1.2] at hw
  exact hw

/-- The whole ball is large because its length-s reduced walks have distinct endpoints. -/
theorem ball_card_lower (hconn : G.IsConnected) (w : G.Vertex) (s D : ℕ)
    (hcubic : ∀ v, G.toSimpleGraph.dist w v < s → G.degree v = 3)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) (hshort : 2 * s ≤ D) :
    2 ^ s ≤ (ball G w s).card := by
  classical
  by_cases hs : s = 0
  · subst s
    have hm : w ∈ ball G w 0 := by simp
    simpa using Finset.card_pos.mpr ⟨w, hm⟩
  have hpos : 0 < s := Nat.pos_of_ne_zero hs
  let f : StartingRuns G (s - 1) w → ball G w s := fun p =>
    ⟨endVertex G (s - 1) w p, by
      rw [mem_ball]
      simpa only [Nat.sub_add_cancel hpos] using endVertex_dist_le G (s - 1) w p⟩
  have hinj : Function.Injective f := by
    intro p q he
    exact endVertex_injective_of_girth G (s - 1) D w hg
      (by simpa only [Nat.sub_add_cancel hpos] using hshort) (congrArg Subtype.val he)
  have hcard := Fintype.card_le_of_injective f hinj
  rw [startingRuns_card_of_cubic_ball G hconn w s hpos hcubic, Fintype.card_coe] at hcard
  have hp : 2 ^ s = 2 * 2 ^ (s - 1) := by
    calc
      _ = 2 ^ ((s - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_succ]; ring
  rw [hp]
  omega

end Erdos1016.ExactMaximumSupport.LargeGirth.BallRuns
