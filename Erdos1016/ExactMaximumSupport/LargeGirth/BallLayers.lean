import Erdos1016.ExactMaximumSupport.LargeGirth.BallCover
import Erdos1016.ExactMaximumSupport.LargeGirth.SimpleRealization
import Mathlib.Data.Int.Interval

set_option autoImplicit false

/-!
# A large literal distance layer from a port-free cubic ball

The cardinality conclusion refers to the integer-valued graph-distance levels
used by the thin-marker theorem. The only numerical condition is that the
union of the port balls is smaller than the graph. Both the ball size and
its concentration in `2s+1` consecutive levels are proved here.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.BallLayers

open Nonbacktracking BallRuns BallCover

/-- A finite set mapped into a finite interval has a fiber at least its
average size. The multiplied form avoids any rounding convention. -/
theorem exists_large_fiber {V : Type*} [DecidableEq V] (S : Finset V)
    (I : Finset ℤ) (f : V → ℤ) (hI : I.Nonempty)
    (hmap : ∀ v ∈ S, f v ∈ I) :
    ∃ j ∈ I, S.card ≤ I.card * (S.filter fun v => f v = j).card := by
  classical
  obtain ⟨j, hj, hm⟩ := I.exists_max_image (fun j => (S.filter fun v => f v = j).card) hI
  refine ⟨j, hj, ?_⟩
  calc
    S.card = ∑ i ∈ I, (S.filter fun v => f v = i).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _i ∈ I, (S.filter fun v => f v = j).card :=
      Finset.sum_le_sum fun i hi => hm i hi
    _ = I.card * (S.filter fun v => f v = j).card := by simp

variable (G : PhysicalGraph)

def level (o : G.Vertex) (v : G.Vertex) : ℤ := G.toSimpleGraph.dist o v

def layer (o : G.Vertex) (j : ℤ) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v => level G o v = j

/-- Every radius-s ball meets at most `2s+1` distance levels from any root. -/
theorem exists_large_layer_of_ball (hconn : G.IsConnected) (o w : G.Vertex) (s : ℕ) :
    ∃ j : ℤ, (ball G w s).card ≤ (2 * s + 1) * (layer G o j).card := by
  classical
  let d : ℤ := G.toSimpleGraph.dist o w
  let I := Finset.Icc (d - s) (d + s)
  have hI : I.Nonempty := ⟨d, Finset.mem_Icc.mpr (by constructor <;> omega)⟩
  have hcard : I.card = 2 * s + 1 := by
    rw [Int.card_Icc]
    have he : d + (s : ℤ) + 1 - (d - s) = (2 * s + 1 : ℕ) := by omega
    rw [he, Int.toNat_natCast]
  have hmap (v : G.Vertex) (hv : v ∈ ball G w s) : level G o v ∈ I := by
    have hs := (mem_ball G w v s).mp hv
    have h₁ : G.toSimpleGraph.dist o v ≤ G.toSimpleGraph.dist o w + G.toSimpleGraph.dist w v :=
      hconn.dist_triangle
    have h₂ : G.toSimpleGraph.dist o w ≤ G.toSimpleGraph.dist o v + G.toSimpleGraph.dist v w :=
      hconn.dist_triangle
    rw [SimpleGraph.dist_comm (u := v) (v := w)] at h₂
    change level G o v ∈ Finset.Icc (d - s) (d + s)
    rw [Finset.mem_Icc]
    dsimp [level, d]
    constructor <;> omega
  obtain ⟨j, _, hj⟩ := exists_large_fiber (ball G w s) I (level G o) hI hmap
  refine ⟨j, ?_⟩
  rw [hcard] at hj
  exact hj.trans (Nat.mul_le_mul_left _ (Finset.card_le_card (by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩)))

/-- A degree-three neighborhood away from all exceptional vertices forces
an exponentially large distance layer. -/
theorem exists_large_layer (hconn : G.IsConnected) (hmax : ∀ v, G.degree v ≤ 3)
    (P : Finset G.Vertex) (hcubic : ∀ v, v ∉ P → G.degree v = 3)
    (o : G.Vertex) (s D : ℕ)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D) (hshort : 2 * s ≤ D)
    (hsize : 3 * P.card * 2 ^ s < G.vertexCount) :
    ∃ j : ℤ, 2 ^ s ≤ (2 * s + 1) * (layer G o j).card := by
  classical
  obtain ⟨w, hw⟩ := exists_far_vertex G hconn hmax P s hsize
  have hc (v : G.Vertex) (hv : G.toSimpleGraph.dist w v < s) : G.degree v = 3 := by
    apply hcubic v
    intro hp
    have hh := hw v hp
    omega
  have hl := ball_card_lower G hconn w s D hc hg hshort
  obtain ⟨j, hj⟩ := exists_large_layer_of_ball G hconn o w s
  exact ⟨j, hl.trans hj⟩

/-- Same-label multigraph interface. No simplicity hypothesis is added:
the actual cycle-word girth assumption excludes loops and parallel labels. -/
theorem multigraph_exists_large_layer (M : FiniteMultiGraph)
    (hconn : M.toSimpleGraph.Connected) (hmax : ∀ v, M.degree v ≤ 3)
    (P : Finset M.Vertex) (hcubic : ∀ v, v ∉ P → M.degree v = 3)
    (o : M.Vertex) (s g : ℕ) (hg : 3 ≤ g)
    (hshort : ¬ M.HasCycleShorterThan g) (hs : 2 * s < g)
    (hsize : 3 * P.card * 2 ^ s < M.vertexCount) :
    ∃ j : ℤ, 2 ^ s ≤ (2 * s + 1) *
      (Finset.univ.filter fun v => (M.toSimpleGraph.dist o v : ℤ) = j).card := by
  classical
  let h3 := no_short_three_of_le M g hg hshort
  let G := realization M h3
  have hc : G.IsConnected := realization_connected M h3 hconn
  have hm (v : G.Vertex) : G.degree v ≤ 3 := by rw [realization_degree]; exact hmax v
  have hd (v : G.Vertex) (hv : v ∉ P) : G.degree v = 3 := by
    rw [realization_degree]
    exact hcubic v hv
  have hgg := realization_girthGreater M h3 (g - 1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ g)] using hshort)
  obtain ⟨j, hj⟩ := exists_large_layer G hc hm P hd o s (g - 1) hgg (by omega) hsize
  refine ⟨j, ?_⟩
  simpa only [layer, level, G, realization_toSimpleGraph] using hj

end Erdos1016.ExactMaximumSupport.LargeGirth.BallLayers
