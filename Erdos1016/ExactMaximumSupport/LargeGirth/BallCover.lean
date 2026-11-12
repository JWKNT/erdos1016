import Erdos1016.ExactMaximumSupport.LargeGirth.BallRuns

set_option autoImplicit false

/-!
# Subcubic ball size and a center far from the ports

Shortest paths are encoded by actual nonbacktracking runs. The existing
subcubic prefix count bounds a closed radius-s ball by `3*2^s` vertices.
A union bound then supplies a vertex outside all port balls.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.BallCover

open Nonbacktracking Proof.WalkPrefix BallRuns

theorem path_reduced {V : Type*} {H : SimpleGraph V} {u v : V}
    (p : H.Walk u v) (hp : p.IsPath) : ShortWalks.Reduced p := by
  induction p with
  | nil => trivial
  | @cons u w v huw q ih =>
    have hq := (SimpleGraph.Walk.cons_isPath_iff huw q).mp hp
    refine ⟨ih hq.1, ?_⟩
    intro _ he
    exact hq.2 (he ▸ q.getVert_mem_support 1)

variable (G : PhysicalGraph)

abbrev ReachCode (s : ℕ) (w : G.Vertex) := Unit ⊕ (Σ i : Fin s, StartingRuns G i.val w)

def endpoint (s : ℕ) (w : G.Vertex) : ReachCode G s w → G.Vertex
  | .inl _ => w
  | .inr ⟨i, r⟩ => endVertex G i.val w r

theorem endpoint_dist_le (s : ℕ) (w : G.Vertex) (c : ReachCode G s w) :
    G.toSimpleGraph.dist w (endpoint G s w c) ≤ s := by
  cases c with
  | inl _ => simp [endpoint, SimpleGraph.dist_self]
  | inr z =>
    exact (endVertex_dist_le G z.1.val w z.2).trans (by omega)

theorem endpoint_surjective_to_ball (hconn : G.IsConnected) (s : ℕ) (w : G.Vertex)
    (v : G.Vertex) (hv : v ∈ ball G w s) :
    ∃ c : ReachCode G s w, endpoint G s w c = v := by
  classical
  by_cases he : v = w
  · subst v
    exact ⟨.inl (), rfl⟩
  obtain ⟨p, hp, hlen⟩ := hconn.exists_path_of_dist w v
  have hpos : 0 < p.length := by
    rw [hlen]
    exact hconn.pos_dist_of_ne (Ne.symm he)
  have hle : p.length ≤ s := by simpa only [hlen, mem_ball] using hv
  obtain ⟨d, e, hdt, _, _, het, r, _⟩ :=
    Proof.CyclicRunCollisionGeometry.reduced_walk_has_dart_run G p (path_reduced p hp) hpos
  let i : Fin s := ⟨p.length - 1, by omega⟩
  exact ⟨.inr ⟨i, ⟨⟨d, hdt⟩, e, r⟩⟩, het⟩

theorem geometric_sum (s : ℕ) : (∑ i : Fin s, 3 * 2 ^ i.val) + 3 = 3 * 2 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [pow_succ]
    omega

theorem reachCode_card_le (hmax : ∀ v, G.degree v ≤ 3) (s : ℕ) (w : G.Vertex) :
    Fintype.card (ReachCode G s w) ≤ 3 * 2 ^ s := by
  classical
  change Fintype.card (Unit ⊕ (Σ i : Fin s, StartingRuns G i.val w)) ≤ _
  rw [Fintype.card_sum, Fintype.card_sigma, Fintype.card_unit]
  have hh : (∑ i : Fin s, Fintype.card (StartingRuns G i.val w)) ≤ ∑ i : Fin s, 3 * 2 ^ i.val :=
    Finset.sum_le_sum fun i _ => startingRuns_card_le_of_max_degree G hmax i.val w
  have hs := geometric_sum s
  omega

theorem ball_card_upper (hconn : G.IsConnected) (hmax : ∀ v, G.degree v ≤ 3)
    (w : G.Vertex) (s : ℕ) : (ball G w s).card ≤ 3 * 2 ^ s := by
  classical
  let f : ReachCode G s w → ball G w s := fun c =>
    ⟨endpoint G s w c, (mem_ball G w _ s).mpr (endpoint_dist_le G s w c)⟩
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨c, hc⟩ := endpoint_surjective_to_ball G hconn s w v.1 v.2
    exact ⟨c, Subtype.ext hc⟩
  have hc := Fintype.card_le_of_surjective f hf
  rw [Fintype.card_coe] at hc
  exact hc.trans (reachCode_card_le G hmax s w)

/-- The center avoids every degree-two port when the union of port balls
is smaller than the graph. The result uses literal graph distance. -/
theorem exists_far_vertex (hconn : G.IsConnected) (hmax : ∀ v, G.degree v ≤ 3)
    (P : Finset G.Vertex) (s : ℕ) (hsize : 3 * P.card * 2 ^ s < G.vertexCount) :
    ∃ w : G.Vertex, ∀ p ∈ P, s < G.toSimpleGraph.dist w p := by
  classical
  let U := P.biUnion fun p => ball G p s
  have hcard : U.card < G.vertexCount := by
    calc
      U.card ≤ ∑ p ∈ P, (ball G p s).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ P, 3 * 2 ^ s := Finset.sum_le_sum fun p _ => ball_card_upper G hconn hmax p s
      _ = 3 * P.card * 2 ^ s := by simp; ring
      _ < G.vertexCount := hsize
  have hnot : ∃ w : G.Vertex, w ∉ U := by
    by_contra hn
    push_neg at hn
    have he : U = Finset.univ := Finset.eq_univ_iff_forall.mpr hn
    simp only [he, Finset.card_univ, Fintype.card_fin, lt_self_iff_false] at hcard
  obtain ⟨w, hw⟩ := hnot
  refine ⟨w, ?_⟩
  intro p hp
  have hnp : w ∉ ball G p s := fun h => hw (Finset.mem_biUnion.mpr ⟨p, hp, h⟩)
  rw [mem_ball, SimpleGraph.dist_comm] at hnp
  omega

end Erdos1016.ExactMaximumSupport.LargeGirth.BallCover
