import Erdos1016.ExactMaximum.RingCount
import Erdos1016.ExactMaximum.NetCutRank

set_option autoImplicit false

/-!
# The rank of the ring

The network `ring k` is connected, also without its rung. It has `4k + 6` vertices and `6k + 9`
edges, and no two of its edges have the same two ends. So its rank is `2k + 4`, and the rank of
the ring without the rung is `2k + 3` (`networkRank_ring`, `networkRank_ring_noRung`).
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.ExactMaximum.Ring

open BoundaryTrace BoundaryTrace.Network BoundaryDecay

local instance ringRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable {k : ℕ}

/-! ### Connectedness -/

/-- An edge other than the rung joins its ends in the ring without the rung. -/
theorem adj_of_joins {e : Edge k} {u v : Vertex k} (he : noRung e)
    (h : (ring k).Joins e u v) : ((ring k).sub noRung).graph.Adj u v :=
  ⟨⟨e, he⟩, h⟩

theorem noRung_sq (i : Fin (k + 1)) (x y : Bool) : noRung (sq i x y : Edge k) := by
  simp [noRung, sq, rung]

theorem noRung_link (i : Fin k) (x : Bool) : noRung (link i x : Edge k) := by
  simp [noRung, link, rung]

/-- Every vertex of a tile is joined to `L 0 false` in the ring without the rung. -/
theorem reachable_tile (i : Fin (k + 1)) :
    (∀ x, ((ring k).sub noRung).graph.Reachable (L 0 false) (L i x)) ∧
      ∀ y, ((ring k).sub noRung).graph.Reachable (L 0 false) (R i y) := by
  induction i using Fin.induction with
  | zero =>
    have hR : ∀ y, ((ring k).sub noRung).graph.Reachable (L 0 false) (R (0 : Fin (k + 1)) y) :=
      fun y => (adj_of_joins (noRung_sq 0 false y) (joins_sq 0 false y)).reachable
    refine ⟨fun x => ?_, hR⟩
    cases x
    · exact SimpleGraph.Reachable.refl _
    · exact (hR false).trans
        (adj_of_joins (noRung_sq 0 true false) (joins_sq 0 true false)).symm.reachable
  | succ i ih =>
    have hL : ∀ x, ((ring k).sub noRung).graph.Reachable (L 0 false) (L i.succ x) := fun x =>
      (ih.2 x).trans (adj_of_joins (noRung_link i x) (joins_link i x)).reachable
    exact ⟨hL, fun y => (hL false).trans
      (adj_of_joins (noRung_sq i.succ false y) (joins_sq i.succ false y)).reachable⟩

/-- **The ring without the rung is connected.** -/
theorem connected_noRung (k : ℕ) : ((ring k).sub noRung).graph.Connected := by
  have hroot : ∀ v : Vertex k, ((ring k).sub noRung).graph.Reachable (L 0 false) v := by
    rintro (⟨i, x⟩ | ⟨i, x⟩ | x)
    · exact (reachable_tile i).1 x
    · exact (reachable_tile i).2 x
    · exact ((reachable_tile 0).1 x).trans
        (adj_of_joins (noRung_first x) (joins_first x)).symm.reachable
  haveI : Nonempty (Vertex k) := ⟨L 0 false⟩
  exact ⟨fun u v => (hroot u).symm.trans (hroot v)⟩

/-- **The ring is connected.** -/
theorem connected_ring (k : ℕ) : (ring k).graph.Connected := by
  refine (connected_noRung k).mono ?_
  rintro u v ⟨e, h⟩
  exact ⟨e.1, h⟩

/-! ### The numbers of vertices and edges -/

theorem card_vertex (k : ℕ) : Fintype.card (Vertex k) = 4 * k + 6 := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

theorem card_edge (k : ℕ) : Fintype.card (Edge k) = 6 * k + 9 := by
  simp only [Edge, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_unit]
  ring

theorem natCard_noRung (k : ℕ) : Nat.card {e : Edge k // noRung e} = 6 * k + 8 := by
  have h1 : Nat.card (Edge k) = Nat.card {e : Edge k // e = rung} +
      Nat.card {e : Edge k // noRung e} := by
    rw [← natCard_or_of_disjoint (fun e : Edge k => e = rung) (fun e => noRung e)
      (fun e h1 h2 => h2 h1)]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun e => Classical.em (e = rung)))).symm
  have h2 : Nat.card {e : Edge k // e = rung} = 1 := Nat.card_unique
  have h3 : Nat.card (Edge k) = 6 * k + 9 := by
    rw [Nat.card_eq_fintype_card, card_edge]
  omega

/-! ### The rank -/

/-- **The rank of the ring with the rung is `2k + 4`.** -/
theorem networkRank_ring (k : ℕ) : networkRank (ring k) = 2 * k + 4 := by
  have h := network_rank_euler (ring k)
  rw [connected_component_card (ring k) (connected_ring k), card_vertex, card_edge] at h
  omega

/-- **The rank of the ring without the rung is `2k + 3`.** -/
theorem networkRank_ring_noRung (k : ℕ) : networkRank ((ring k).sub noRung) = 2 * k + 3 := by
  have h := network_rank_euler ((ring k).sub noRung)
  rw [connected_component_card ((ring k).sub noRung) (connected_noRung k), card_vertex,
    ← Nat.card_eq_fintype_card, natCard_noRung] at h
  omega

/-! ### No parallel edges -/

/-- **The ring has no two edges with the same ends.** -/
theorem ring_simple (e f : Edge k)
    (h : (ring k).Joins e ((ring k).src f) ((ring k).dst f)) : e = f := by
  have hjoin : ((ring k).src e = (ring k).src f ∧ (ring k).dst e = (ring k).dst f) ∨
      ((ring k).src e = (ring k).dst f ∧ (ring k).dst e = (ring k).src f) := h
  rcases e with ⟨i, x, y⟩ | ⟨i, x⟩ | x | x | u <;>
    rcases f with ⟨i', x', y'⟩ | ⟨i', x'⟩ | x' | x' | u'
  all_goals
    simp only [ring, src, dst, L, R, H, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, false_and, and_false, or_false, false_or, Fin.ext_iff, Fin.val_succ,
      Fin.coe_castSucc, Fin.val_last, Fin.val_zero] at hjoin
  all_goals first
    | exact hjoin.elim
    | (exfalso; omega)
    | (obtain ⟨⟨h1, h2⟩, _, h4⟩ := hjoin
       have h5 := Fin.ext h1
       subst h5
       subst h2
       subst h4
       rfl)
    | (obtain ⟨⟨h1, h2⟩, _, _⟩ := hjoin
       have h5 := Fin.ext h1
       subst h5
       subst h2
       rfl)
    | (obtain ⟨h1, _⟩ := hjoin
       subst h1
       rfl)
    | (obtain ⟨⟨_, h1⟩, _⟩ := hjoin
       subst h1
       rfl)
    | rfl

end Erdos1016.ExactMaximum.Ring
