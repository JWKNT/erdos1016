import Erdos1016.Graph.Multigraph.Basic

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PathBoundaryTelescoping

open Erdos1016
open Erdos1016.FiniteMultiGraph

/-- Mod-two demand contributed by the two endpoints of a vertex pair. -/
def pairDemand (P : FiniteMultiGraph) (a b : P.Vertex) : P.Demand :=
  fun w => (if a = w then (1 : F₂) else 0) + (if b = w then 1 else 0)

private theorem f2_one_add_one : (1 : F₂) + 1 = 0 := by
  change (2 : ZMod 2) = 0
  exact ZMod.natCast_self 2

/-- The endpoint demands of consecutive pairs telescope along a finite vertex
sequence. Canonical `castSucc`/`succ` indices make the induction tail exact. -/
theorem path_pairDemand_sum (P : FiniteMultiGraph) : ∀ {n : ℕ}
    (v : Fin (n + 1) → P.Vertex),
    (∑ i : Fin n, pairDemand P (v i.castSucc) (v i.succ)) =
      pairDemand P (v 0) (v (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro v
      ext w
      by_cases h : v 0 = w <;>
        simp [pairDemand, h, f2_one_add_one]
  | succ n ih =>
      intro v
      let tail : Fin (n + 1) → P.Vertex := fun i => v i.succ
      have htail := ih tail
      rw [Fin.sum_univ_succ]
      have htail' :
          (∑ i : Fin n, pairDemand P
            (v (i.succ.castSucc)) (v (i.succ.succ))) =
            pairDemand P (v (Fin.succ (0 : Fin (n + 1))))
              (v (Fin.last (n + 1))) := by
        simpa [tail, Fin.succ_castSucc] using htail
      rw [htail']
      ext w
      by_cases h0 : v 0 = w <;>
        by_cases hmid : v 1 = w <;>
        by_cases hlast : v (Fin.last (n + 1)) = w
      all_goals
        simp [pairDemand, h0, hmid, hlast, f2_one_add_one]

end Erdos1016.Proof.PathBoundaryTelescoping
