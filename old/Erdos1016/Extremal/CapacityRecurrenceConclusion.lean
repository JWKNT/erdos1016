import Erdos1016.Extremal.InfimumLowerBound
import Erdos1016.Extremal.PancyclicGraphTransfer
import Erdos1016.Extremal.UpperBound
import Erdos1016.Extremal.Capacity.CapacityLowerBound

set_option autoImplicit false

/-!
# Integrating the upper and conditional lower bounds

This module isolates the one remaining analytic input: a quartic near-halving
recurrence for `tailCapacity`. Given that recurrence, the lower bound transfers
from physical graphs to the community extremal infimum. The existing recursive
shortcut construction and explicit small-order witnesses give the upper
bound with additive constant one at every order.
-/

noncomputable section
namespace Erdos1016.Problem1016

open Erdos1016.Extremal

/-- A pancyclic community graph has the lower bound supplied by the physical
capacity estimate, expressed in the community excess convention. -/
private theorem community_excess_lower_of_tail_decay
    (K : ℝ) (hK : 0 < K)
    (hdecay : ∀ r, tailCapacity r ≤ K / (2 : ℝ) ^ logStar r)
    {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPancyclic G) :
    Real.logb 2 (n : ℝ) + (logStar n : ℝ) -
        (Real.logb 2 (K + 2) + 3) ≤ (excess n G : ℝ) := by
  let H := physicalOfSimpleGraph G
  have hp : Extremal.IsPancyclic H := final_isPancyclic_of_isPancyclic G hn hG
  have hlow := pancyclic_excess_lower_of_tail_decay K hK hdecay H hp
  have hconnG : G.Connected := by
    have hconnH : H.IsConnected := hp.1
    change H.toSimpleGraph.Connected at hconnH
    simpa [H, physicalOfSimpleGraph_toSimpleGraph] using hconnH
  have hrank := physicalOfSimpleGraph_rank_eq_excess_add_one G
    hconnG
    hn hG
  have hrankR := congrArg (fun x : ℕ => (x : ℝ)) hrank
  push_cast at hrankR
  have heuler := rank_real_eq_excess_add_one H hp.1
  have hexcess : edgeExcess H = (excess n G : ℝ) := by
    linarith [hrankR, heuler]
  simpa [H, physicalOfSimpleGraph_vertexCount, hexcess] using hlow

/-- The full asymptotic statement follows from the explicit quartic
tail-capacity recurrence. The recurrence is retained as a named hypothesis so
the remaining analytic obligation is visible at the integration boundary. -/
theorem mainTheorem_of_quartic_tail_capacity_recurrence
    (C Rmin : ℕ) (hC : 1 ≤ C)
    (hrec : ∀ R, Rmin ≤ R →
      tailCapacity (2 ^ (C * R ^ 4)) ≤
        ((1 / 2 : ℝ) + 1 / (R : ℝ)) * tailCapacity R +
          (2 : ℝ) ^ (2 - (R : ℝ))) :
    MainTheorem := by
  obtain ⟨K, hK, hdecay⟩ := initialCapacity_tail_logStar_bound C Rmin hC hrec
  let Aminus : ℝ := Real.logb 2 (K + 2) + 3
  let Aplus : ℝ := 1
  refine ⟨Aminus, Aplus, ?_⟩
  intro n hn
  have hlow : Real.logb 2 (n : ℝ) + (logStar n : ℝ) - Aminus ≤ (h n : ℝ) := by
    apply real_lower_bound_of_candidate_graphs n _ (candidateExcesses_nonempty n)
    intro G hG
    simpa [Aminus] using community_excess_lower_of_tail_decay K hK hdecay hn G hG
  have hupp : (h n : ℝ) ≤
      Real.logb 2 (n : ℝ) + (logStar n : ℝ) + Aplus := by
    exact upper_bound n hn
  constructor
  · simpa [Aminus] using hlow
  · simpa [Aplus] using hupp

end Erdos1016.Problem1016
