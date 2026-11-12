import Erdos1016.ExactMaximumSupport.NetworkFourLayers
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false

/-!
# The four-thin-layer input

The general distance-window theorem supplies the exact interface of Lemma 5.5.
Its cycle uses physical labels and stays inside the four specified layers.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport
open BoundaryTrace BoundaryTrace.Network

local instance poleFourLayersDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Lemma 5.5 holds for the original network model. -/
theorem fourThinLayersStatement : ExactMaximum.FourThinLayersStatement := by
  intro V E _ _ N s t hN j h0 h1 h2 h3
  have hdeg (v : V) : N.deg (fun _ => 1) v ≤ 3 := by
    by_cases hs : v = s
    · subst v
      exact hN.deg_s.le.trans (by decide)
    by_cases ht : v = t
    · subst v
      exact hN.deg_t.le.trans (by decide)
    exact (hN.deg_other v hs ht).le
  have hcard (i : Fin 4) :
      Nat.card {v : V // N.graph.dist s v = j + i.val} = 2 := by
    fin_cases i
    · simpa using h0.2.2
    · simpa using h1.2.2
    · simpa using h2.2.2
    · simpa using h3.2.2
  have hmid (v : V)
      (hv : N.graph.dist s v = j + 1 ∨ N.graph.dist s v = j + 2) :
      N.deg (fun _ => 1) v = 3 := by
    apply hN.deg_other v
    · intro hs
      subst v
      simp only [SimpleGraph.dist_self] at hv
      omega
    · intro ht
      subst v
      have hj := h3.2.1
      omega
  exact NetworkFourLayers.exists_cycle_of_four_distance_layers N hN.connected s j
    h0.1 hcard hdeg hmid

end Erdos1016.ExactMaximumSupport
