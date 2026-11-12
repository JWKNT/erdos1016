import Erdos1016.CycleSpace.Graphical.ExceptionalPartners
import Erdos1016.Cycles.Geometry.DegreeTwoTreePaths

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The actual pruned forest for terminal strings

The input condition is geometric: every relevant nonterminal vertex has
at least two terminal-containing branches after deletion. No local parity
space is assumed to have already supplied a forest or a path decomposition.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
open SimpleGraph ExceptionalPartners
variable {V : Type*} [Fintype V]
local instance decidableForest (p : Prop) : Decidable p := Classical.propDecidable p

/-- The existing terminal-route injection also works for two branches. -/
theorem terminalBranch_card_le_span_degree_two
    (G F : SimpleGraph V) (hFG : F ≤ G) (hF : F.IsAcyclic)
    (hreach : ∀ u v, G.Reachable u v → F.Reachable u v)
    (B : Finset V) (w : V)
    (htwo : 2 ≤ Nat.card (TerminalBranch G B w)) :
    Nat.card (TerminalBranch G B w) ≤ (TerminalForest.span F B).degree w := by
  let I := TerminalBranch G B w
  have hc : 2 ≤ Fintype.card I := by simpa only [Nat.card_eq_fintype_card] using htwo
  letI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  choose t ht hcomp hconnected using fun c : I => c.2
  choose p hp using fun c : I => (hreach w (t c).1 (hconnected c)).exists_isPath
  have hn (c : I) : ¬ (p c).Nil := fun h => (t c).2 h.eq.symm
  have hi : Function.Injective (fun c : I => (p c).snd) := by
    intro c d heq
    obtain ⟨hc, hpc⟩ := first_component_eq_terminal G F hFG (t c).2 (p c) (hp c)
    obtain ⟨hd, hpd⟩ := first_component_eq_terminal G F hFG (t d).2 (p d) (hp d)
    apply Subtype.ext
    calc
      c.1 = (deleted G w).connectedComponentMk (t c) := (hcomp c).symm
      _ = (deleted G w).connectedComponentMk ⟨(p c).snd, hc⟩ := hpc.symm
      _ = (deleted G w).connectedComponentMk ⟨(p d).snd, hd⟩ := by congr 1; exact Subtype.ext heq
      _ = (deleted G w).connectedComponentMk (t d) := hpd
      _ = d.1 := hcomp d
  simpa only [Nat.card_eq_fintype_card] using
    TerminalForest.route_card_le_span_degree F hF B w (fun c : I => (t c).1)
      ht p hp hn hi

/-- Vertices left for the ordered strings. Isolated discarded vertices are
not included, even though the terminal span keeps the original vertex type. -/
def interiors (T : SimpleGraph V) (B : Finset V) : Finset V :=
  Finset.univ.filter fun v => T.degree v = 2 ∧ v ∉ B

def branchVertices (T : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => 3 ≤ T.degree v

def exceptions (T : SimpleGraph V) (B R : Finset V) : Finset V :=
  R ∩ (B ∪ branchVertices T)

/-- Every relevant vertex is either a foot, a branch exception, or an
actual degree-two vertex of the constructed terminal span. -/
theorem exists_terminal_span (G : SimpleGraph V) (B R : Finset V)
    (hrelevant : ∀ v ∈ R, v ∉ B → 2 ≤ Nat.card (TerminalBranch G B v)) :
    ∃ F : SimpleGraph V, F ≤ G ∧ F.IsAcyclic ∧
      (∀ u v, G.Reachable u v → F.Reachable u v) ∧
      (exceptions (TerminalForest.span F B) B R).card ≤ 2*B.card ∧
      (∀ v ∈ R, v ∉ exceptions (TerminalForest.span F B) B R →
        v ∈ interiors (TerminalForest.span F B) B) := by
  obtain ⟨F, hFG, hF, hreach⟩ := TerminalForest.exists_spanning_forest G
  refine ⟨F, hFG, hF, hreach, ?_, ?_⟩
  · have hb := TerminalForest.span_branch_card_le F hF B
    change (branchVertices (TerminalForest.span F B)).card ≤ B.card at hb
    calc
      _ ≤ (B ∪ branchVertices (TerminalForest.span F B)).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ ≤ B.card + (branchVertices (TerminalForest.span F B)).card := Finset.card_union_le _ _
      _ ≤ 2*B.card := by omega
  · intro v hv hn
    have hb : v ∉ B := by
      intro hb
      exact hn (Finset.mem_inter.mpr ⟨hv, Finset.mem_union_left _ hb⟩)
    have hbranch : ¬ 3 ≤ (TerminalForest.span F B).degree v := by
      intro hh
      exact hn (Finset.mem_inter.mpr ⟨hv,
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)⟩)
    have hd := (hrelevant v hv hb).trans
      (terminalBranch_card_le_span_degree_two G F hFG hF hreach B v (hrelevant v hv hb))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hb⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
