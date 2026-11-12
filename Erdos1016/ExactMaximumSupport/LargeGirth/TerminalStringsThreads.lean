import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringsForest
import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringCount

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Degree-two components are the terminal strings' threads

The threads are actual components of the induced degree-two, nonterminal
region. Their number is bounded by the feet and branch vertices. Each thread
has a simple spanning path in the auxiliary terminal forest.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
open SimpleGraph ExceptionalPartners
variable {V : Type*} [Fintype V]
local instance decidableThreads (p : Prop) : Decidable p := Classical.propDecidable p
local instance componentFintype (G : SimpleGraph V) : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk Quot.mk_surjective

/-- Every terminal-to-terminal path is retained, with its complete support. -/
def terminalPath (F : SimpleGraph V) (B : Finset V) {a b : V}
    (ha : a ∈ B) (hb : b ∈ B) (p : F.Walk a b) (hp : p.IsPath) :
    (TerminalForest.span F B).Walk a b :=
  p.transfer _ (by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      exact ⟨a, ha, b, hb, p, hp, (p.mem_edges_toSubgraph).mpr he⟩)

/-- A retained vertex can reach every terminal in its original component
inside the terminal span itself. -/
theorem terminal_reachable (G F : SimpleGraph V)
    (hreach : ∀ u v, G.Reachable u v → F.Reachable u v)
    (B : Finset V) {v t : V} (hv : 0 < (TerminalForest.span F B).degree v)
    (ht : t ∈ B) (hvt : G.Reachable v t) : (TerminalForest.span F B).Reachable v t := by
  obtain ⟨w, a, ha, b, hb, p, hp, hadj⟩ :=
    ((TerminalForest.span F B).degree_pos_iff_exists_adj v).mp hv
  have hvp : v ∈ p.support := Walk.mem_support_of_adj_toSubgraph hadj
  let q := terminalPath F B ha hb p hp
  have hvq : v ∈ q.support := by simpa [q, terminalPath] using hvp
  have hva : F.Reachable a v := (p.takeUntil v hvp).reachable
  obtain ⟨r, hr⟩ := (hva.trans (hreach v t hvt)).exists_isPath
  exact (q.takeUntil v hvq).reverse.reachable.trans
    (terminalPath F B ha ht r hr).reachable

abbrev Thread (T : SimpleGraph V) (B : Finset V) :=
  (T.induce (↑(interiors T B) : Set V)).ConnectedComponent

def threadVertices (T : SimpleGraph V) (B : Finset V) (c : Thread T B) : Finset V :=
  c.supp.toFinset.image Subtype.val

theorem thread_subset (T : SimpleGraph V) (B : Finset V) (c : Thread T B) :
    threadVertices T B c ⊆ interiors T B := by
  intro v hv
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
  exact w.2

theorem thread_count (F : SimpleGraph V) (hF : F.IsAcyclic) (B : Finset V) :
    Nat.card (Thread (TerminalForest.span F B) B) ≤ 2*B.card := by
  let T := TerminalForest.span F B
  have hle := TerminalStringCount.component_count_le_boundary T
    (TerminalForest.span_isAcyclic F hF B) (interiors T B) (B ∪ branchVertices T)
    (fun v hv => (Finset.mem_filter.mp hv).2.1) (by
      intro v hv w hvw hw
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_left _ hwB
      · have hpos : 0 < T.degree w := (T.degree_pos_iff_exists_adj w).mpr ⟨v, hvw.symm⟩
        have hone : T.degree w ≠ 1 := fun h => hwB (TerminalForest.span_leaf_mem F B w h)
        have htwo : T.degree w ≠ 2 := fun h => hw
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hwB⟩)
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
  have hb := TerminalForest.span_branch_card_le F hF B
  change (branchVertices T).card ≤ B.card at hb
  exact hle.trans ((Finset.card_union_le _ _).trans (by omega))

/-- The actual component path, with equality of its support and component region. -/
theorem exists_thread_path (T : SimpleGraph V) (hT : T.IsAcyclic) (B : Finset V)
    (c : Thread T B) :
    ∃ a b, ∃ p : T.Walk a b, p.IsPath ∧ p.support.toFinset = threadVertices T B c := by
  let H := T.induce (↑(interiors T B) : Set V)
  let K := H.induce c.supp
  let inc : K ↪g T := {
    toFun := fun v => v.1.1
    inj' := by intro a b h; exact Subtype.ext (Subtype.ext h)
    map_rel_iff' := by intro a b; rfl }
  have hK : K.IsAcyclic := by
    intro v p hp
    exact hT (p.map inc.toHom) (hp.map inc.injective)
  have hd (v : c.supp) : (K.neighborFinset v).card ≤ 2 := by
    have hcard := Fintype.card_le_of_injective (inc.mapNeighborSet v) (inc.mapNeighborSet v).injective
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at hcard
    have hv := (Finset.mem_filter.mp v.1.2).2.1
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hcard.trans_eq hv
  obtain ⟨a, b, p, hp, hcover⟩ := Proof.FiniteTreeDegreeTwoPath.exists_spanning_path
    K c.connected_induce_supp hK hd
  refine ⟨a.1.1, b.1.1, p.map inc.toHom, Walk.map_isPath_of_injective inc.injective hp, ?_⟩
  ext v
  constructor
  · intro hv
    have hv' : ∃ u, u ∈ p.support ∧ inc u = v := by
      simpa only [List.mem_toFinset, Walk.support_map, List.mem_map] using hv
    obtain ⟨u, _, rfl⟩ := hv'
    exact Finset.mem_image.mpr ⟨u.1, Set.mem_toFinset.mpr u.2, rfl⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    apply List.mem_toFinset.mpr
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨u, Set.mem_toFinset.mp hu⟩, hcover _, rfl⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
