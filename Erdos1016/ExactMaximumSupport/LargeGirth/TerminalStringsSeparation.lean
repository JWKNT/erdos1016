import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStringsForest

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Separation at a degree-two terminal-span vertex

The two incidences of the span lie in distinct components of the original
graph after deleting a relevant vertex. This is stronger than separation in
the auxiliary forest and is the geometric input for the interval regions.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
open SimpleGraph ExceptionalPartners
variable {V : Type*} [Fintype V]
local instance decidableSeparation (p : Prop) : Decidable p := Classical.propDecidable p

/-- Any two distinct span neighbors are separated in the original graph. -/
theorem span_neighbors_separate
    (G F : SimpleGraph V) (hFG : F ≤ G) (hF : F.IsAcyclic)
    (hreach : ∀ u v, G.Reachable u v → F.Reachable u v)
    (B : Finset V) (w : V) (htwo : 2 ≤ Nat.card (TerminalBranch G B w))
    (hdegree : (TerminalForest.span F B).degree w = 2)
    {a b : V} (ha : (TerminalForest.span F B).Adj w a)
    (hb : (TerminalForest.span F B).Adj w b) (hab : a ≠ b) :
    ¬ (deleted G w).Reachable ⟨a, ha.ne.symm⟩ ⟨b, hb.ne.symm⟩ := by
  let I := TerminalBranch G B w
  have hc : 2 ≤ Fintype.card I := by simpa only [Nat.card_eq_fintype_card] using htwo
  letI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨c, d, hcd⟩ := exists_pair_ne I
  obtain ⟨tc, htc, htccomp, htcconn⟩ := c.2
  obtain ⟨td, htd, htdcomp, htdconn⟩ := d.2
  obtain ⟨pc, hpc⟩ := (hreach w tc.1 htcconn).exists_isPath
  obtain ⟨pd, hpd⟩ := (hreach w td.1 htdconn).exists_isPath
  obtain ⟨hsc, hccomp⟩ := first_component_eq_terminal G F hFG tc.2 pc hpc
  obtain ⟨hsd, hdcomp⟩ := first_component_eq_terminal G F hFG td.2 pd hpd
  have hfirst : pc.snd ≠ pd.snd := by
    intro hh
    apply hcd
    apply Subtype.ext
    calc
      c.1 = (deleted G w).connectedComponentMk tc := htccomp.symm
      _ = (deleted G w).connectedComponentMk ⟨pc.snd, hsc⟩ := hccomp.symm
      _ = (deleted G w).connectedComponentMk ⟨pd.snd, hsd⟩ := by congr 1; exact Subtype.ext hh
      _ = (deleted G w).connectedComponentMk td := hdcomp
      _ = d.1 := htdcomp
  have hac : (TerminalForest.span F B).Adj w pc.snd :=
    TerminalForest.span_adj_of_two_terminal_routes F hF B htc htd pc pd hpc hpd
      (fun hn => tc.2 hn.eq.symm) hfirst
  have had : (TerminalForest.span F B).Adj w pd.snd :=
    TerminalForest.span_adj_of_two_terminal_routes F hF B htd htc pd pc hpd hpc
      (fun hn => td.2 hn.eq.symm) hfirst.symm
  have hpairs : ({pc.snd, pd.snd} : Finset V) = (TerminalForest.span F B).neighborFinset w := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hac
      · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr had
    · simp [hfirst, hdegree]
  have ha' : a = pc.snd ∨ a = pd.snd := by
    have h := (SimpleGraph.mem_neighborFinset _ _ _).mpr ha
    rw [← hpairs] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hb' : b = pc.snd ∨ b = pd.snd := by
    have h := (SimpleGraph.mem_neighborFinset _ _ _).mpr hb
    rw [← hpairs] at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have hnot : ¬ (deleted G w).Reachable ⟨pc.snd, hsc⟩ ⟨pd.snd, hsd⟩ := by
    intro hr
    apply hcd
    apply Subtype.ext
    exact htccomp.symm.trans (hccomp.symm.trans
      ((ConnectedComponent.sound hr).trans (hdcomp.trans htdcomp)))
  intro hr
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact hab rfl
  · exact hnot hr
  · exact hnot hr.symm
  · exact hab rfl

/-- Separation along every simple tree route, phrased entirely in the
original graph's deleted-vertex components. -/
def CutsRoutes (G T : SimpleGraph V) (v : V) : Prop :=
  ∀ (a b : V) (p : T.Walk a b), p.IsPath → v ∈ p.support →
    ∀ (ha : a ≠ v) (hb : b ≠ v),
      ¬ (deleted G v).Reachable ⟨a, ha⟩ ⟨b, hb⟩

omit [Fintype V] in
private theorem snd_mem_tail {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hp : ¬ p.Nil) : p.snd ∈ p.support.tail := by
  cases p with
  | nil => exact (hp Walk.Nil.nil).elim
  | cons h q => simp [Walk.snd_cons]

omit [Fintype V] in
/-- If the two neighbors are separated, every simple route through the
vertex separates its endpoints in the original graph as well. -/
theorem cutsRoutes_of_neighbors (G T : SimpleGraph V) (hTG : T ≤ G) (v : V)
    (hsep : ∀ {a b : V} (ha : T.Adj v a) (hb : T.Adj v b), a ≠ b →
      ¬ (deleted G v).Reachable ⟨a, ha.ne.symm⟩ ⟨b, hb.ne.symm⟩) : CutsRoutes G T v := by
  intro a b p hp hv ha hb
  let l := p.takeUntil v hv
  let r := p.dropUntil v hv
  have hlp : l.IsPath := hp.takeUntil hv
  have hrp : r.IsPath := hp.dropUntil hv
  have hln : ¬ l.reverse.Nil := fun h => ha h.eq.symm
  have hrn : ¬ r.Nil := fun h => hb h.eq.symm
  have hfirst : l.reverse.snd ≠ r.snd := by
    intro heq
    have hnodup := hp.support_nodup
    rw [← Walk.take_spec p hv, Walk.support_append, List.nodup_append] at hnodup
    have hleft : l.reverse.snd ∈ l.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using l.reverse.getVert_mem_support 1
    exact List.disjoint_left.mp hnodup.2.2 hleft (heq ▸ snd_mem_tail r hrn)
  have hla := l.reverse.adj_snd hln
  have hra := r.adj_snd hrn
  obtain ⟨hls, hcl⟩ := first_component_eq_terminal G T hTG ha l.reverse hlp.reverse
  obtain ⟨hrs, hcr⟩ := first_component_eq_terminal G T hTG hb r hrp
  intro hab
  apply hsep hla hra hfirst
  exact ConnectedComponent.exact
    (hcl.trans ((ConnectedComponent.sound hab).trans hcr.symm))

/-- Relevant degree-two vertices cut the original graph across their span routes. -/
theorem span_cutsRoutes
    (G F : SimpleGraph V) (hFG : F ≤ G) (hF : F.IsAcyclic)
    (hreach : ∀ u v, G.Reachable u v → F.Reachable u v)
    (B : Finset V) (w : V) (htwo : 2 ≤ Nat.card (TerminalBranch G B w))
    (hdegree : (TerminalForest.span F B).degree w = 2) :
    CutsRoutes G (TerminalForest.span F B) w :=
  cutsRoutes_of_neighbors G (TerminalForest.span F B) ((TerminalForest.span_le F B).trans hFG) w
    (span_neighbors_separate G F hFG hF hreach B w htwo hdegree)

end Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
