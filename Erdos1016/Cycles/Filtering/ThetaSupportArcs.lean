import Erdos1016.Cycles.Filtering.ThetaArcUniqueness
import Erdos1016.Nonbacktracking.Walks.CyclePathUniqueness

set_option autoImplicit false

namespace Erdos1016.Proof.ThetaSupportArcUniqueness

open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.ThetaArcUniqueness
open Erdos1016.Proof.CyclePathUniqueness
open Erdos1016.Nonbacktracking
open SimpleGraph

private noncomputable def liftWalkOnCycle (G : Erdos1016.PhysicalGraph)
    {r u v : G.Vertex} (c : G.toSimpleGraph.Walk r r)
    (p : G.toSimpleGraph.Walk u v)
    (hEdges : ∀ e, e ∈ p.edges → e ∈ c.edges) :
    c.toSubgraph.spanningCoe.Walk u v :=
  match p with
  | .nil' _ => .nil
  | .cons' a b v hab p =>
      have hAdj : c.toSubgraph.spanningCoe.Adj a b := by
        change s(a, b) ∈ c.toSubgraph.edgeSet
        rw [c.mem_edges_toSubgraph]
        exact hEdges _ (by simp)
      Walk.cons hAdj (liftWalkOnCycle G c p (by
        intro e he
        apply hEdges
        simp [Walk.edges_cons, he]))

private theorem liftWalkOnCycle_support (G : Erdos1016.PhysicalGraph) {r u v : G.Vertex}
    (c : G.toSimpleGraph.Walk r r) (p : G.toSimpleGraph.Walk u v)
    (hEdges : ∀ e, e ∈ p.edges → e ∈ c.edges) :
    (liftWalkOnCycle G c p hEdges).support = p.support := by
  induction p with
  | nil => rfl
  | @cons a b v hab p ih => simp [liftWalkOnCycle, ih]

private theorem liftWalkOnCycle_edges (G : Erdos1016.PhysicalGraph) {r u v : G.Vertex}
    (c : G.toSimpleGraph.Walk r r) (p : G.toSimpleGraph.Walk u v)
    (hEdges : ∀ e, e ∈ p.edges → e ∈ c.edges) :
    (liftWalkOnCycle G c p hEdges).edges = p.edges := by
  induction p with
  | nil => rfl
  | @cons a b v hab p ih => simp [liftWalkOnCycle, ih]

private theorem liftWalkOnCycle_isPath (G : Erdos1016.PhysicalGraph) {r u v : G.Vertex}
    (c : G.toSimpleGraph.Walk r r) (p : G.toSimpleGraph.Walk u v)
    (hEdges : ∀ e, e ∈ p.edges → e ∈ c.edges) (hp : p.IsPath) :
    (liftWalkOnCycle G c p hEdges).IsPath := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    rw [liftWalkOnCycle_edges]
    exact hp.isTrail.edges_nodup
  · rw [liftWalkOnCycle_support]
    exact hp.support_nodup

private theorem liftWalkOnCycle_snd (G : Erdos1016.PhysicalGraph) {r u v : G.Vertex}
    (c : G.toSimpleGraph.Walk r r) (p : G.toSimpleGraph.Walk u v)
    (hEdges : ∀ e, e ∈ p.edges → e ∈ c.edges) (huv : u ≠ v) :
    (liftWalkOnCycle G c p hEdges).snd = p.snd := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons => simp [liftWalkOnCycle]

private theorem cycle_subgraph_le (G : Erdos1016.PhysicalGraph)
    {r : G.Vertex} (c : G.toSimpleGraph.Walk r r) :
    c.toSubgraph.spanningCoe ≤ G.toSimpleGraph := by
  intro a b hab
  change s(a, b) ∈ c.toSubgraph.edgeSet at hab
  rw [c.mem_edges_toSubgraph] at hab
  exact c.adj_of_mem_edges hab



private theorem first_edge_mem {V : Type*} {H : SimpleGraph V} {u v : V}
    (p : H.Walk u v) (huv : u ≠ v) : s(u, p.snd) ∈ p.edges := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons hadj q => simp

private theorem first_neighbors_ne_of_edge_disjoint {V : Type*}
    {H : SimpleGraph V} {u v : V} (p q : H.Walk u v) (huv : u ≠ v)
    (hdisj : ∀ e, e ∈ p.edges → e ∉ q.edges) : p.snd ≠ q.snd := by
  intro heq
  have hp : s(u, p.snd) ∈ p.edges := first_edge_mem p huv
  have hq : s(u, p.snd) ∈ q.edges := by
    rw [heq]
    exact first_edge_mem q huv
  exact hdisj _ hp hq

private theorem thetaArc_edges_subset_base (G : Erdos1016.PhysicalGraph) {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) :
    (∀ e, e ∈ t.left.edges → e ∈ (leftRightCycle G.toSimpleGraph t).edges) ∧
    (∀ e, e ∈ t.right.edges → e ∈ (leftRightCycle G.toSimpleGraph t).edges) := by
  constructor
  · intro e he
    simp [leftRightCycle, Walk.edges_append, he]
  · intro e he
    simp [leftRightCycle, Walk.edges_append, Walk.edges_reverse, he]

private theorem path_snd_adj {V : Type*} {H : SimpleGraph V} {u v : V}
    (p : H.Walk u v) (huv : u ≠ v) : H.Adj u p.snd := by
  cases p with
  | nil => exact False.elim (huv rfl)
  | cons hadj q => simpa using hadj

private theorem path_eq_or_swap_of_degree_two {V : Type*} [Finite V] [DecidableEq V]
    (H : SimpleGraph V) (hcycles : H.IsCycles) {u v : V}
    (huv : u ≠ v)
    (p q p' q' : H.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (hp' : p'.IsPath) (hq' : q'.IsPath)
    (hfirstPair : p.snd ≠ q.snd) (hsecondPair : p'.snd ≠ q'.snd)
    (hadjP : H.Adj u p.snd) (hadjQ : H.Adj u q.snd)
    (hadjP' : H.Adj u p'.snd) (hadjQ' : H.Adj u q'.snd) :
    (p = p' ∧ q = q') ∨ (p = q' ∧ q = p') := by
  obtain ⟨z, hz, hzuniq⟩ := hcycles.existsUnique_ne_adj hadjP
  have hqz : q.snd = z := hzuniq q.snd ⟨hfirstPair, hadjQ⟩
  by_cases hsame : p.snd = p'.snd
  · left
    have hpEq := path_eq_of_first_edge H hcycles p p' hp hp' huv hsame
    have hq'z : q'.snd = z := hzuniq q'.snd ⟨by simpa [hsame] using hsecondPair, hadjQ'⟩
    have hqEq := path_eq_of_first_edge H hcycles q q' hq hq' huv (hqz.trans hq'z.symm)
    exact ⟨hpEq, hqEq⟩
  · right
    have hp'z : p'.snd = z := hzuniq p'.snd ⟨by
      intro h
      exact hsame h, hadjP'⟩
    have hq'first : q'.snd = p.snd := by
      by_contra h
      have hq'z : q'.snd = z := hzuniq q'.snd ⟨by
        intro h'
        exact h h'.symm, hadjQ'⟩
      exact hsecondPair (hp'z.trans hq'z.symm)
    have hpEq := path_eq_of_first_edge H hcycles p q' hp hq' huv hq'first.symm
    have hqEq := path_eq_of_first_edge H hcycles q p' hq hp' huv (hqz.trans hp'z.symm)
    exact ⟨hpEq, hqEq⟩


/-- Equal physical cycle words force the two theta arc pairs to agree up to
exchange.  The proof uses the cycle support as a degree-two graph: all four
arcs lift into that spanning subgraph, where their endpoints and first
neighbors determine each simple path. -/
theorem arcCorrespondence_of_equal_base_cycleWord (G : Erdos1016.PhysicalGraph)
    {u v : G.Vertex} (t t' : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (hword : cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t)
        (leftRightCycle_isCycle G.toSimpleGraph t huv) =
      cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t')
        (leftRightCycle_isCycle G.toSimpleGraph t' huv)) :
    ArcPairCorrespondence G t.left t.right t'.left t'.right := by
  let c := leftRightCycle G.toSimpleGraph t
  let d := leftRightCycle G.toSimpleGraph t'
  have hc : c.IsCycle := leftRightCycle_isCycle G.toSimpleGraph t huv
  have hd : d.IsCycle := leftRightCycle_isCycle G.toSimpleGraph t' huv
  change cycleWordOfWalk G c hc = cycleWordOfWalk G d hd at hword
  have hedges : c.edges.toFinset = d.edges.toFinset :=
    cycleWord_eq_edges_toFinset_eq (G := G) (u := u) (v := v) c d hc hd hword
  have htc := thetaArc_edges_subset_base G t
  have ht'c := thetaArc_edges_subset_base G t'
  have hleft' : ∀ e, e ∈ t'.left.edges → e ∈ c.edges := by
    intro e he
    have heD : e ∈ d.edges.toFinset := List.mem_toFinset.mpr (ht'c.1 e he)
    have heC : e ∈ c.edges.toFinset := hedges.symm ▸ heD
    exact List.mem_toFinset.mp heC
  have hright' : ∀ e, e ∈ t'.right.edges → e ∈ c.edges := by
    intro e he
    have heD : e ∈ d.edges.toFinset := List.mem_toFinset.mpr (ht'c.2 e he)
    have heC : e ∈ c.edges.toFinset := hedges.symm ▸ heD
    exact List.mem_toFinset.mp heC
  let H := c.toSubgraph.spanningCoe
  let p := liftWalkOnCycle G c t.left htc.1
  let q := liftWalkOnCycle G c t.right htc.2
  let p' := liftWalkOnCycle G c t'.left hleft'
  let q' := liftWalkOnCycle G c t'.right hright'
  have hp : p.IsPath := liftWalkOnCycle_isPath G c t.left htc.1 t.left_path
  have hq : q.IsPath := liftWalkOnCycle_isPath G c t.right htc.2 t.right_path
  have hp' : p'.IsPath := liftWalkOnCycle_isPath G c t'.left hleft' t'.left_path
  have hq' : q'.IsPath := liftWalkOnCycle_isPath G c t'.right hright' t'.right_path
  have hcycles : H.IsCycles := by
    dsimp [H, c]
    exact hc.isCycles_spanningCoe_toSubgraph
  have hfirst : p.snd ≠ q.snd := by
    simpa [p, q, liftWalkOnCycle_snd G c t.left htc.1 huv,
      liftWalkOnCycle_snd G c t.right htc.2 huv] using
      first_neighbors_ne_of_edge_disjoint t.left t.right huv t.left_right_edges
  have hsecond : p'.snd ≠ q'.snd := by
    simpa [p', q', liftWalkOnCycle_snd G c t'.left hleft' huv,
      liftWalkOnCycle_snd G c t'.right hright' huv] using
      first_neighbors_ne_of_edge_disjoint t'.left t'.right huv t'.left_right_edges
  have hadjP : H.Adj u p.snd := path_snd_adj p huv
  have hadjQ : H.Adj u q.snd := path_snd_adj q huv
  have hadjP' : H.Adj u p'.snd := path_snd_adj p' huv
  have hadjQ' : H.Adj u q'.snd := path_snd_adj q' huv
  have hpaths := path_eq_or_swap_of_degree_two H hcycles huv p q p' q'
    hp hq hp' hq' hfirst hsecond hadjP hadjQ hadjP' hadjQ'
  rcases hpaths with ⟨hpEq, hqEq⟩ | ⟨hpEq, hqEq⟩
  · left
    exact ⟨by simpa [p, p', liftWalkOnCycle_edges] using
        congrArg (fun x => x.edges.toFinset) hpEq,
      by simpa [q, q', liftWalkOnCycle_edges] using
        congrArg (fun x => x.edges.toFinset) hqEq⟩
  · right
    exact ⟨by simpa [p, q', liftWalkOnCycle_edges] using
        congrArg (fun x => x.edges.toFinset) hpEq,
      by simpa [q, p', liftWalkOnCycle_edges] using
        congrArg (fun x => x.edges.toFinset) hqEq⟩



/-- Swap the two base arcs while keeping the external branch. -/
def swapThetaBaseArcs (G : Erdos1016.PhysicalGraph) {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) :
    ThetaPaths G.toSimpleGraph u v where
  left := t.right
  right := t.left
  external := t.external
  left_path := t.right_path
  right_path := t.left_path
  external_path := t.external_path
  left_right_vertices := fun x hx hy => t.left_right_vertices x hy hx
  left_external_vertices := t.right_external_vertices
  right_external_vertices := t.left_external_vertices
  left_right_edges := fun e he hne => t.left_right_edges e hne he
  left_external_edges := t.right_external_edges
  right_external_edges := t.left_external_edges













/-- General selected-code recovery for any of the three constituent tags.
Once the source and chosen theta have the same tagged pair of arcs, the
existing physical-word lemma identifies the source with the decoded code. -/
theorem selectedThetaCode_recovery_of_arcCorrespondence
    (G : Erdos1016.PhysicalGraph) {bases : Finset G.CycleWord} {s L : ℕ}
    {w : Erdos1016.Proof.PhysicalThetaCandidates.Candidate G bases s L}
    (R : Erdos1016.Proof.PhysicalThetaCandidates.CandidateRealization G w)
    (t : ThetaPaths G.toSimpleGraph (candidateEndpoints G w).1
      (candidateEndpoints G w).2)
    (huv : (candidateEndpoints G w).1 ≠ (candidateEndpoints G w).2)
    (sourceTag candidateTag : Fin 3) (source : G.CycleWord)
    (hsource : source = thetaPairWord G t huv sourceTag)
    (harcs : ArcPairCorrespondence G
      (thetaPairPaths G t sourceTag).1 (thetaPairPaths G t sourceTag).2
      (thetaPairPaths G
        (Erdos1016.Proof.PhysicalThetaCandidates.chosenThetaPaths G R)
        candidateTag).1
      (thetaPairPaths G
        (Erdos1016.Proof.PhysicalThetaCandidates.chosenThetaPaths G R)
        candidateTag).2) :
    source = Erdos1016.Proof.PhysicalThetaCandidates.chosenConstituentWord G R
      candidateTag := by
  exact Erdos1016.Proof.PhysicalThetaCandidates.sourceCycle_eq_candidateTag_of_arcCorrespondence
    G source R t huv sourceTag candidateTag hsource harcs




end Erdos1016.Proof.ThetaSupportArcUniqueness
