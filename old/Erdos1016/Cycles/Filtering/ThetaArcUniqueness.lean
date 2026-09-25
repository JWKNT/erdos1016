import Erdos1016.Cycles.Filtering.MinimumPairTransport

set_option autoImplicit false

namespace Erdos1016.Proof.ThetaArcUniqueness

open Erdos1016.Proof.ExternalReturnTheta
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.PhysicalThetaPairRelabel
open Erdos1016.Proof.MinimumPairArcTransport
open Erdos1016.Proof.PathEndpointRunInjection
open Erdos1016.Nonbacktracking
open Erdos1016.BoundaryDecay
open SimpleGraph

variable (G : Erdos1016.PhysicalGraph)







private theorem physicalPair_exists_local {a : Sym2 G.Vertex}
    (ha : a ∈ G.toSimpleGraph.edgeSet) :
    ∃ e : G.Edge, physicalPair G e = a := by
  revert ha
  refine Sym2.inductionOn a ?_
  intro u v huv
  rcases huv with ⟨e, _, h | h⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inl h)⟩
  · exact ⟨e, Sym2.eq_iff.2 (Or.inr h)⟩

private theorem walkWord_edge_image_local {u v : G.Vertex}
    (p : G.toSimpleGraph.Walk u v) :
    (G.edgeSupport (walkWord G p)).image (physicalPair G) = p.edges.toFinset := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ha
    apply List.mem_toFinset.2
    exact (walkWord_nonzero_iff G p e).1 (Finset.mem_filter.1 he).2
  · intro ha
    have hm : a ∈ p.edges := List.mem_toFinset.1 ha
    have hbase : a ∈ G.toSimpleGraph.edgeSet :=
      p.toSubgraph.edgeSet_subset ((p.mem_edges_toSubgraph).2 hm)
    obtain ⟨e, he⟩ := physicalPair_exists_local G hbase
    refine Finset.mem_image.2 ⟨e, ?_, he⟩
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _, (walkWord_nonzero_iff G p e).2 ?_⟩
    rwa [he]

/-- Equality of physical cycle words fixes the actual unordered edge set of
any two simple-walk representatives. -/
theorem cycleWord_eq_edges_toFinset_eq {u v : G.Vertex}
    (c d : G.toSimpleGraph.Walk u u)
    (hc : c.IsCycle) (hd : d.IsCycle)
    (hword : cycleWordOfWalk G c hc = cycleWordOfWalk G d hd) :
    c.edges.toFinset = d.edges.toFinset := by
  have h := congrArg
    (fun C : G.CycleWord => (G.edgeSupport C.1).image (physicalPair G)) hword
  simpa only [cycleWordOfWalk, walkWord_edge_image_local] using h













/-- Canonical realization built from the explicit minimum-pair relabeling.
The two equalities are exactly the candidate-code checks: the candidate base
word represents the selected source pair-cycle, and its path is the omitted
source branch. -/
noncomputable def candidateRealizationOfSourceTheta
    {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L)
    (sourceTheta : ThetaPaths G.toSimpleGraph
      (candidateEndpoints G w).1 (candidateEndpoints G w).2)
    (p : ThetaPair)
    (huv : (candidateEndpoints G w).1 ≠ (candidateEndpoints G w).2)
    (hword : cycleWordOfWalk G
        (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
        (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p)
          huv)
        = candidateCycle G w)
    (hpath : candidatePath G w =
        (thetaAtPair sourceTheta p).external) :
    CandidateRealization G w := by
  let t := thetaAtPair sourceTheta p
  refine ⟨(candidateEndpoints G w).1, leftRightCycle G.toSimpleGraph t,
    leftRightCycle_isCycle G.toSimpleGraph t huv,
    ?_, Walk.start_mem_support (leftRightCycle G.toSimpleGraph t), ?_, ?_, ?_, ?_⟩
  · exact hword
  · exact (Walk.mem_support_append_iff t.left t.right.reverse).2
      (Or.inl t.left.end_mem_support)
  · exact huv
  · intro z hz hzu hzv hzbase
    rw [hpath] at hz
    rcases (Walk.mem_support_append_iff t.left t.right.reverse).1 hzbase with hzleft | hzright
    · rcases t.left_external_vertices z hzleft hz with h | h <;> tauto
    · have hzright' : z ∈ t.right.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hzright
      rcases t.right_external_vertices z hzright' hz with h | h <;> tauto
  · intro e he hebase
    rw [hpath] at he
    change e ∈ (t.left.append t.right.reverse).edges at hebase
    simp only [Walk.edges_append, List.mem_append] at hebase
    rcases hebase with hleft | hright
    · exact t.left_external_edges e hleft he
    · have hright' : e ∈ t.right.edges := by
        simpa only [Walk.edges_reverse, List.mem_reverse] using hright
      exact t.right_external_edges e hright' he





/-- Encode a source theta as its minimum-pair base, ordered endpoints, and
omitted simple branch. This is the concrete candidate construction used by
the charging step; its source-to-code cycle and path equalities are reflexive. -/
noncomputable def candidateOfSourceTheta
    (bases : Finset G.CycleWord) (s L : ℕ)
    {u v : G.Vertex}
    (sourceTheta : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (p : ThetaPair)
    (hbase : cycleWordOfWalk G
      (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
      (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p) huv)
      ∈ bases)
    (hs : s < (thetaAtPair sourceTheta p).external.length)
    (hL : (thetaAtPair sourceTheta p).external.length ≤ L) :
    Candidate G bases s L := by
  let t := thetaAtPair sourceTheta p
  let C := cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t)
    (leftRightCycle_isCycle G.toSimpleGraph t huv)
  have huC : u ∈ Cycle.vertices C := by
    change u ∈ G.usedVertices (walkWord G (leftRightCycle G.toSimpleGraph t))
    exact (used_walkWord_iff G (leftRightCycle G.toSimpleGraph t)
      (leftRightCycle_isCycle G.toSimpleGraph t huv) u).2
      (Walk.start_mem_support (leftRightCycle G.toSimpleGraph t))
  have hvC : v ∈ Cycle.vertices C := by
    change v ∈ G.usedVertices (walkWord G (leftRightCycle G.toSimpleGraph t))
    exact (used_walkWord_iff G (leftRightCycle G.toSimpleGraph t)
      (leftRightCycle_isCycle G.toSimpleGraph t huv) v).2
      ((Walk.mem_support_append_iff t.left t.right.reverse).2
        (Or.inl t.left.end_mem_support))
  let endpoints : G.Vertex × G.Vertex := (u, v)
  let endpointMember : endpoints ∈ cycleEndpointPairs G C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, huC, hvC⟩
  let a : ↥(Finset.Ioc s L) :=
    ⟨t.external.length, Finset.mem_Ioc.mpr ⟨hs, hL⟩⟩
  let branch : FixedEndpointSimplePaths G a.1 u v :=
    ⟨t.external, t.external_path, rfl, by simpa [a] using Nat.zero_lt_of_lt hs⟩
  refine ⟨⟨C, hbase⟩, ?_⟩
  refine ⟨⟨endpoints, endpointMember⟩, ?_⟩
  exact ⟨a, branch⟩

theorem candidateOfSourceTheta_cycle_eq
    (bases : Finset G.CycleWord) (s L : ℕ)
    {u v : G.Vertex}
    (sourceTheta : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (p : ThetaPair)
    (hbase : cycleWordOfWalk G
      (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
      (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p) huv)
      ∈ bases)
    (hs : s < (thetaAtPair sourceTheta p).external.length)
    (hL : (thetaAtPair sourceTheta p).external.length ≤ L) :
    candidateCycle G (candidateOfSourceTheta G bases s L sourceTheta huv p
      hbase hs hL) =
      cycleWordOfWalk G
        (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
        (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p) huv) := rfl

theorem candidateOfSourceTheta_path_eq
    (bases : Finset G.CycleWord) (s L : ℕ)
    {u v : G.Vertex}
    (sourceTheta : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (p : ThetaPair)
    (hbase : cycleWordOfWalk G
      (leftRightCycle G.toSimpleGraph (thetaAtPair sourceTheta p))
      (leftRightCycle_isCycle G.toSimpleGraph (thetaAtPair sourceTheta p) huv)
      ∈ bases)
    (hs : s < (thetaAtPair sourceTheta p).external.length)
    (hL : (thetaAtPair sourceTheta p).external.length ≤ L) :
    candidatePath G (candidateOfSourceTheta G bases s L sourceTheta huv p
      hbase hs hL) = (thetaAtPair sourceTheta p).external := rfl



/-! ### Full oriented theta codes -/

/-- An oriented theta code keeps the two base arcs ordered. This avoids the
loss of arc orientation in a candidate consisting only of a base cycle word,
endpoints, and omitted path. -/
structure OrientedThetaCode (G : PhysicalGraph) where
  leftEndpoint : G.Vertex
  rightEndpoint : G.Vertex
  endpoints_ne : leftEndpoint ≠ rightEndpoint
  paths : ThetaPaths G.toSimpleGraph leftEndpoint rightEndpoint





end Erdos1016.Proof.ThetaArcUniqueness
