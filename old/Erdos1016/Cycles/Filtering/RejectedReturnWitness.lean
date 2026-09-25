import Erdos1016.Cycles.Filtering.RejectedCycleEncoding
import Erdos1016.Cycles.Filtering.ReturnExclusion

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Erdos1016.Proof.RejectedReturnWitness

open Erdos1016
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.PhysicalThetaCandidates
open Erdos1016.Proof.RejectedCycleEncoding

open Erdos1016.Proof.ExternalReturnFilter
open Erdos1016.BoundaryDecay
open SimpleGraph

variable (G : PhysicalGraph)

private def adjoinedReturnPath {u v r s : G.Vertex}
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v)
    (p : G.toSimpleGraph.Walk r s) : G.toSimpleGraph.Walk u v :=
  Walk.cons hru.symm (p.append (Walk.cons hsv Walk.nil))

private theorem adjoinedReturnPath_support {u v r s : G.Vertex}
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v)
    (p : G.toSimpleGraph.Walk r s) :
    (adjoinedReturnPath G hru hsv p).support = u :: (p.support ++ [v]) := by
  simp [adjoinedReturnPath, Walk.support_cons, Walk.support_append]

private theorem adjoinedReturnPath_length {u v r s : G.Vertex}
    (hru : G.toSimpleGraph.Adj r u) (hsv : G.toSimpleGraph.Adj s v)
    (p : G.toSimpleGraph.Walk r s) :
    (adjoinedReturnPath G hru hsv p).length = p.length + 2 := by
  simp [adjoinedReturnPath, Walk.length_cons, Walk.length_append]

/-- A cycle word omitted by the retained filter has an external simple return
of length at most `q`, once its representative cycle walk is chosen. -/
theorem rejected_cycle_has_short_external_return
    {V : Finset G.Vertex} {bases : Finset G.CycleWord} {q : ℕ}
    (C : G.CycleWord) (hbase : C ∈ bases)
    (hnot : C ∉ acceptedShortReturnCycles G V bases q) :
    ∃ a : G.Vertex, ∃ (c : G.toSimpleGraph.Walk a a) (hc : c.IsCycle),
      ∃ (hword : cycleWordOfWalk G c hc = C), ∃ u v : G.Vertex,
      ∃ (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v),
      ∃ (route : G.toSimpleGraph.Walk u v),
      route.IsPath ∧ route.length ≤ q ∧
      (∀ z, z ∈ route.support → z ≠ u → z ≠ v → z ∉ c.support) ∧
      (∀ e, e ∈ route.edges → e ∉ c.edges) := by
  classical
  obtain ⟨a, c, hc, hword⟩ := exists_cycle_walk_of_cycleWord G C
  have hwordValue : walkWord G c = C.1 := by
    exact congrArg Subtype.val hword
  have hvertices : Cycle.vertices C = c.support.toFinset := by
    ext z
    rw [Cycle.vertices, ← hwordValue]
    simpa using (used_walkWord_iff G c hc z)
  have hnoReturn :
      ¬ NoShortExternalReturnWithin G V (Cycle.vertices C) q := by
    intro hgood
    apply hnot
    exact Finset.mem_filter.mpr ⟨hbase, hgood⟩
  simp only [NoShortExternalReturnWithin] at hnoReturn
  push_neg at hnoReturn
  obtain ⟨r, s, u, v, huC, hvC, huv, hru, hsv, p, hp, hpV, hpC, hpnotlen⟩ := hnoReturn
  have hrnotC : r ∉ c.support := by
    intro hrC
    have hrnotCycleVertices : r ∉ Cycle.vertices C := hpC r p.start_mem_support
    exact hrnotCycleVertices (by simpa [hvertices] using hrC)
  have hsnotC : s ∉ c.support := by
    intro hsC
    have hsnotCycleVertices : s ∉ Cycle.vertices C := hpC s p.end_mem_support
    exact hsnotCycleVertices (by simpa [hvertices] using hsC)
  have huC' : u ∈ c.support := by
    simpa [hvertices] using huC
  have hvC' : v ∈ c.support := by
    simpa [hvertices] using hvC
  let route := adjoinedReturnPath G hru hsv p
  have hrouteSupport := adjoinedReturnPath_support G hru hsv p
  have huNotP : u ∉ p.support := by
    intro huP
    exact (hpC u huP) huC
  have hvNotP : v ∉ p.support := by
    intro hvP
    exact (hpC v hvP) hvC
  have hroutePath : route.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hrouteSupport]
    apply List.nodup_cons.mpr
    constructor
    · simp only [List.mem_append, List.mem_singleton]
      intro hz
      rcases hz with hz | hz
      · exact huNotP hz
      · exact huv hz
    · rw [List.nodup_append]
      refine ⟨hp.support_nodup, by simp, ?_⟩
      intro z hz hzv
      simp only [List.mem_singleton] at hzv
      subst z
      exact hvNotP hz
  have hrouteLength : route.length ≤ q := by
    have hlen : route.length = p.length + 2 := by
      simpa [route] using adjoinedReturnPath_length G hru hsv p
    omega
  have hrouteInterior : ∀ z, z ∈ route.support → z ≠ u → z ≠ v → z ∉ c.support := by
    intro z hz hzu hzv
    rw [hrouteSupport] at hz
    simp only [List.mem_cons] at hz
    rcases hz with hzu' | hz
    · exact (hzu hzu').elim
    · simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hzP | hzV
      · intro hzCycle
        exact (hpC z hzP) (by simpa [hvertices] using hzCycle)
      · exact (hzv hzV).elim
  have hrouteEdges : ∀ e, e ∈ route.edges → e ∉ c.edges := by
    intro e he heCycle
    have hrouteEdges' : route.edges = s(u, r) :: (p.edges ++ [s(s, v)]) := by
      simp [route, adjoinedReturnPath, Walk.edges_cons, Walk.edges_append]
    rw [hrouteEdges'] at he
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at he
    rcases he with heFirst | heMid | heLast
    · subst e
      exact hrnotC (c.snd_mem_support_of_mem_edges heCycle)
    · induction e using Sym2.inductionOn with
      | hf x y =>
        have hpX := p.fst_mem_support_of_mem_edges (by simpa using heMid)
        have hcX := c.fst_mem_support_of_mem_edges (by simpa using heCycle)
        exact (hpC x hpX) (by simpa [hvertices] using hcX)
    · rcases heLast with heLast | hfalse
      · subst e
        exact hsnotC (c.fst_mem_support_of_mem_edges heCycle)
      · simp at hfalse
  refine ⟨a, c, hc, hword, u, v, huC', hvC', huv, route,
    hroutePath, hrouteLength, hrouteInterior, hrouteEdges⟩



end Erdos1016.Proof.RejectedReturnWitness

end
