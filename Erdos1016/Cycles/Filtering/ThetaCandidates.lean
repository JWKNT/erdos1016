import Erdos1016.Nonbacktracking.Walks.PathRunEncoding
import Erdos1016.Cycles.Geometry.CycleWalkExistence
import Erdos1016.Cycles.Filtering.ReturnTheta

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.PhysicalThetaCandidates

open Erdos1016.BoundaryDecay
open Erdos1016.Proof.PathEndpointRunInjection
open Erdos1016.Nonbacktracking
open Erdos1016.Proof.ExternalReturnTheta

variable (G : PhysicalGraph)



/-- The two branches selected by a constituent tag. -/
def thetaPairPaths {u v : G.Vertex} (t : ThetaPaths G.toSimpleGraph u v)
    (i : Fin 3) : G.toSimpleGraph.Walk u v × G.toSimpleGraph.Walk u v :=
  if i.val = 0 then (t.left, t.right)
  else if i.val = 1 then (t.left, t.external)
  else (t.external, t.right)

def thetaPairWalk {u v : G.Vertex} (t : ThetaPaths G.toSimpleGraph u v)
    (i : Fin 3) : G.toSimpleGraph.Walk u u :=
  (thetaPairPaths G t i).1.append (thetaPairPaths G t i).2.reverse

theorem thetaPairWalk_isCycle {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v) (i : Fin 3) :
    (thetaPairWalk G t i).IsCycle := by
  fin_cases i
  · simpa [thetaPairWalk, thetaPairPaths, leftRightCycle] using
      (ExternalReturnTheta.leftRightCycle_isCycle G.toSimpleGraph t huv)
  · simpa [thetaPairWalk, thetaPairPaths, leftExternalCycle] using
      (ExternalReturnTheta.leftExternalCycle_isCycle G.toSimpleGraph t huv)
  · simpa [thetaPairWalk, thetaPairPaths, externalRightCycle] using
      (ExternalReturnTheta.externalRightCycle_isCycle G.toSimpleGraph t huv)

noncomputable def thetaPairWord {u v : G.Vertex}
    (t : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v) (i : Fin 3) : G.CycleWord :=
  cycleWordOfWalk G (thetaPairWalk G t i) (thetaPairWalk_isCycle G t huv i)

/-- Two pairs of endpoint-to-endpoint branches correspond when their arc
edge sets agree, allowing the two arcs to be swapped. -/
def ArcPairCorrespondence {u v : G.Vertex}
    (p q p' q' : G.toSimpleGraph.Walk u v) : Prop :=
  (p.edges.toFinset = p'.edges.toFinset ∧ q.edges.toFinset = q'.edges.toFinset) ∨
  (p.edges.toFinset = q'.edges.toFinset ∧ q.edges.toFinset = p'.edges.toFinset)

/-- Ordered endpoint pairs lying on a physical cycle word. -/
def cycleEndpointPairs (C : G.CycleWord) : Finset (G.Vertex × G.Vertex) :=
  Finset.univ.filter fun p =>
    p.1 ∈ BoundaryDecay.Cycle.vertices C ∧
      p.2 ∈ BoundaryDecay.Cycle.vertices C

/-- Finite physical candidates for a theta: its shortest-pair base cycle,
ordered endpoints on the base support, and the remaining simple branch of
length `s < a ≤ L`. -/
abbrev Candidate (bases : Finset G.CycleWord) (s L : ℕ) :=
  Σ C : {C : G.CycleWord // C ∈ bases},
    Σ e : {e : G.Vertex × G.Vertex // e ∈ cycleEndpointPairs G C.1},
      Σ a : Finset.Ioc s L,
        FixedEndpointSimplePaths G a.1 e.1.1 e.1.2

def candidateCycle {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) : G.CycleWord := w.1.1

def candidateEndpoints {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) : G.Vertex × G.Vertex := w.2.1.1

def candidateBranchLength {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) : ℕ := w.2.2.1.1

def candidatePath {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) := w.2.2.2.1

def candidatePath_isPath {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) : (candidatePath G w).IsPath := w.2.2.2.2.1

/-- A realization supplies the physical base-cycle walk and the externality
facts needed to extract its theta. -/
structure CandidateRealization {bases : Finset G.CycleWord} {s L : ℕ}
    (w : Candidate G bases s L) where
  root : G.Vertex
  baseWalk : G.toSimpleGraph.Walk root root
  base_isCycle : baseWalk.IsCycle
  word_eq : cycleWordOfWalk G baseWalk base_isCycle = candidateCycle G w
  left_on_base : (candidateEndpoints G w).1 ∈ baseWalk.support
  right_on_base : (candidateEndpoints G w).2 ∈ baseWalk.support
  endpoints_ne : (candidateEndpoints G w).1 ≠ (candidateEndpoints G w).2
  branch_interior : ∀ z, z ∈ (candidatePath G w).support →
    z ≠ (candidateEndpoints G w).1 → z ≠ (candidateEndpoints G w).2 →
    z ∉ baseWalk.support
  branch_edges : ∀ e, e ∈ (candidatePath G w).edges → e ∉ baseWalk.edges


/-- The candidate family is finite: each layer is a finite subtype or a
fixed-length simple-path type already injected into endpoint runs. -/
noncomputable instance candidateFintype
    (bases : Finset G.CycleWord) (s L : ℕ) : Fintype (Candidate G bases s L) := by
  classical
  infer_instance



/-- Length bridge for an actual physical cycle-word representative used by
the theta decomposition. -/
theorem candidate_cycle_walk_length_eq
    (bases : Finset G.CycleWord) (s L : ℕ) (w : Candidate G bases s L)
    {x : G.Vertex} (c : G.toSimpleGraph.Walk x x) (hc : c.IsCycle)
    (hword : cycleWordOfWalk G c hc = candidateCycle G w) :
    G.wordLength (candidateCycle G w).1 = c.length := by
  calc
    G.wordLength (candidateCycle G w).1 =
        BoundaryDecay.Cycle.length (candidateCycle G w) := rfl
    _ = BoundaryDecay.Cycle.length (cycleWordOfWalk G c hc) :=
      congrArg BoundaryDecay.Cycle.length hword.symm
    _ = c.length := cycleWordOfWalk_length G c hc

/-- A walk representing the shortest-pair base, together with the long
remaining branch, yields the three theta branches. This base walk is kept
separate from the source excluded cycle; that source is recovered only after
the constituent tag is supplied. -/
theorem candidate_externalReturn_theta
    (bases : Finset G.CycleWord) (s L : ℕ) (w : Candidate G bases s L)
    {x : G.Vertex} (baseWalk : G.toSimpleGraph.Walk x x) (hbaseWalk : baseWalk.IsCycle)
    (hword : cycleWordOfWalk G baseWalk hbaseWalk = candidateCycle G w)
    (hu : (candidateEndpoints G w).1 ∈ baseWalk.support)
    (hv : (candidateEndpoints G w).2 ∈ baseWalk.support)
    (huv : (candidateEndpoints G w).1 ≠ (candidateEndpoints G w).2)
    (hinterior : ∀ z, z ∈ (candidatePath G w).support →
      z ≠ (candidateEndpoints G w).1 → z ≠ (candidateEndpoints G w).2 →
      z ∉ baseWalk.support)
    (hedges : ∀ e, e ∈ (candidatePath G w).edges → e ∉ baseWalk.edges) :
    ∃ t : ThetaPaths G.toSimpleGraph (candidateEndpoints G w).1
        (candidateEndpoints G w).2,
      leftRightCycle G.toSimpleGraph t = baseWalk.rotate hu ∧
      (leftRightCycle G.toSimpleGraph t).IsCycle ∧
      (leftExternalCycle G.toSimpleGraph t).IsCycle ∧
      (externalRightCycle G.toSimpleGraph t).IsCycle ∧
      G.wordLength (candidateCycle G w).1 = t.left.length + t.right.length ∧
      t.external = candidatePath G w := by
  obtain ⟨t, hbase, hbaseCycle, hleftExtCycle, hrightExtCycle, _, _, _, hext⟩ :=
    ExternalReturnTheta.externalReturn_theta G.toSimpleGraph baseWalk hbaseWalk hu hv huv
      (candidatePath G w) (candidatePath_isPath G w) hinterior hedges
  have hlength := candidate_cycle_walk_length_eq G bases s L w baseWalk hbaseWalk hword
  have hsum := ExternalReturnTheta.theta_base_length_eq_cycle_length
    G.toSimpleGraph baseWalk hu t hbase
  exact ⟨t, hbase, hbaseCycle, hleftExtCycle, hrightExtCycle,
    hlength.trans hsum, hext⟩

/-- Rotating a closed walk only changes the order of its edge list, not its
physical edge word. -/
theorem walkWord_rotate_eq {x u : G.Vertex} (c : G.toSimpleGraph.Walk x x)
    (hu : u ∈ c.support) : walkWord G (c.rotate hu) = walkWord G c := by
  funext e
  have hperm := SimpleGraph.Walk.rotate_edges c hu
  have hmem : physicalPair G e ∈ (c.rotate hu).edges ↔ physicalPair G e ∈ c.edges :=
    hperm.mem_iff
  by_cases he : physicalPair G e ∈ c.edges
  · have he' : physicalPair G e ∈ (c.rotate hu).edges := hmem.mpr he
    have hnz₁ : walkWord G (c.rotate hu) e ≠ 0 :=
      (walkWord_nonzero_iff G (c.rotate hu) e).2 he'
    have hnz₂ : walkWord G c e ≠ 0 :=
      (walkWord_nonzero_iff G c e).2 he
    have hone (z : F₂) (hz : z ≠ 0) : z = 1 := by
      fin_cases z <;> simp_all
    rw [hone _ hnz₁, hone _ hnz₂]
  · have he' : physicalPair G e ∉ (c.rotate hu).edges := by
      intro hr
      exact he (hmem.mp hr)
    have hz₁ : walkWord G (c.rotate hu) e = 0 := by
      by_contra hnz
      exact he' ((walkWord_nonzero_iff G (c.rotate hu) e).1 hnz)
    have hz₂ : walkWord G c e = 0 := by
      by_contra hnz
      exact he ((walkWord_nonzero_iff G c e).1 hnz)
    rw [hz₁, hz₂]

theorem walkWord_eq_of_edges_toFinset_eq {u v : G.Vertex}
    (p q : G.toSimpleGraph.Walk u v)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    walkWord G p = walkWord G q := by
  funext e
  have binary (x : F₂) : x = 0 ∨ x = 1 := by
    fin_cases x <;> simp
  by_cases hp : physicalPair G e ∈ p.edges
  · have hp' : physicalPair G e ∈ p.edges.toFinset := List.mem_toFinset.mpr hp
    have hq' : physicalPair G e ∈ q.edges.toFinset := by rw [← hedges]; exact hp'
    have hq : physicalPair G e ∈ q.edges := List.mem_toFinset.mp hq'
    have hnzp : walkWord G p e ≠ 0 := (walkWord_nonzero_iff G p e).2 hp
    have hnzq : walkWord G q e ≠ 0 := (walkWord_nonzero_iff G q e).2 hq
    have hone (x : F₂) (hx : x ≠ 0) : x = 1 := by
      rcases binary x with hz | hone
      · exact (hx hz).elim
      · exact hone
    rw [hone _ hnzp, hone _ hnzq]
  · have hq : physicalPair G e ∉ q.edges := by
      intro hq
      exact hp ((List.mem_toFinset.mp (hedges ▸ List.mem_toFinset.mpr hq)))
    have hpzero : walkWord G p e = 0 := by
      by_contra hnz
      exact hp ((walkWord_nonzero_iff G p e).1 hnz)
    have hqzero : walkWord G q e = 0 := by
      by_contra hnz
      exact hq ((walkWord_nonzero_iff G q e).1 hnz)
    rw [hpzero, hqzero]

theorem thetaPairWord_eq_of_arcCorrespondence {u v : G.Vertex}
    (t t' : ThetaPaths G.toSimpleGraph u v) (huv : u ≠ v)
    (i j : Fin 3)
    (harcs : ArcPairCorrespondence G
      (thetaPairPaths G t i).1 (thetaPairPaths G t i).2
      (thetaPairPaths G t' j).1 (thetaPairPaths G t' j).2) :
    thetaPairWord G t huv i = thetaPairWord G t' huv j := by
  apply Subtype.ext
  apply walkWord_eq_of_edges_toFinset_eq G
  unfold thetaPairWalk
  simp only [SimpleGraph.Walk.edges_append, List.toFinset_append,
    SimpleGraph.Walk.edges_reverse, List.toFinset_reverse]
  rcases harcs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂]
    ac_rfl


theorem cycleWordOfWalk_rotate_eq {x u : G.Vertex}
    (c : G.toSimpleGraph.Walk x x) (hc : c.IsCycle) (hu : u ∈ c.support) :
    cycleWordOfWalk G (c.rotate hu) (hc.rotate hu) = cycleWordOfWalk G c hc := by
  apply Subtype.ext
  exact walkWord_rotate_eq G c hu

/-- In the decomposition returned for an external return, the original
source cycle is exactly the physical word of the left-right constituent. -/
theorem sourceCycleWord_eq_externalReturn_base
    {x u v : G.Vertex} (source : G.toSimpleGraph.Walk x x)
    (hsource : source.IsCycle) (hu : u ∈ source.support)
    (huv : u ≠ v)
    (t : ThetaPaths G.toSimpleGraph u v)
    (hdecomp : leftRightCycle G.toSimpleGraph t = source.rotate hu) :
    cycleWordOfWalk G source hsource =
      cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t)
        (leftRightCycle_isCycle G.toSimpleGraph t huv) := by
  apply Subtype.ext
  change walkWord G source = walkWord G (leftRightCycle G.toSimpleGraph t)
  rw [hdecomp]
  exact (walkWord_rotate_eq G source hu).symm

/-- The classical theta selected for a physical candidate. -/
noncomputable def chosenThetaPaths {bases : Finset G.CycleWord} {s L : ℕ}
    {w : Candidate G bases s L} (R : CandidateRealization G w) :
    ThetaPaths G.toSimpleGraph (candidateEndpoints G w).1
      (candidateEndpoints G w).2 :=
  Classical.choose (candidate_externalReturn_theta G bases s L w R.baseWalk
    R.base_isCycle R.word_eq R.left_on_base R.right_on_base R.endpoints_ne
    R.branch_interior R.branch_edges)

theorem chosenThetaPaths_spec {bases : Finset G.CycleWord} {s L : ℕ}
    {w : Candidate G bases s L} (R : CandidateRealization G w) :
    leftRightCycle G.toSimpleGraph (chosenThetaPaths G R) =
        R.baseWalk.rotate R.left_on_base ∧
      (leftRightCycle G.toSimpleGraph (chosenThetaPaths G R)).IsCycle ∧
      (leftExternalCycle G.toSimpleGraph (chosenThetaPaths G R)).IsCycle ∧
      (externalRightCycle G.toSimpleGraph (chosenThetaPaths G R)).IsCycle ∧
      G.wordLength (candidateCycle G w).1 =
        (chosenThetaPaths G R).left.length + (chosenThetaPaths G R).right.length ∧
      (chosenThetaPaths G R).external = candidatePath G w :=
  Classical.choose_spec (candidate_externalReturn_theta G bases s L w R.baseWalk
    R.base_isCycle R.word_eq R.left_on_base R.right_on_base R.endpoints_ne
    R.branch_interior R.branch_edges)

/-- The three constituent physical cycle words, indexed by their omitted
theta branch: the base pair, left-plus-external, or external-plus-right. -/
noncomputable def chosenConstituentWord {bases : Finset G.CycleWord} {s L : ℕ}
    {w : Candidate G bases s L} (R : CandidateRealization G w) (i : Fin 3) :
    G.CycleWord := by
  classical
  let t := chosenThetaPaths G R
  by_cases hi0 : i.val = 0
  · exact cycleWordOfWalk G (leftRightCycle G.toSimpleGraph t)
      (leftRightCycle_isCycle G.toSimpleGraph t R.endpoints_ne)
  · by_cases hi1 : i.val = 1
    · exact cycleWordOfWalk G (leftExternalCycle G.toSimpleGraph t)
        (leftExternalCycle_isCycle G.toSimpleGraph t R.endpoints_ne)
    · exact cycleWordOfWalk G (externalRightCycle G.toSimpleGraph t)
        (externalRightCycle_isCycle G.toSimpleGraph t R.endpoints_ne)







theorem chosenConstituentWord_eq_thetaPairWord
    {bases : Finset G.CycleWord} {s L : ℕ}
    {w : Candidate G bases s L} (R : CandidateRealization G w) (i : Fin 3) :
    chosenConstituentWord G R i =
      thetaPairWord G (chosenThetaPaths G R) R.endpoints_ne i := by
  fin_cases i <;> rfl

/-- Source recovery from the explicit cycle-arc correspondence. This is the
minimum-pair comparison boundary: prove the two source branches are exactly
the two candidate theta arcs, up to swapping, and the cycle word follows. -/
theorem sourceCycle_eq_candidateTag_of_arcCorrespondence
    {bases : Finset G.CycleWord} {s L : ℕ}
    (source : G.CycleWord)
    {w : Candidate G bases s L} (R : CandidateRealization G w)
    (sourceTheta : ThetaPaths G.toSimpleGraph
      (candidateEndpoints G w).1 (candidateEndpoints G w).2)
    (sourceHuV : (candidateEndpoints G w).1 ≠ (candidateEndpoints G w).2)
    (sourceTag : Fin 3)
    (candidateTag : Fin 3)
    (hsource : source = thetaPairWord G sourceTheta sourceHuV sourceTag)
    (harcs : ArcPairCorrespondence G
      (thetaPairPaths G sourceTheta sourceTag).1
      (thetaPairPaths G sourceTheta sourceTag).2
      (thetaPairPaths G (chosenThetaPaths G R) candidateTag).1
      (thetaPairPaths G (chosenThetaPaths G R) candidateTag).2) :
      source = chosenConstituentWord G R candidateTag := by
  calc
    source = thetaPairWord G sourceTheta sourceHuV sourceTag := hsource
    _ = thetaPairWord G (chosenThetaPaths G R) R.endpoints_ne candidateTag :=
      thetaPairWord_eq_of_arcCorrespondence G sourceTheta (chosenThetaPaths G R)
        sourceHuV sourceTag candidateTag harcs
    _ = chosenConstituentWord G R candidateTag :=
      (chosenConstituentWord_eq_thetaPairWord G R candidateTag).symm

/-- The finite subtype of candidates for which all walk-representation and
externality data needed by the theta construction have been supplied. -/
abbrev RealizableCandidate (bases : Finset G.CycleWord) (s L : ℕ) :=
  {w : Candidate G bases s L // Nonempty (CandidateRealization G w)}

noncomputable instance realizableCandidateFintype
    (bases : Finset G.CycleWord) (s L : ℕ) :
    Fintype (RealizableCandidate G bases s L) := by
  classical
  infer_instance

/-- Fix the realization for a valid candidate once, so its three constituent
cycle words define a concrete recovery map on the finite tagged family. -/
noncomputable def chosenCandidateRealization
    {bases : Finset G.CycleWord} {s L : ℕ}
    (w : RealizableCandidate G bases s L) : CandidateRealization G w.1 :=
  Classical.choice w.2

def recoverThetaTagCycle {bases : Finset G.CycleWord} {s L : ℕ}
    (code : RealizableCandidate G bases s L × Fin 3) : G.CycleWord :=
  chosenConstituentWord G (chosenCandidateRealization G code.1) code.2













end Erdos1016.Proof.PhysicalThetaCandidates
end
