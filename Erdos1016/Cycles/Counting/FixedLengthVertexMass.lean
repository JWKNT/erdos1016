import Erdos1016.Nonbacktracking.Walks.RootedCyclePrefixes
import Erdos1016.Cycles.Filtering.ReturnRunCounts

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace Erdos1016.Proof.FixedLengthVertexMass

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.CycleRootChoice
open Erdos1016.Proof.RootedCyclePrefixes


variable (G : PhysicalGraph)

/-- The length-`ell` physical cycle words that pass through a fixed vertex. -/
noncomputable def cyclesAtVertex (ell : ℕ) (v : G.Vertex) :
    Finset (CycleWordsAtLength G ell) := by
  classical
  exact Finset.univ.filter fun C =>
    v ∈ BoundaryDecay.Cycle.vertices C.1

noncomputable def selectRootAtVertex (ell : ℕ) (v : G.Vertex)
    (C : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v}) :
    RootChoices (chosenRootedSimpleCycle C.1).1.2 :=
  Classical.choose (exists_rootChoice_at_vertex G C.1
    ((Finset.mem_filter.mp C.2).2))

theorem selectRootAtVertex_spec (ell : ℕ) (v : G.Vertex)
    (C : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v}) :
    (selectRootAtVertex G ell v C).1 = v :=
  Classical.choose_spec (exists_rootChoice_at_vertex G C.1
    ((Finset.mem_filter.mp C.2).2))

noncomputable def encodeCyclePrefixAtVertex (ell : ℕ) (v : G.Vertex)
    (C : {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v})
    (orientation : Bool) : EndpointRuns G (ell - 1) v v :=
  rootedCycleEndpointPrefix G (chosenRootedSimpleCycle C.1)
    (selectRootAtVertex G ell v C) (selectRootAtVertex_spec G ell v C) orientation

/-- At a fixed vertex, the two orientations of distinct physical simple
cycles produce distinct endpoint prefixes. The prefix's dart serialization
is exactly the oriented cycle's full dart list, so its physical edge word
recovers the original cycle; the first dart then separates the two
orientations. -/
theorem encodeCyclePrefixAtVertex_injective (ell : ℕ) (v : G.Vertex) :
    Function.Injective (fun z :
      {C : CycleWordsAtLength G ell // C ∈ cyclesAtVertex G ell v} × Bool =>
        encodeCyclePrefixAtVertex G ell v z.1 z.2) := by
  classical
  intro z w h
  rcases z with ⟨⟨C, hC⟩, orientationC⟩
  rcases w with ⟨⟨D, hD⟩, orientationD⟩
  let xC := selectRootAtVertex G ell v ⟨C, hC⟩
  let xD := selectRootAtVertex G ell v ⟨D, hD⟩
  have hxC : xC.1 = v := selectRootAtVertex_spec G ell v ⟨C, hC⟩
  have hxD : xD.1 = v := selectRootAtVertex_spec G ell v ⟨D, hD⟩
  let cC := chosenRootedSimpleCycle C
  let cD := chosenRootedSimpleCycle D
  let qC := rootedOrientedWalk cC.1.2 xC orientationC
  let qD := rootedOrientedWalk cD.1.2 xD orientationD
  have hprefix :
      rootedCycleEndpointPrefix G cC xC hxC orientationC =
        rootedCycleEndpointPrefix G cD xD hxD orientationD := by
    simpa [encodeCyclePrefixAtVertex, xC, xD, cC, cD] using h
  have hdarts : runDarts G (ell - 1)
      (rootedCycleEndpointPrefix G cC xC hxC orientationC).1.2.2 =
      runDarts G (ell - 1)
      (rootedCycleEndpointPrefix G cD xD hxD orientationD).1.2.2 :=
    congrArg (fun p : EndpointRuns G (ell - 1) v v =>
      runDarts G (ell - 1) p.1.2.2) hprefix
  have hwalkDarts : walkDarts G qC = walkDarts G qD := by
    simpa [qC, qD] using
      (rootedCycleEndpointPrefix_darts G cC xC hxC orientationC).symm.trans
        (hdarts.trans (rootedCycleEndpointPrefix_darts G cD xD hxD orientationD))
  have hedges : qC.edges = qD.edges := by
    have h := congrArg (fun ds : List (Dart G) =>
        ds.map (fun d => physicalPair G d.1)) hwalkDarts
    change List.map (fun d => physicalPair G d.1) (walkDarts G qC) =
      List.map (fun d => physicalPair G d.1) (walkDarts G qD) at h
    rw [walkDarts_map_physicalPair, walkDarts_map_physicalPair] at h
    exact h
  have hwordWalk : walkWord G qC = walkWord G qD := by
    funext e
    simp [walkWord, hedges]
  have hwordC : walkWord G qC = C.1.1 := by
    calc
      walkWord G qC = walkWord G cC.1.2 :=
        rootedOrientedWalk_word_eq cC.1.2 xC orientationC
      _ = (cycleWordOfWalk G cC.1.2 cC.2.1).1 := by rfl
      _ = C.1.1 := congrArg Subtype.val (chosenRootedSimpleCycle_word C)
  have hwordD : walkWord G qD = D.1.1 := by
    calc
      walkWord G qD = walkWord G cD.1.2 :=
        rootedOrientedWalk_word_eq cD.1.2 xD orientationD
      _ = (cycleWordOfWalk G cD.1.2 cD.2.1).1 := by rfl
      _ = D.1.1 := congrArg Subtype.val (chosenRootedSimpleCycle_word D)
  have hCDword : C.1.1 = D.1.1 := hwordC.symm.trans (hwordWalk.trans hwordD)
  have hCD : C = D := Subtype.ext (Subtype.ext hCDword)
  have hfirst :
      rootedCycleStartDart cC.1.2 cC.2.1 xC orientationC =
        rootedCycleStartDart cD.1.2 cD.2.1 xD orientationD := by
    have h := congrArg (fun p : EndpointRuns G (ell - 1) v v => p.1.1) hprefix
    simpa [rootedCycleEndpointPrefix, rootedCycleRun, cC, cD] using h
  cases hCD
  have hfirst' :
      rootedCycleStartDart cC.1.2 cC.2.1 xC orientationC =
        rootedCycleStartDart cC.1.2 cC.2.1 xD orientationD := by
    simpa [cC, cD] using hfirst
  have horient : orientationC = orientationD := by
    have hpair : (xC, orientationC) = (xD, orientationD) := by
      apply rootedCycleStartDart_injective cC.1.2 cC.2.1
      exact hfirst'
    exact congrArg Prod.snd hpair
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · exact horient



end Erdos1016.Proof.FixedLengthVertexMass

end
