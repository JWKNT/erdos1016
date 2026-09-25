import Erdos1016.Cleanup.Support.WitnessComponentScreen

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace Erdos1016.Proof.VertexSupportedWitness

open Erdos1016

/-- Vertices that are endpoints of at least one edge in the witness union. -/
def witnessSupportVertices (G : PhysicalGraph) (F : Finset G.CycleWord) : Finset G.Vertex := by
  classical
  exact Finset.univ.filter fun v => ∃ e ∈ witnessSupportEdges G F, G.incident e v

/-- The actual vertex-supported witness graph: edges are exactly the witness
support labels, and vertices are exactly their endpoints. -/
def trimmedWitnessGraph (G : PhysicalGraph) (F : Finset G.CycleWord) : PhysicalGraph := by
  classical
  let S := witnessSupportEdges G F
  let V := witnessSupportVertices G F
  refine {
    vertexCount := V.card
    edgeCount := S.card
    src := fun e => Finset.equivFin V ⟨G.src ((Finset.equivFin S).symm e).1,
      ?_⟩
    dst := fun e => Finset.equivFin V ⟨G.dst ((Finset.equivFin S).symm e).1,
      ?_⟩
    noLoops := ?_
    simple := ?_
  }
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨((Finset.equivFin S).symm e).1, ((Finset.equivFin S).symm e).2,
        Or.inl rfl⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨((Finset.equivFin S).symm e).1, ((Finset.equivFin S).symm e).2,
        Or.inr rfl⟩⟩
  · intro e h
    apply G.noLoops ((Finset.equivFin S).symm e).1
    exact congrArg Subtype.val ((Finset.equivFin V).injective h)
  · intro e f h
    apply (Finset.equivFin S).symm.injective
    apply Subtype.ext
    apply G.simple
    rcases h with h | h
    · exact Or.inl ⟨congrArg Subtype.val ((Finset.equivFin V).injective h.1),
        congrArg Subtype.val ((Finset.equivFin V).injective h.2)⟩
    · exact Or.inr ⟨congrArg Subtype.val ((Finset.equivFin V).injective h.1),
        congrArg Subtype.val ((Finset.equivFin V).injective h.2)⟩

@[simp] theorem trimmedWitnessGraph_vertexCount (G : PhysicalGraph)
    (F : Finset G.CycleWord) :
    (trimmedWitnessGraph G F).vertexCount = (witnessSupportVertices G F).card := rfl

@[simp] theorem trimmedWitnessGraph_edgeCount (G : PhysicalGraph)
    (F : Finset G.CycleWord) :
    (trimmedWitnessGraph G F).edgeCount = (witnessSupportEdges G F).card := rfl

/-- The original host vertex represented by a trimmed-graph vertex. -/
def trimmedHostVertex (G : PhysicalGraph) (F : Finset G.CycleWord)
    (v : (trimmedWitnessGraph G F).Vertex) : G.Vertex :=
  ((Finset.equivFin (witnessSupportVertices G F)).symm v).1

/-- An edge incident to the represented host vertex stays incident after
relabeling the support edges and endpoint vertices. -/
theorem trimmed_incident_of_host_incident
    (G : PhysicalGraph) (F : Finset G.CycleWord)
    (v : (trimmedWitnessGraph G F).Vertex) (e : G.Edge)
    (he : e ∈ witnessSupportEdges G F)
    (hinc : G.incident e (trimmedHostVertex G F v)) :
    (trimmedWitnessGraph G F).incident
      ((Finset.equivFin (witnessSupportEdges G F)) ⟨e, he⟩) v := by
  classical
  let V := witnessSupportVertices G F
  let S := witnessSupportEdges G F
  rcases hinc with hs | hd
  · have hmem : G.src e ∈ V :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, Or.inl rfl⟩⟩
    have hv : (⟨G.src e, hmem⟩ : {x // x ∈ V}) = (Finset.equivFin V).symm v := by
      apply Subtype.ext
      exact hs
    have := congrArg (Finset.equivFin V) hv
    exact Or.inl (by simpa [PhysicalGraph.incident, trimmedWitnessGraph, V, S] using this)
  · have hmem : G.dst e ∈ V :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e, he, Or.inr rfl⟩⟩
    have hv : (⟨G.dst e, hmem⟩ : {x // x ∈ V}) = (Finset.equivFin V).symm v := by
      apply Subtype.ext
      exact hd
    have := congrArg (Finset.equivFin V) hv
    exact Or.inr (by simpa [PhysicalGraph.incident, trimmedWitnessGraph, V, S] using this)

/-- A host cycle that uses a vertex supplies two distinct incident support
edges, hence degree at least two in the trimmed graph. -/
theorem trimmed_degree_ge_two_of_cycle
    (G : PhysicalGraph) (F : Finset G.CycleWord)
    {C : G.CycleWord} (hC : C ∈ F) (v : (trimmedWitnessGraph G F).Vertex)
    (hv : trimmedHostVertex G F v ∈ G.usedVertices C.1) :
    2 ≤ (trimmedWitnessGraph G F).degree v := by
  classical
  let H := trimmedWitnessGraph G F
  let I : Finset G.Edge := Finset.univ.filter fun e =>
    C.1 e ≠ 0 ∧ G.incident e (trimmedHostVertex G F v)
  have hI : I.card = 2 := by
    change G.selectedDegree C.1 (trimmedHostVertex G F v) = 2
    simpa [I, PhysicalGraph.selectedDegree] using C.2.2.2.2
      (trimmedHostVertex G F v) hv
  let f : {e : G.Edge // e ∈ I} → H.Edge := fun e =>
    (Finset.equivFin (witnessSupportEdges G F)) ⟨e.1,
      witnessSupport_edge_mem G F hC
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp e.2).2.1⟩)⟩
  have hf : Function.Injective f := by
    intro x y h
    have hs := (Finset.equivFin (witnessSupportEdges G F)).injective h
    have hxy : x.1 = y.1 :=
      congrArg (fun z : {e : G.Edge // e ∈ witnessSupportEdges G F} => z.1) hs
    exact Subtype.ext hxy
  let J : Finset H.Edge := I.attach.image f
  have hJcard : J.card = 2 := by
    have himage : (I.attach.image f).card = I.attach.card :=
      Finset.card_image_iff.mpr (fun x _ y _ hxy => hf hxy)
    rw [himage]
    simpa [I] using hI
  have hJsubset : J ⊆ Finset.univ.filter fun e : H.Edge => H.incident e v := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨x, hx, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      trimmed_incident_of_host_incident G F v x.1
        (witnessSupport_edge_mem G F hC
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp x.2).2.1⟩)) (Finset.mem_filter.mp x.2).2.2⟩
  have hcard : J.card ≤ (Finset.univ.filter fun e : H.Edge => H.incident e v).card :=
    Finset.card_le_card hJsubset
  have hdeg : (Finset.univ.filter fun e : H.Edge => H.incident e v).card = H.degree v := by
    simp [H, PhysicalGraph.degree, PhysicalGraph.selectedDegree]
  have hfinal : 2 ≤ (Finset.univ.filter fun e : H.Edge => H.incident e v).card := by
    rw [← hJcard]
    exact hcard
  exact hdeg ▸ hfinal

/-- Every vertex of the endpoint-supported union inherits the two incident
edges of some selected cycle that contains it. -/
theorem trimmed_degree_ge_two
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    ∀ v : (trimmedWitnessGraph G F).Vertex,
      2 ≤ (trimmedWitnessGraph G F).degree v := by
  classical
  intro v
  let V := witnessSupportVertices G F
  have hvV : trimmedHostVertex G F v ∈ V :=
    (Finset.equivFin V).symm v |>.2
  rcases (Finset.mem_filter.mp hvV).2 with ⟨e, he, hinc⟩
  rcases Finset.mem_biUnion.mp he with ⟨C, hC, heC⟩
  have hval : C.1 e ≠ 0 := (Finset.mem_filter.mp heC).2
  have hvused : trimmedHostVertex G F v ∈ G.usedVertices C.1 := by
    simp only [PhysicalGraph.usedVertices, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨e, hval, hinc⟩
  exact trimmed_degree_ge_two_of_cycle G F hC v hvused

/-- The desired vertex/edge estimate follows from the natural minimum-degree
screen on the endpoint-supported graph. -/
theorem trimmed_vertexCount_le_edgeCount_of_minDegree
    (G : PhysicalGraph) (F : Finset G.CycleWord)
    (hdegree : ∀ v : (trimmedWitnessGraph G F).Vertex,
      2 ≤ (trimmedWitnessGraph G F).degree v) :
    (trimmedWitnessGraph G F).vertexCount ≤
      (trimmedWitnessGraph G F).edgeCount := by
  let H := trimmedWitnessGraph G F
  have hsum := Erdos1016.Nonbacktracking.physical_degree_sum H
  have hlow : 2 * H.vertexCount ≤ ∑ v : H.Vertex, H.degree v := by
    calc
      2 * H.vertexCount = ∑ _v : H.Vertex, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : H.Vertex, H.degree v := Finset.sum_le_sum fun v _ => hdegree v
  rw [hsum] at hlow
  change H.vertexCount ≤ H.edgeCount
  omega

/-- The endpoint-supported union has at most as many vertices as support
edges, because every support vertex belongs to a selected cycle. -/
theorem trimmed_vertexCount_le_edgeCount
    (G : PhysicalGraph) (F : Finset G.CycleWord) :
    (trimmedWitnessGraph G F).vertexCount ≤
      (trimmedWitnessGraph G F).edgeCount :=
  trimmed_vertexCount_le_edgeCount_of_minDegree G F (trimmed_degree_ge_two G F)









end Erdos1016.Proof.VertexSupportedWitness
