import Erdos1016.Cycles.Geometry.PhysicalCycleEmbedding

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PhysicalCycleEmbedding

open Nonbacktracking BoundaryDecay BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

section WalkRestriction

variable {V : Type*} (J : SimpleGraph V) (S : Set V)

/-- Restrict a walk whose actual vertices all lie in the induced region. -/
def restrictWalk : ∀ {u v : V} (p : J.Walk u v)
    (hp : ∀ x ∈ p.support, x ∈ S),
    (J.induce S).Walk ⟨u, hp u p.start_mem_support⟩ ⟨v, hp v p.end_mem_support⟩
  | _, _, .nil, _ => .nil
  | u, _, .cons (v := w) h p, hp =>
      .cons (show (J.induce S).Adj ⟨u, hp u (by simp)⟩ ⟨w, hp w (by simp)⟩ from h)
        (restrictWalk p (fun x hx => hp x (by simp [hx])))

theorem restrictWalk_map {u v : V} (p : J.Walk u v)
    (hp : ∀ x ∈ p.support, x ∈ S) :
    (restrictWalk J S p hp).map (SimpleGraph.Embedding.induce (G := J) S).toHom = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp only [restrictWalk, SimpleGraph.Walk.map_cons]
      rw [ih]

theorem restrictWalk_isCycle {u : V} (p : J.Walk u u)
    (hp : ∀ x ∈ p.support, x ∈ S) (hcycle : p.IsCycle) :
    (restrictWalk J S p hp).IsCycle := by
  apply (SimpleGraph.Walk.map_isCycle_iff_of_injective
    (f := (SimpleGraph.Embedding.induce (G := J) S).toHom) Subtype.val_injective).mp
  simpa only [restrictWalk_map] using hcycle

end WalkRestriction

/-- Mapping a walk reads the same coefficient at every embedded edge. -/
theorem Embedding.walkWord_map_coord {H G : PhysicalGraph} (E : Embedding H G)
    {u v : H.Vertex} (p : H.toSimpleGraph.Walk u v) (e : H.Edge) :
    walkWord G (p.map E.graphHom) (E.edge e) = walkWord H p e := by
  have hp : physicalPair G (E.edge e) = Sym2.map E.graphHom (physicalPair H e) := by
    change s(G.src (E.edge e), G.dst (E.edge e)) = s(E.vertex (H.src e), E.vertex (H.dst e))
    rw [E.src, E.dst]
  have hmem : physicalPair G (E.edge e) ∈ (p.map E.graphHom).edges ↔
      physicalPair H e ∈ p.edges := by
    rw [SimpleGraph.Walk.edges_map, hp]
    exact List.mem_map_of_injective (Sym2.map.injective E.vertex.injective)
  simp only [walkWord, hmem]

/-- Every supported ambient cycle is the lift of an actual cycle in the
literal induced physical graph. -/
theorem exists_induced_cycle (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : G.CycleWord) (hC : Cycle.vertices C ⊆ S) :
    ∃ D : (FiniteTwoCore.inducedPhysical G S).CycleWord,
      (induced G S).liftCycle D = C := by
  classical
  obtain ⟨u, p, hp, hpC⟩ := exists_cycle_walk_of_cycleWord G C
  have hsup : ∀ x ∈ p.support, x ∈ (↑S : Set G.Vertex) := by
    intro x hx
    apply hC
    rw [← hpC]
    exact (used_walkWord_iff G p hp x).mpr hx
  let P := FiniteTwoCore.inducedPhysical G S
  let E := induced G S
  let φ : G.toSimpleGraph.induce (↑S : Set G.Vertex) →g P.toSimpleGraph :=
    { toFun := fun v => Fintype.equivFin (Network.Shore.InsideVertex S) v
      map_rel' := by
        intro v w hvw
        apply (induced_adj_iff G S _ _).mpr
        simpa [induced] using hvw }
  have hφ : Function.Injective φ := (Fintype.equivFin (Network.Shore.InsideVertex S)).injective
  let q := (restrictWalk G.toSimpleGraph (↑S : Set G.Vertex) p hsup).map φ
  have hq : q.IsCycle := (restrictWalk_isCycle G.toSimpleGraph _ p hsup hp).map hφ
  let D := cycleWordOfWalk P q hq
  have hcomp : E.graphHom.comp φ = (SimpleGraph.Embedding.induce (G := G.toSimpleGraph) (↑S : Set G.Vertex)).toHom := by
    ext v
    change ((Fintype.equivFin (Network.Shore.InsideVertex S)).symm
      ((Fintype.equivFin (Network.Shore.InsideVertex S)) v)).1.val = v.1.val
    rw [Equiv.symm_apply_apply]
  have hedges : (q.map E.graphHom).edges = p.edges := by
    change (((restrictWalk G.toSimpleGraph (↑S : Set G.Vertex) p hsup).map φ).map E.graphHom).edges = p.edges
    rw [SimpleGraph.Walk.map_map]
    have he := congrArg (fun f : G.toSimpleGraph.induce (↑S : Set G.Vertex) →g G.toSimpleGraph =>
      ((restrictWalk G.toSimpleGraph (↑S : Set G.Vertex) p hsup).map f).edges) hcomp
    exact he.trans (congrArg SimpleGraph.Walk.edges (restrictWalk_map G.toSimpleGraph _ p hsup))
  have hcoord (e : P.Edge) : D.1 e = C.1 (E.edge e) := by
    have h := E.walkWord_map_coord q e
    change walkWord P q e = C.1 (E.edge e)
    rw [← h]
    have hCeq : C.1 = walkWord G p := congrArg Subtype.val hpC.symm
    simp only [walkWord, hedges, hCeq]
  refine ⟨D, ?_⟩
  apply Subtype.ext
  funext e
  by_cases he : G.src e ∈ S ∧ G.dst e ∈ S
  · let f : P.Edge := Fintype.equivFin (Network.Shore.InsideEdge G.traceNetwork S) ⟨e, he⟩
    have hf : E.edge f = e := by simp [E, f, induced]
    rw [← hf, E.liftCycle_coord, hcoord]
  · have hzero (B : G.CycleWord) (hB : Cycle.vertices B ⊆ S) : B.1 e = 0 := by
      apply Classical.byContradiction
      intro hne
      exact he ⟨hB (src_mem_used_of_ne_zero B.1 e hne),
        hB (dst_mem_used_of_ne_zero B.1 e hne)⟩
    rw [hzero C hC, hzero (E.liftCycle D) (induced_liftCycle_subset G S D)]

/-- Restriction is inverse to the induced embedding on supported cycles. -/
def restrictCycle (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : G.CycleWord) (hC : Cycle.vertices C ⊆ S) :
    (FiniteTwoCore.inducedPhysical G S).CycleWord :=
  (exists_induced_cycle G S C hC).choose

@[simp] theorem lift_restrictCycle (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : G.CycleWord) (hC : Cycle.vertices C ⊆ S) :
    (induced G S).liftCycle (restrictCycle G S C hC) = C :=
  (exists_induced_cycle G S C hC).choose_spec

@[simp] theorem restrictCycle_length (G : PhysicalGraph) (S : Finset G.Vertex)
    (C : G.CycleWord) (hC : Cycle.vertices C ⊆ S) :
    BoundaryDecay.Cycle.length (restrictCycle G S C hC) = BoundaryDecay.Cycle.length C := by
  rw [← (induced G S).liftCycle_length, lift_restrictCycle]



/-- Restrict a whole supported family without adding or identifying cycles. -/
def restrictFamily (G : PhysicalGraph) (S : Finset G.Vertex) (F : Finset G.CycleWord)
    (hF : ∀ C ∈ F, Cycle.vertices C ⊆ S) : Finset (FiniteTwoCore.inducedPhysical G S).CycleWord :=
  F.attach.image (fun C => restrictCycle G S C.1 (hF C.1 C.2))

theorem restrictFamily_injective (G : PhysicalGraph) (S : Finset G.Vertex) (F : Finset G.CycleWord)
    (hF : ∀ C ∈ F, Cycle.vertices C ⊆ S) :
    Function.Injective (fun C : F => restrictCycle G S C.1 (hF C.1 C.2)) := by
  intro C D h
  apply Subtype.ext
  have he := congrArg (induced G S).liftCycle h
  simpa only [lift_restrictCycle] using he

theorem sum_restrictFamily (G : PhysicalGraph) (S : Finset G.Vertex) (F : Finset G.CycleWord)
    (hF : ∀ C ∈ F, Cycle.vertices C ⊆ S) (mass : G.CycleWord → ℝ) :
    (∑ D ∈ restrictFamily G S F hF, mass ((induced G S).liftCycle D)) =
      ∑ C ∈ F, mass C := by
  classical
  unfold restrictFamily
  rw [Finset.sum_image (fun _ _ _ _ h => restrictFamily_injective G S F hF h)]
  simp only [lift_restrictCycle, Finset.sum_attach]

theorem lift_restrictFamily (G : PhysicalGraph) (S : Finset G.Vertex) (F : Finset G.CycleWord)
    (hF : ∀ C ∈ F, Cycle.vertices C ⊆ S) :
    (induced G S).liftFamily (restrictFamily G S F hF) = F := by
  unfold Embedding.liftFamily restrictFamily
  rw [Finset.image_image]
  change F.attach.image (fun C : F =>
    (induced G S).liftCycle (restrictCycle G S C.1 (hF C.1 C.2))) = F
  have heq : (fun C : F => (induced G S).liftCycle (restrictCycle G S C.1 (hF C.1 C.2))) =
      (fun C : F => C.1) := funext (fun C => lift_restrictCycle G S C.1 (hF C.1 C.2))
  rw [heq]
  exact Finset.attach_image_val

theorem vertexLoad_restrictFamily (G : PhysicalGraph) (S : Finset G.Vertex) (F : Finset G.CycleWord)
    (hF : ∀ C ∈ F, Cycle.vertices C ⊆ S) (mass : G.CycleWord → ℝ) (v : G.Vertex) :
    vertexLoad (restrictFamily G S F hF)
      (fun D => (Cycle.vertices D).image (induced G S).vertex)
      (fun D => mass ((induced G S).liftCycle D)) v = vertexLoad F Cycle.vertices mass v := by
  have h := sum_restrictFamily G S F hF (fun C => if v ∈ Cycle.vertices C then mass C else 0)
  unfold vertexLoad
  convert h using 1
  · apply Finset.sum_congr rfl
    intro C _
    rw [Embedding.liftCycle_vertices]
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> rfl

theorem induced_girth_of_noShortCycles (G : PhysicalGraph) (S : Finset G.Vertex) (D : ℕ)
    (hno : CycleSupply.NoShortCycles G S D) :
    ShortWalks.GirthGreater (FiniteTwoCore.inducedPhysical G S).toSimpleGraph D := by
  intro v p hp
  let E := induced G S
  let q := p.map E.graphHom
  have hq : q.IsCycle := hp.map E.vertex.injective
  let C := cycleWordOfWalk G q hq
  have hC : Cycle.vertices C ⊆ S := by
    intro w hw
    have hmem := (used_walkWord_iff G q hq w).mp hw
    rw [SimpleGraph.Walk.support_map] at hmem
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hmem
    exact induced_vertex_mem G S u
  have h := hno C hC
  simpa only [C, cycleWordOfWalk_length, q, SimpleGraph.Walk.length_map] using h

end Erdos1016.Proof.PhysicalCycleEmbedding
