import Erdos1016.Expansion.ApexProtector

set_option autoImplicit false

/-!
# Cycle words lift from the core to its one-apex completion

Old edge coordinates are retained and every new spoke has coordinate zero.
The construction therefore preserves the cycle support, including its
vertices and length.
-/

noncomputable section
namespace Erdos1016.CycleSupply
open SafeCore BoundaryDecay BoundaryTrace

local instance apexCycleLiftDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (H : PhysicalGraph)

private def liftApexWord (x : H.Word) : (coreApexGraph H).Word := by
  classical
  intro e
  match (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
  | Sum.inl f => exact x f
  | Sum.inr _ => exact 0

@[simp] private theorem liftApexWord_old (x : H.Word) (e : H.Edge) :
    liftApexWord H x (coreEdgeLift H e) = x e := by
  simp [liftApexWord, coreEdgeLift]

private theorem coreEdgeLift_injective' : Function.Injective (coreEdgeLift H) :=
  coreEdgeLift_injective H

private theorem liftApexWord_edgeSupport (x : H.Word) :
    (coreApexGraph H).edgeSupport (liftApexWord H x) =
      (H.edgeSupport x).image (coreEdgeLift H) := by
  classical
  ext e
  simp only [PhysicalGraph.edgeSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro he
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
      have hedge : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      refine ⟨f, ?_, hedge.symm⟩
      simpa [liftApexWord, hdec] using he
    | inr p =>
      have hz : liftApexWord H x e = 0 := by simp [liftApexWord, hdec]
      exact (he hz).elim
  · rintro ⟨f, hf, rfl⟩
    simpa using hf

theorem liftApexWord_wordLength (x : H.Word) :
    (coreApexGraph H).wordLength (liftApexWord H x) = H.wordLength x := by
  unfold PhysicalGraph.wordLength
  rw [liftApexWord_edgeSupport]
  exact Finset.card_image_of_injective _ (coreEdgeLift_injective' H)

theorem liftApexWord_usedVertices (x : H.Word) :
    (coreApexGraph H).usedVertices (liftApexWord H x) =
      (H.usedVertices x).image (coreVertexLift H) := by
  classical
  ext w
  simp only [PhysicalGraph.usedVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hinc⟩
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
      have hedge : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      subst e
      change (coreApexGraph H).src (coreEdgeLift H f) = w ∨
        (coreApexGraph H).dst (coreEdgeLift H f) = w at hinc
      rw [coreEdgeLift_src, coreEdgeLift_dst] at hinc
      rcases hinc with hinc | hinc
      · refine ⟨H.src f, ⟨f, ?_, Or.inl rfl⟩, hinc⟩
        simpa using he
      · refine ⟨H.dst f, ⟨f, ?_, Or.inr rfl⟩, hinc⟩
        simpa using he
    | inr p =>
      have hz : liftApexWord H x e = 0 := by simp [liftApexWord, hdec]
      exact (he hz).elim
  · rintro ⟨v, ⟨e, he, hinc⟩, rfl⟩
    refine ⟨coreEdgeLift H e, ?_, ?_⟩
    · simpa using he
    · rcases hinc with hinc | hinc
      · exact Or.inl ((coreEdgeLift_src H e).trans (congrArg (coreVertexLift H) hinc))
      · exact Or.inr ((coreEdgeLift_dst H e).trans (congrArg (coreVertexLift H) hinc))

private theorem selectedIncidenceFinset_lift_eq (x : H.Word) (v : H.Vertex) :
    (Finset.univ.filter (fun e : (coreApexGraph H).Edge =>
      liftApexWord H x e ≠ 0 ∧ (coreApexGraph H).incident e (coreVertexLift H v))) =
      (Finset.univ.filter (fun e : H.Edge => x e ≠ 0 ∧ H.incident e v)).image
        (coreEdgeLift H) := by
  classical
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨he, hinc⟩
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
      have hedge : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      subst e
      change (coreApexGraph H).src (coreEdgeLift H f) = coreVertexLift H v ∨
        (coreApexGraph H).dst (coreEdgeLift H f) = coreVertexLift H v at hinc
      rw [coreEdgeLift_src, coreEdgeLift_dst] at hinc
      rcases hinc with hinc | hinc
      · refine ⟨f, ⟨?_, Or.inl ?_⟩, rfl⟩
        · simpa using he
        · exact coreVertexLift_injective H hinc
      · refine ⟨f, ⟨?_, Or.inr ?_⟩, rfl⟩
        · simpa using he
        · exact coreVertexLift_injective H hinc
    | inr p =>
      have hz : liftApexWord H x e = 0 := by simp [liftApexWord, hdec]
      exact (he hz).elim
  · rintro ⟨f, ⟨he, hinc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa using he
    · change (coreApexGraph H).src (coreEdgeLift H f) = coreVertexLift H v ∨
        (coreApexGraph H).dst (coreEdgeLift H f) = coreVertexLift H v
      rw [coreEdgeLift_src, coreEdgeLift_dst]
      rcases hinc with hinc | hinc
      · exact Or.inl (congrArg (coreVertexLift H) hinc)
      · exact Or.inr (congrArg (coreVertexLift H) hinc)

theorem selectedDegree_liftApex_eq (x : H.Word) (v : H.Vertex) :
    (coreApexGraph H).selectedDegree (liftApexWord H x) (coreVertexLift H v) =
      H.selectedDegree x v := by
  unfold PhysicalGraph.selectedDegree
  rw [selectedIncidenceFinset_lift_eq]
  exact Finset.card_image_of_injective _ (coreEdgeLift_injective' H)

private def liftApexNetworkWord (x : H.Word) : (coreApexNetwork H).Word :=
  fun e => match e with
    | Sum.inl f => x f
    | Sum.inr _ => 0

private theorem liftApexNetwork_boundary_old (x : H.Word) (v : H.Vertex) :
    (coreApexNetwork H).boundary (liftApexNetworkWord H x) (Sum.inl v) =
      H.traceNetwork.boundary x v := by
  classical
  rw [BoundaryTrace.Network.boundary_apply, H.traceNetwork_boundary,
    PhysicalGraph.boundary]
  simp_rw [Fintype.sum_sum_type]
  simp [coreApexNetwork, liftApexNetworkWord, corePorts, Ported.apex,
    PhysicalGraph.traceNetwork, Finset.sum_add_distrib, add_comm]

private theorem liftApexNetwork_boundary_apex (x : H.Word) :
    (coreApexNetwork H).boundary (liftApexNetworkWord H x) (Sum.inr ()) = 0 := by
  classical
  rw [BoundaryTrace.Network.boundary_apply]
  simp_rw [Fintype.sum_sum_type]
  simp [coreApexNetwork, liftApexNetworkWord, corePorts, Ported.apex]

private theorem liftApexNetwork_cycle (x : H.CycleSpace) :
    liftApexNetworkWord H x.1 ∈ (coreApexNetwork H).CycleSpace := by
  apply LinearMap.mem_ker.mpr
  funext w
  cases w with
  | inl v =>
    rw [liftApexNetwork_boundary_old, H.traceNetwork_boundary]
    exact congrFun (LinearMap.mem_ker.mp x.2) v
  | inr u => cases u; exact liftApexNetwork_boundary_apex H x.1

private theorem liftApexWord_cycleSpace (x : H.CycleSpace) :
    liftApexWord H x.1 ∈ (coreApexGraph H).CycleSpace := by
  let y : (coreApexNetwork H).CycleSpace :=
    ⟨liftApexNetworkWord H x.1, liftApexNetwork_cycle H x⟩
  let z := BoundaryDecay.physicalCycleEquiv (coreApexNetwork H) (coreApex_simple H) y
  have hz : z.1 = liftApexWord H x.1 := by
    funext e
    change liftApexNetworkWord H x.1
        ((Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e) = liftApexWord H x.1 e
    simp [liftApexNetworkWord, liftApexWord]
  rw [← hz]
  exact z.2

private theorem selectedAdj_liftApex_iff (x : H.Word) (u v : H.Vertex) :
    ((coreApexGraph H).selectedGraph (liftApexWord H x)).Adj
      (coreVertexLift H u) (coreVertexLift H v) ↔ (H.selectedGraph x).Adj u v := by
  classical
  constructor
  · rintro ⟨e, he, hend⟩
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
      have hedge : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      subst e
      refine ⟨f, ?_, ?_⟩
      · simpa using he
      · rw [coreEdgeLift_src, coreEdgeLift_dst] at hend
        rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨coreVertexLift_injective H h₁, coreVertexLift_injective H h₂⟩
        · exact Or.inr ⟨coreVertexLift_injective H h₁, coreVertexLift_injective H h₂⟩
    | inr p =>
      have hz : liftApexWord H x e = 0 := by simp [liftApexWord, hdec]
      exact (he hz).elim
  · rintro ⟨e, he, hend⟩
    refine ⟨coreEdgeLift H e, ?_, ?_⟩
    · simpa using he
    · rw [coreEdgeLift_src, coreEdgeLift_dst]
      rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg (coreVertexLift H) h₁, congrArg (coreVertexLift H) h₂⟩
      · exact Or.inr ⟨congrArg (coreVertexLift H) h₁, congrArg (coreVertexLift H) h₂⟩

private noncomputable def usedVertexEquiv (x : H.Word) :
    {v // v ∈ H.usedVertices x} ≃
      {v // v ∈ (coreApexGraph H).usedVertices (liftApexWord H x)} where
  toFun v := ⟨coreVertexLift H v.1, by
    rw [liftApexWord_usedVertices]
    exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun w := by
    have hm : w.1 ∈ (H.usedVertices x).image (coreVertexLift H) := by
      rw [← liftApexWord_usedVertices]
      exact w.2
    let v := Classical.choose (Finset.mem_image.mp hm)
    exact ⟨v, (Classical.choose_spec (Finset.mem_image.mp hm)).1⟩
  left_inv v := by
    apply Subtype.ext
    apply coreVertexLift_injective H
    have hm : coreVertexLift H v.1 ∈ (H.usedVertices x).image (coreVertexLift H) :=
      Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩
    exact (Classical.choose_spec (Finset.mem_image.mp hm)).2
  right_inv w := by
    apply Subtype.ext
    have hm : w.1 ∈ (H.usedVertices x).image (coreVertexLift H) := by
      rw [← liftApexWord_usedVertices]
      exact w.2
    exact (Classical.choose_spec (Finset.mem_image.mp hm)).2

private theorem selectedInduce_connected_liftApex (x : H.Word)
    (hconn : ((H.selectedGraph x).induce (↑(H.usedVertices x) : Set H.Vertex)).Connected) :
    (((coreApexGraph H).selectedGraph (liftApexWord H x)).induce
      (↑((coreApexGraph H).usedVertices (liftApexWord H x)) : Set (coreApexGraph H).Vertex)).Connected := by
  let e := usedVertexEquiv H x
  let f : (H.selectedGraph x).induce (↑(H.usedVertices x) : Set H.Vertex) →g
      ((coreApexGraph H).selectedGraph (liftApexWord H x)).induce
        (↑((coreApexGraph H).usedVertices (liftApexWord H x)) : Set (coreApexGraph H).Vertex) :=
    { toFun := e
      map_rel' := by
        intro a b hab
        change (H.selectedGraph x).Adj a b at hab
        change ((coreApexGraph H).selectedGraph (liftApexWord H x)).Adj (e a) (e b)
        exact (selectedAdj_liftApex_iff H x a b).2 hab }
  exact hconn.map f e.surjective

/-- Lift a core cycle to the apex completion, extending it by zero on every spoke. -/
def liftApexCycleWord (c : H.CycleWord) : (coreApexGraph H).CycleWord := by
  classical
  let x := c.1
  have hspace : liftApexWord H x ∈ (coreApexGraph H).CycleSpace :=
    liftApexWord_cycleSpace H ⟨x, by
      apply LinearMap.mem_ker.mpr
      funext v
      change H.boundary x v = 0
      exact congrFun c.2.2.1 v⟩
  refine ⟨liftApexWord H x, ?_⟩
  refine ⟨?_, ?_, selectedInduce_connected_liftApex H x c.2.2.2.1, ?_⟩
  · intro hz
    apply c.2.1
    funext e
    have hz' := congrFun hz (coreEdgeLift H e)
    simpa [liftApexWord, coreEdgeLift] using hz'
  · change (coreApexGraph H).boundary (liftApexWord H x) = 0
    exact LinearMap.mem_ker.mp hspace
  · intro t ht
    let e := usedVertexEquiv H x
    let v := e.symm ⟨t, ht⟩
    have hvt : coreVertexLift H v.1 = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)
    rw [← hvt, selectedDegree_liftApex_eq]
    exact c.2.2.2.2 v.1 v.2

@[simp] theorem liftApexCycleWord_old_edge (c : H.CycleWord) (e : H.Edge) :
    (liftApexCycleWord H c).1 (coreEdgeLift H e) = c.1 e := by
  simp [liftApexCycleWord, liftApexWord, coreEdgeLift]

@[simp] theorem liftApexCycleWord_spoke (c : H.CycleWord) (p : CorePin H) :
    (liftApexCycleWord H c).1 (apexSpoke H p) = 0 := by
  simp [liftApexCycleWord, liftApexWord, apexSpoke]

theorem liftApexCycleWord_vertices (c : H.CycleWord) :
    (coreApexGraph H).usedVertices (liftApexCycleWord H c).1 =
      (H.usedVertices c.1).image (coreVertexLift H) := by
  exact liftApexWord_usedVertices H c.1

theorem liftApexCycleWord_length (c : H.CycleWord) :
    (coreApexGraph H).wordLength (liftApexCycleWord H c).1 = H.wordLength c.1 := by
  exact liftApexWord_wordLength H c.1

end Erdos1016.CycleSupply
