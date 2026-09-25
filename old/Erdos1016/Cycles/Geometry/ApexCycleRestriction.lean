import Erdos1016.Cycles.Geometry.ApexCycleLift
import Erdos1016.Cycles.Selection.PackingTransversalDichotomy

set_option autoImplicit false

noncomputable section
namespace Erdos1016.CycleSupply

open SafeCore BoundaryDecay
local instance apexCycleRestrictionDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (H : PhysicalGraph)

/-- Restrict an apex-graph word to the original physical edges. -/
def restrictApexWord (x : (coreApexGraph H).Word) : H.Word :=
  fun e => x (coreEdgeLift H e)

private def extendRestrictedWord (x : H.Word) : (coreApexGraph H).Word := by
  classical
  intro e
  match (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
  | Sum.inl f => exact x f
  | Sum.inr _ => exact 0

private theorem extendRestrictedWord_old (x : H.Word) (e : H.Edge) :
    extendRestrictedWord H x (coreEdgeLift H e) = x e := by
  simp [extendRestrictedWord, coreEdgeLift]

private theorem extendRestrictedWord_spoke (x : H.Word) (p : CorePin H) :
    extendRestrictedWord H x (apexSpoke H p) = 0 := by
  simp [extendRestrictedWord, apexSpoke]

private theorem extendRestrictedWord_usedVertices (x : H.Word) :
    (coreApexGraph H).usedVertices (extendRestrictedWord H x) =
      (H.usedVertices x).image (coreVertexLift H) := by
  classical
  ext w
  simp only [PhysicalGraph.usedVertices, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hinc⟩
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
        have hedge : e = coreEdgeLift H f := by
          dsimp [coreEdgeLift]
          rw [← hdec]
          exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
        subst e
        change ((coreApexGraph H).src (coreEdgeLift H f) = w ∨
          (coreApexGraph H).dst (coreEdgeLift H f) = w) at hinc
        rw [coreEdgeLift_src, coreEdgeLift_dst] at hinc
        have hf : x f ≠ 0 := by
          rw [extendRestrictedWord_old] at he
          exact he
        rcases hinc with hinc | hinc
        · exact ⟨H.src f, ⟨⟨f, hf, Or.inl rfl⟩, hinc⟩⟩
        · exact ⟨H.dst f, ⟨⟨f, hf, Or.inr rfl⟩, hinc⟩⟩
    | inr p =>
        have hz : extendRestrictedWord H x e = 0 := by simp [extendRestrictedWord, hdec]
        exact (he hz).elim
  · rintro ⟨v, ⟨e, he, hinc⟩, rfl⟩
    refine ⟨coreEdgeLift H e, ?_, ?_⟩
    · simp [extendRestrictedWord_old, he]
    ·
      change ((coreApexGraph H).src (coreEdgeLift H e) = coreVertexLift H v ∨
        (coreApexGraph H).dst (coreEdgeLift H e) = coreVertexLift H v)
      rw [coreEdgeLift_src, coreEdgeLift_dst]
      rcases hinc with hinc | hinc
      · exact Or.inl (congrArg (coreVertexLift H) hinc)
      · exact Or.inr (congrArg (coreVertexLift H) hinc)

private theorem selectedAdj_extendRestrictedWord_iff (x : H.Word) (u v : H.Vertex) :
    ((coreApexGraph H).selectedGraph (extendRestrictedWord H x)).Adj
        (coreVertexLift H u) (coreVertexLift H v) ↔
      (H.selectedGraph x).Adj u v := by
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
        have hf : x f ≠ 0 := by rw [extendRestrictedWord_old] at he; exact he
        refine ⟨f, hf, ?_⟩
        change ((coreApexGraph H).src (coreEdgeLift H f) = coreVertexLift H u ∧
          (coreApexGraph H).dst (coreEdgeLift H f) = coreVertexLift H v) ∨
          ((coreApexGraph H).src (coreEdgeLift H f) = coreVertexLift H v ∧
          (coreApexGraph H).dst (coreEdgeLift H f) = coreVertexLift H u) at hend
        rw [coreEdgeLift_src, coreEdgeLift_dst] at hend
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨(coreVertexLift_injective H).eq_iff.mp h1,
            (coreVertexLift_injective H).eq_iff.mp h2⟩
        · exact Or.inr ⟨(coreVertexLift_injective H).eq_iff.mp h1,
            (coreVertexLift_injective H).eq_iff.mp h2⟩
    | inr p =>
        have hz : extendRestrictedWord H x e = 0 := by simp [extendRestrictedWord, hdec]
        exact (he hz).elim
  · rintro ⟨e, he, hend⟩
    refine ⟨coreEdgeLift H e, ?_, ?_⟩
    · rw [extendRestrictedWord_old]
      exact he
    · change ((coreApexGraph H).src (coreEdgeLift H e) = coreVertexLift H u ∧
        (coreApexGraph H).dst (coreEdgeLift H e) = coreVertexLift H v) ∨
        ((coreApexGraph H).src (coreEdgeLift H e) = coreVertexLift H v ∧
        (coreApexGraph H).dst (coreEdgeLift H e) = coreVertexLift H u)
      rw [coreEdgeLift_src, coreEdgeLift_dst]
      rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg (coreVertexLift H) h1, congrArg (coreVertexLift H) h2⟩
      · exact Or.inr ⟨congrArg (coreVertexLift H) h1, congrArg (coreVertexLift H) h2⟩

private noncomputable def usedVertexEquiv (x : H.Word) :
    {v // v ∈ H.usedVertices x} ≃
      {v // v ∈ (coreApexGraph H).usedVertices (extendRestrictedWord H x)} where
  toFun v := ⟨coreVertexLift H v.1, by
    rw [extendRestrictedWord_usedVertices]
    exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun w := by
    have hm : w.1 ∈ (H.usedVertices x).image (coreVertexLift H) := by
      rw [← extendRestrictedWord_usedVertices]
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
      rw [← extendRestrictedWord_usedVertices]
      exact w.2
    exact (Classical.choose_spec (Finset.mem_image.mp hm)).2

private theorem selectedInduce_connected_restriction (x : H.Word)
    (hconn : (((coreApexGraph H).selectedGraph (extendRestrictedWord H x)).induce
      (↑((coreApexGraph H).usedVertices (extendRestrictedWord H x)) :
        Set (coreApexGraph H).Vertex)).Connected) :
    (((H.selectedGraph x).induce (↑(H.usedVertices x) : Set H.Vertex)).Connected) := by
  let e := usedVertexEquiv H x
  let f : (((coreApexGraph H).selectedGraph (extendRestrictedWord H x)).induce
      (↑((coreApexGraph H).usedVertices (extendRestrictedWord H x)) :
        Set (coreApexGraph H).Vertex)) →g
      ((H.selectedGraph x).induce (↑(H.usedVertices x) : Set H.Vertex)) :=
    { toFun := e.symm
      map_rel' := by
        intro a b hab
        change ((coreApexGraph H).selectedGraph (extendRestrictedWord H x)).Adj a b at hab
        change (H.selectedGraph x).Adj (e.symm a).1 (e.symm b).1
        have ha : coreVertexLift H (e.symm a).1 = a.1 :=
          congrArg Subtype.val (e.apply_symm_apply a)
        have hb : coreVertexLift H (e.symm b).1 = b.1 :=
          congrArg Subtype.val (e.apply_symm_apply b)
        exact (selectedAdj_extendRestrictedWord_iff H x _ _).1 (by
          rw [ha, hb]
          exact hab) }
  exact hconn.map f e.symm.surjective

theorem apexCycle_spoke_zero {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) (p : CorePin H) :
    C.1 (apexSpoke H p) = 0 := by
  by_contra hne
  have hmem : coreApexVertex H ∈ Cycle.vertices C := by
    change coreApexVertex H ∈ (coreApexGraph H).usedVertices C.1
    simp only [PhysicalGraph.usedVertices, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨apexSpoke H p, hne, Or.inr (apexSpoke_dst H p)⟩
  exact havoid hmem

/-- A cycle whose support omits the apex has no spoke coordinates, and its
word is exactly the zero-spoke extension of its restriction to the old edges. -/
theorem apexCycle_eq_extend_restriction {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) :
    C.1 = extendRestrictedWord H (restrictApexWord H C.1) := by
  funext e
  cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
  | inl f =>
      have he : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      rw [he, extendRestrictedWord_old]
      rfl
  | inr p =>
      have he : e = apexSpoke H p := by
        dsimp [apexSpoke]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      rw [he, extendRestrictedWord_spoke]
      exact apexCycle_spoke_zero H havoid p

theorem apexCycle_restriction_connected {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) :
    (((H.selectedGraph (restrictApexWord H C.1)).induce
      (↑(H.usedVertices (restrictApexWord H C.1)) : Set H.Vertex)).Connected) := by
  let x := restrictApexWord H C.1
  have hconn : (((coreApexGraph H).selectedGraph (extendRestrictedWord H x)).induce
      (↑((coreApexGraph H).usedVertices (extendRestrictedWord H x)) :
        Set (coreApexGraph H).Vertex)).Connected := by
    have hword := apexCycle_eq_extend_restriction H havoid
    have hc := C.2.2.2.1
    rw [hword] at hc
    simpa [x] using hc
  exact selectedInduce_connected_restriction H x hconn

theorem apexCycle_length_eq_restriction {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) :
    (coreApexGraph H).wordLength C.1 = H.wordLength (restrictApexWord H C.1) := by
  rw [apexCycle_eq_extend_restriction H havoid]
  let x := restrictApexWord H C.1
  have hsupp : (coreApexGraph H).edgeSupport (extendRestrictedWord H x) =
      (H.edgeSupport x).image (coreEdgeLift H) := by
    classical
    ext e
    simp only [PhysicalGraph.edgeSupport, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image]
    cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
    | inl f =>
        have he : e = coreEdgeLift H f := by
          dsimp [coreEdgeLift]
          rw [← hdec]
          exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
        rw [he, extendRestrictedWord_old]
        change (C.1 (coreEdgeLift H f) ≠ 0) ↔
          ∃ a, C.1 (coreEdgeLift H a) ≠ 0 ∧ coreEdgeLift H a = coreEdgeLift H f
        constructor
        · intro hf
          exact ⟨f, hf, rfl⟩
        · rintro ⟨a, ha, hef⟩
          have : a = f := coreEdgeLift_injective H hef
          simpa [this] using ha
    | inr p =>
        have he : e = apexSpoke H p := by
          dsimp [apexSpoke]
          rw [← hdec]
          exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
        rw [he, extendRestrictedWord_spoke]
        change (0 ≠ (0 : F₂)) ↔ ∃ f, C.1 (coreEdgeLift H f) ≠ 0 ∧
          coreEdgeLift H f = apexSpoke H p
        constructor
        · intro h
          exact (h rfl).elim
        · rintro ⟨f, _, hef⟩
          have hsum := (Fintype.equivFin (H.Edge ⊕ CorePin H)).injective hef
          exact Sum.noConfusion hsum
  unfold PhysicalGraph.wordLength
  rw [hsupp]
  rw [Finset.card_image_of_injective _ (coreEdgeLift_injective H)]
  have hret : restrictApexWord H (extendRestrictedWord H x) = x := by
    funext e
    simp [restrictApexWord, extendRestrictedWord_old]
  change (H.edgeSupport x).card =
    (H.edgeSupport (restrictApexWord H (extendRestrictedWord H x))).card
  rw [hret]

private theorem selectedIncidenceFinset_extend_eq (x : H.Word) (v : H.Vertex) :
    (Finset.univ.filter (fun e : (coreApexGraph H).Edge =>
      extendRestrictedWord H x e ≠ 0 ∧
        (coreApexGraph H).incident e (coreVertexLift H v))) =
      (Finset.univ.filter (fun e : H.Edge =>
        x e ≠ 0 ∧ H.incident e v)).image (coreEdgeLift H) := by
  classical
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  cases hdec : (Fintype.equivFin (H.Edge ⊕ CorePin H)).symm e with
  | inl f =>
      have he : e = coreEdgeLift H f := by
        dsimp [coreEdgeLift]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      subst e
      simp only [extendRestrictedWord_old, PhysicalGraph.incident,
        coreEdgeLift_src, coreEdgeLift_dst]
      constructor
      · rintro ⟨hf, hv | hv⟩
        · exact ⟨f, ⟨hf, Or.inl ((coreVertexLift_injective H).eq_iff.mp hv)⟩, rfl⟩
        · exact ⟨f, ⟨hf, Or.inr ((coreVertexLift_injective H).eq_iff.mp hv)⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hv⟩, heq⟩
        have : a = f := coreEdgeLift_injective H heq
        subst a
        exact ⟨ha, by
          rcases hv with hv | hv
          · exact Or.inl (congrArg (coreVertexLift H) hv)
          · exact Or.inr (congrArg (coreVertexLift H) hv)⟩
  | inr p =>
      have he : e = apexSpoke H p := by
        dsimp [apexSpoke]
        rw [← hdec]
        exact (Fintype.equivFin (H.Edge ⊕ CorePin H)).apply_symm_apply e |>.symm
      subst e
      rw [extendRestrictedWord_spoke]
      constructor
      · rintro ⟨hzero, _⟩
        exact (hzero rfl).elim
      · rintro ⟨a, ⟨_, _⟩, heq⟩
        have hsum := (Fintype.equivFin (H.Edge ⊕ CorePin H)).injective heq
        exact Sum.noConfusion hsum

/-- Selected degree at an old vertex is preserved when a word is extended
by zero over all spokes. -/
theorem selectedDegree_extendRestrictedWord (x : H.Word) (v : H.Vertex) :
    (coreApexGraph H).selectedDegree (extendRestrictedWord H x) (coreVertexLift H v) =
      H.selectedDegree x v := by
  unfold PhysicalGraph.selectedDegree
  rw [selectedIncidenceFinset_extend_eq]
  exact Finset.card_image_of_injective _ (coreEdgeLift_injective H)

theorem apexCycle_selectedDegree_eq_restriction {C : (coreApexGraph H).CycleWord}
    (havoid : coreApexVertex H ∉ Cycle.vertices C) (v : H.Vertex) :
    (coreApexGraph H).selectedDegree C.1 (coreVertexLift H v) =
      H.selectedDegree (restrictApexWord H C.1) v := by
  rw [apexCycle_eq_extend_restriction H havoid]
  have hret : restrictApexWord H
      (extendRestrictedWord H (restrictApexWord H C.1)) = restrictApexWord H C.1 := by
    funext e
    simp [restrictApexWord, extendRestrictedWord_old]
  rw [hret]
  exact selectedDegree_extendRestrictedWord H _ v











end Erdos1016.CycleSupply
end
