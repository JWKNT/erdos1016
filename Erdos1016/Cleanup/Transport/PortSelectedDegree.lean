import Erdos1016.Cleanup.Transport.PortExpansionCycleSpace

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.PortSelectedDegree

open Erdos1016
open Erdos1016.FiniteMultiGraph
open Erdos1016.Proof.PortExpansion
open Erdos1016.Proof.PortExpansionCycleSpace
open Erdos1016.Proof.CleanupSpecification

private theorem filter_univ_card_eq_subtype_card
    {α : Type*} (P : α → Prop) [Fintype α] [DecidablePred P] :
    (Finset.univ.filter P).card = Fintype.card {x // P x} := by
  classical
  symm
  simpa using (Fintype.card_subtype P)

local notation "F₂" => ZMod 2

def auxiliaryRestriction (M : FiniteMultiGraph) (K : Finset M.Vertex)
    (x : M.CycleSpace) : M.EdgeWord :=
  fun e => if e ∈ internalEdges M K then x.1 e else 0

def physicalRestriction (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (x : M.CycleSpace) (_hKS : K ⊆ S) :
    (Physical M S h).EdgeWord :=
  fun e => if e ∈ internalEdges (Physical M S h) (oldVertexImage M S h K)
    then (rootPortCycleEquiv M S h x).1 e else 0

private def sourceSelected (Γ : FiniteMultiGraph) (w : Γ.EdgeWord) (v : Γ.Vertex) :
    Finset Γ.Edge :=
  Finset.univ.filter fun e => Γ.src e = v ∧ w e ≠ 0

private def destinationSelected (Γ : FiniteMultiGraph) (w : Γ.EdgeWord) (v : Γ.Vertex) :
    Finset Γ.Edge :=
  Finset.univ.filter fun e => Γ.dst e = v ∧ w e ≠ 0

private theorem internalDirectEdge_injective
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    Function.Injective (internalDirectEdge M S K h hKS) := by
  intro e f hef
  have htag : (⟨e.1, hKS (Finset.mem_filter.mp e.2 |>.2.1),
      hKS (Finset.mem_filter.mp e.2 |>.2.2)⟩ : InternalEdge M S) =
      ⟨f.1, hKS (Finset.mem_filter.mp f.2 |>.2.1),
      hKS (Finset.mem_filter.mp f.2 |>.2.2)⟩ := by
    change edgeEquiv M S (.inl ⟨e.1,
        hKS (Finset.mem_filter.mp e.2 |>.2.1),
        hKS (Finset.mem_filter.mp e.2 |>.2.2)⟩) =
      edgeEquiv M S (.inl ⟨f.1,
        hKS (Finset.mem_filter.mp f.2 |>.2.1),
        hKS (Finset.mem_filter.mp f.2 |>.2.2)⟩) at hef
    exact Sum.inl.inj ((edgeEquiv M S).injective hef)
  have hval : e.1 = f.1 := congrArg (fun z : InternalEdge M S => z.1) htag
  exact Subtype.ext hval

private theorem auxiliarySource_card_eq_tagged
    (M : FiniteMultiGraph) (K : Finset M.Vertex) (x : M.CycleSpace) (v : M.Vertex) :
    (Finset.univ.filter fun e : M.Edge =>
      M.src e = v ∧ auxiliaryRestriction M K x e ≠ 0).card =
    ((internalEdges M K).attach.filter fun e : {e : M.Edge // e ∈ internalEdges M K} =>
      M.src e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).card := by
  classical
  symm
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_attach, true_and] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact he
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    have hs := (Finset.mem_filter.mp he).2
    have hinternal : e ∈ internalEdges M K := by
      by_contra hnot
      simp [auxiliaryRestriction, hnot] at hs
    refine ⟨⟨e, hinternal⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hs⟩

private theorem auxiliaryDestination_card_eq_tagged
    (M : FiniteMultiGraph) (K : Finset M.Vertex) (x : M.CycleSpace) (v : M.Vertex) :
    (Finset.univ.filter fun e : M.Edge =>
      M.dst e = v ∧ auxiliaryRestriction M K x e ≠ 0).card =
    ((internalEdges M K).attach.filter fun e : {e : M.Edge // e ∈ internalEdges M K} =>
      M.dst e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).card := by
  classical
  symm
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_attach, true_and] at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact he
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    have hs := (Finset.mem_filter.mp he).2
    have hinternal : e ∈ internalEdges M K := by
      by_contra hnot
      simp [auxiliaryRestriction, hnot] at hs
    refine ⟨⟨e, hinternal⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hs⟩

private theorem physicalSource_eq_taggedImage
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace) (v : M.Vertex) :
    sourceSelected (Physical M S h) (physicalRestriction M S K h x hKS)
      (oldVertex M S v) =
    ((internalEdges M K).attach.filter fun e : {e : M.Edge // e ∈ internalEdges M K} =>
      M.src e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).image
        (internalDirectEdge M S K h hKS) := by
  classical
  ext i
  constructor
  · intro hi
    have hsel := (Finset.mem_filter.mp hi).2
    have hmemPhysical : i ∈ internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      by_contra hn
      simp [physicalRestriction, hn] at hsel
    have hmemImage := hmemPhysical
    rw [rootPort_internalEdges_image_eq M S K h hKS] at hmemImage
    rcases Finset.mem_image.mp hmemImage with ⟨e, heattach, heq⟩
    have hphi : internalDirectEdge M S K h hKS e ∈
        internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      rw [heq]
      exact hmemPhysical
    have hauxEq : auxiliaryRestriction M K x e.1 = x.1 e.1 := by
      simp [auxiliaryRestriction, e.2]
    have hsource : M.src e.1 = v := by
      have hsrc := hsel.1
      rw [← heq] at hsrc
      have hsrc' : oldVertex M S (M.src e.1) = oldVertex M S v := by
        simpa [internalDirectEdge, src_internalEdge] using hsrc
      exact oldVertex_injective M S hsrc'
    have hword : (rootPortCycleEquiv M S h x).1
        (internalDirectEdge M S K h hKS e) = x.1 e.1 :=
      rootPortCycleEquiv_internalEdges_word M S K h hKS x e
    have hxcoeff : x.1 e.1 ≠ 0 := by
      intro hz
      apply hsel.2
      rw [← heq]
      simpa [physicalRestriction, hphi, hword, hz]
    have hcoeff : auxiliaryRestriction M K x e.1 ≠ 0 := by
      simpa [hauxEq] using hxcoeff
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ?_, heq⟩
    exact ⟨heattach, hsource, hcoeff⟩
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, rfl⟩
    have heprops := (Finset.mem_filter.mp he).2
    have hmem : internalDirectEdge M S K h hKS e ∈
        internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      rw [rootPort_internalEdges_image_eq M S K h hKS]
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mp he |>.1, rfl⟩
    have hsrc : (Physical M S h).src (internalDirectEdge M S K h hKS e) =
        oldVertex M S v := by
      simpa [internalDirectEdge, src_internalEdge] using
        congrArg (oldVertex M S) heprops.1
    have hword : (rootPortCycleEquiv M S h x).1
        (internalDirectEdge M S K h hKS e) = x.1 e.1 :=
      rootPortCycleEquiv_internalEdges_word M S K h hKS x e
    have hcoeffAux : x.1 e.1 ≠ 0 := by
      simpa [auxiliaryRestriction, e.2] using heprops.2
    have hcoeffPhys : physicalRestriction M S K h x hKS
        (internalDirectEdge M S K h hKS e) ≠ 0 := by
      simpa [physicalRestriction, hmem, hword] using hcoeffAux
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsrc, hcoeffPhys⟩

private theorem physicalDestination_eq_taggedImage
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace) (v : M.Vertex) :
    destinationSelected (Physical M S h) (physicalRestriction M S K h x hKS)
      (oldVertex M S v) =
    ((internalEdges M K).attach.filter fun e : {e : M.Edge // e ∈ internalEdges M K} =>
      M.dst e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).image
        (internalDirectEdge M S K h hKS) := by
  classical
  ext i
  constructor
  · intro hi
    have hsel := (Finset.mem_filter.mp hi).2
    have hmemPhysical : i ∈ internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      by_contra hn
      simp [physicalRestriction, hn] at hsel
    have hmemImage := hmemPhysical
    rw [rootPort_internalEdges_image_eq M S K h hKS] at hmemImage
    rcases Finset.mem_image.mp hmemImage with ⟨e, heattach, heq⟩
    have hphi : internalDirectEdge M S K h hKS e ∈
        internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      rw [heq]
      exact hmemPhysical
    have hauxEq : auxiliaryRestriction M K x e.1 = x.1 e.1 := by
      simp [auxiliaryRestriction, e.2]
    have hdest : M.dst e.1 = v := by
      have hdst := hsel.1
      rw [← heq] at hdst
      have hdst' : oldVertex M S (M.dst e.1) = oldVertex M S v := by
        simpa [internalDirectEdge, dst_internalEdge] using hdst
      exact oldVertex_injective M S hdst'
    have hword : (rootPortCycleEquiv M S h x).1
        (internalDirectEdge M S K h hKS e) = x.1 e.1 :=
      rootPortCycleEquiv_internalEdges_word M S K h hKS x e
    have hxcoeff : x.1 e.1 ≠ 0 := by
      intro hz
      apply hsel.2
      rw [← heq]
      simpa [physicalRestriction, hphi, hword, hz]
    have hcoeff : auxiliaryRestriction M K x e.1 ≠ 0 := by
      simpa [hauxEq] using hxcoeff
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ?_, heq⟩
    exact ⟨heattach, hdest, hcoeff⟩
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, rfl⟩
    have heprops := (Finset.mem_filter.mp he).2
    have hmem : internalDirectEdge M S K h hKS e ∈
        internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      rw [rootPort_internalEdges_image_eq M S K h hKS]
      exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mp he |>.1, rfl⟩
    have hdst : (Physical M S h).dst (internalDirectEdge M S K h hKS e) =
        oldVertex M S v := by
      simpa [internalDirectEdge, dst_internalEdge] using
        congrArg (oldVertex M S) heprops.1
    have hword : (rootPortCycleEquiv M S h x).1
        (internalDirectEdge M S K h hKS e) = x.1 e.1 :=
      rootPortCycleEquiv_internalEdges_word M S K h hKS x e
    have hcoeffAux : x.1 e.1 ≠ 0 := by
      simpa [auxiliaryRestriction, e.2] using heprops.2
    have hcoeffPhys : physicalRestriction M S K h x hKS
        (internalDirectEdge M S K h hKS e) ≠ 0 := by
      simpa [physicalRestriction, hmem, hword] using hcoeffAux
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdst, hcoeffPhys⟩

theorem selectedDegree_eq_auxiliaryRestriction
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace) (v : M.Vertex) :
    selectedDegree (Physical M S h) (physicalRestriction M S K h x hKS)
        (oldVertex M S v) =
      selectedDegree M (auxiliaryRestriction M K x) v := by
  classical
  have hsource :
      (sourceSelected (Physical M S h) (physicalRestriction M S K h x hKS)
          (oldVertex M S v)).card =
        (sourceSelected M (auxiliaryRestriction M K x) v).card := by
    calc
      _ = (((internalEdges M K).attach.filter fun e :
          {e : M.Edge // e ∈ internalEdges M K} =>
          M.src e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).image
            (internalDirectEdge M S K h hKS)).card :=
          congrArg Finset.card (physicalSource_eq_taggedImage M S K h hKS x v)
      _ = ((internalEdges M K).attach.filter fun e :
          {e : M.Edge // e ∈ internalEdges M K} =>
          M.src e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).card :=
          Finset.card_image_of_injective _ (internalDirectEdge_injective M S K h hKS)
      _ = (sourceSelected M (auxiliaryRestriction M K x) v).card :=
          (auxiliarySource_card_eq_tagged M K x v).symm
  have hdestination :
      (destinationSelected (Physical M S h) (physicalRestriction M S K h x hKS)
          (oldVertex M S v)).card =
        (destinationSelected M (auxiliaryRestriction M K x) v).card := by
    calc
      _ = (((internalEdges M K).attach.filter fun e :
          {e : M.Edge // e ∈ internalEdges M K} =>
          M.dst e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).image
            (internalDirectEdge M S K h hKS)).card :=
          congrArg Finset.card (physicalDestination_eq_taggedImage M S K h hKS x v)
      _ = ((internalEdges M K).attach.filter fun e :
          {e : M.Edge // e ∈ internalEdges M K} =>
          M.dst e.1 = v ∧ auxiliaryRestriction M K x e.1 ≠ 0).card :=
          Finset.card_image_of_injective _ (internalDirectEdge_injective M S K h hKS)
      _ = (destinationSelected M (auxiliaryRestriction M K x) v).card :=
          (auxiliaryDestination_card_eq_tagged M K x v).symm
  have hsum :
      (sourceSelected (Physical M S h) (physicalRestriction M S K h x hKS)
        (oldVertex M S v)).card +
      (destinationSelected (Physical M S h) (physicalRestriction M S K h x hKS)
        (oldVertex M S v)).card =
      (sourceSelected M (auxiliaryRestriction M K x) v).card +
      (destinationSelected M (auxiliaryRestriction M K x) v).card := by
    rw [hsource, hdestination]
  simpa [selectedDegree, sourceSelected, destinationSelected,
    Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hsum

private theorem selectedDegree_eq_zero_outside_oldVertexImage
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace) (v : (Physical M S h).Vertex)
    (hv : v ∉ oldVertexImage M S h K) :
    selectedDegree (Physical M S h) (physicalRestriction M S K h x hKS) v = 0 := by
  classical
  have hsource :
      (Finset.univ.filter fun e : (Physical M S h).Edge =>
        physicalRestriction M S K h x hKS e ≠ 0).filter
        (fun e => (Physical M S h).src e = v) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    rcases Finset.mem_filter.mp he with ⟨hselected, hsrc⟩
    have hword : physicalRestriction M S K h x hKS e ≠ 0 :=
      (Finset.mem_filter.mp hselected).2
    have hinter : e ∈ internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      by_contra hn
      exact hword (by simp [physicalRestriction, hn])
    have hsrcImage := (Finset.mem_filter.mp hinter).2.1
    change (Physical M S h).src e ∈ oldVertexImage M S h K at hsrcImage
    rw [hsrc] at hsrcImage
    exact hv hsrcImage
  have hdestination :
      (Finset.univ.filter fun e : (Physical M S h).Edge =>
        physicalRestriction M S K h x hKS e ≠ 0).filter
        (fun e => (Physical M S h).dst e = v) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    rcases Finset.mem_filter.mp he with ⟨hselected, hdst⟩
    have hword : physicalRestriction M S K h x hKS e ≠ 0 :=
      (Finset.mem_filter.mp hselected).2
    have hinter : e ∈ internalEdges (Physical M S h) (oldVertexImage M S h K) := by
      by_contra hn
      exact hword (by simp [physicalRestriction, hn])
    have hdstImage := (Finset.mem_filter.mp hinter).2.2
    change (Physical M S h).dst e ∈ oldVertexImage M S h K at hdstImage
    rw [hdst] at hdstImage
    exact hv hdstImage
  simp [selectedDegree, hsource, hdestination]

/-- The physical restriction satisfies the degree-two clause whenever the
auxiliary restriction does. Vertices introduced by the port expansion have
degree zero in this restriction. -/
theorem selectedDegree_le_two_of_auxiliary
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace)
    (hdegree : ∀ v, selectedDegree M (auxiliaryRestriction M K x) v ≤ 2) :
    ∀ v, selectedDegree (Physical M S h) (physicalRestriction M S K h x hKS) v ≤ 2 := by
  intro v
  by_cases hv : v ∈ oldVertexImage M S h K
  · rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    rw [selectedDegree_eq_auxiliaryRestriction M S K h hKS x u]
    exact hdegree u
  · rw [selectedDegree_eq_zero_outside_oldVertexImage M S K h hKS x v hv]
    omega

/-- All linear-forest clauses except acyclicity transfer directly through the
root-port expansion. Supply acyclicity of the restricted physical graph to
obtain the complete predicate. -/
theorem isLinearForestWord_of_restricted_acyclic
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace)
    (hdegree : ∀ v, selectedDegree M (auxiliaryRestriction M K x) v ≤ 2)
    (hacyclic : (selectedGraph (Physical M S h)
      (physicalRestriction M S K h x hKS)).IsAcyclic) :
    IsLinearForestWord (Physical M S h) (physicalRestriction M S K h x hKS) := by
  have hsimple := rootPort_word_loopless_parallel M S h
    (physicalRestriction M S K h x hKS)
  have hdegreePhysical := selectedDegree_le_two_of_auxiliary M S K h hKS x hdegree
  exact ⟨hsimple.1, hsimple.2, hacyclic, hdegreePhysical⟩

/-- Apply the restriction transfer to a complete auxiliary linear-forest
word, leaving only the graph-specific acyclicity transport as an input. -/
theorem isLinearForestWord_of_auxiliary
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace)
    (haux : IsLinearForestWord M (auxiliaryRestriction M K x))
    (hacyclic : (selectedGraph (Physical M S h)
      (physicalRestriction M S K h x hKS)).IsAcyclic) :
    IsLinearForestWord (Physical M S h) (physicalRestriction M S K h x hKS) := by
  exact isLinearForestWord_of_restricted_acyclic M S K h hKS x
    haux.2.2.2 hacyclic

/-- The root-port cycle equivalence preserves the complete linear-forest
event after restricting to edges internal to `K`. -/
theorem isLinearForestWord_of_auxiliary_complete
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace)
    (haux : IsLinearForestWord M (auxiliaryRestriction M K x)) :
    IsLinearForestWord (Physical M S h) (physicalRestriction M S K h x hKS) := by
  have hacyclic : (selectedGraph (Physical M S h)
      (physicalRestriction M S K h x hKS)).IsAcyclic := by
    simpa [physicalRestriction, rootPortPhysicalRestriction,
      auxiliaryRestriction, rootPortAuxRestriction] using
      (rootPort_restriction_isAcyclic_iff M S K h hKS x).mp haux.2.2.1
  exact isLinearForestWord_of_auxiliary M S K h hKS x haux hacyclic

private theorem auxiliarySelectedDegree_eq_zero_outside_K
    (M : FiniteMultiGraph) (K : Finset M.Vertex) (x : M.CycleSpace)
    (v : M.Vertex) (hv : v ∉ K) :
    selectedDegree M (auxiliaryRestriction M K x) v = 0 := by
  classical
  have hsource :
      (Finset.univ.filter fun e : M.Edge =>
        auxiliaryRestriction M K x e ≠ 0).filter (fun e => M.src e = v) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    rcases Finset.mem_filter.mp he with ⟨hselected, hsrc⟩
    have hword : auxiliaryRestriction M K x e ≠ 0 :=
      (Finset.mem_filter.mp hselected).2
    have hinter : e ∈ internalEdges M K := by
      by_contra hn
      exact hword (by simp [auxiliaryRestriction, hn])
    have hsrcK := (Finset.mem_filter.mp hinter).2.1
    rw [hsrc] at hsrcK
    exact hv hsrcK
  have hdestination :
      (Finset.univ.filter fun e : M.Edge =>
        auxiliaryRestriction M K x e ≠ 0).filter (fun e => M.dst e = v) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    rcases Finset.mem_filter.mp he with ⟨hselected, hdst⟩
    have hword : auxiliaryRestriction M K x e ≠ 0 :=
      (Finset.mem_filter.mp hselected).2
    have hinter : e ∈ internalEdges M K := by
      by_contra hn
      exact hword (by simp [auxiliaryRestriction, hn])
    have hdstK := (Finset.mem_filter.mp hinter).2.2
    rw [hdst] at hdstK
    exact hv hdstK
  simp [selectedDegree, hsource, hdestination]

private theorem isLinearForestWord_of_physical_restriction
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace)
    (hphysical : IsLinearForestWord (Physical M S h)
      (physicalRestriction M S K h x hKS)) :
    IsLinearForestWord M (auxiliaryRestriction M K x) := by
  have hacyclic : (selectedGraph M (auxiliaryRestriction M K x)).IsAcyclic := by
    simpa [physicalRestriction, rootPortPhysicalRestriction,
      auxiliaryRestriction, rootPortAuxRestriction] using
      (rootPort_restriction_isAcyclic_iff M S K h hKS x).mpr
        hphysical.2.2.1
  have hdegree : ∀ v, selectedDegree M (auxiliaryRestriction M K x) v ≤ 2 := by
    intro v
    by_cases hv : v ∈ K
    · have hdegreeEq := selectedDegree_eq_auxiliaryRestriction M S K h hKS x v
      rw [← hdegreeEq]
      exact hphysical.2.2.2 (oldVertex M S v)
    · rw [auxiliarySelectedDegree_eq_zero_outside_K M K x v hv]
      omega
  have hloop : ∀ e, auxiliaryRestriction M K x e ≠ 0 → M.src e ≠ M.dst e := by
    intro e he
    have hinter : e ∈ internalEdges M K := by
      by_contra hn
      have hnot : ¬ (M.src e ∈ K ∧ M.dst e ∈ K) := by
        intro hp
        apply hn
        simp [internalEdges, hp]
      exact he (by unfold auxiliaryRestriction; rw [if_neg hn])
    have hend := (Finset.mem_filter.mp hinter).2
    exact h.2.1 e (hKS hend.1) (hKS hend.2)
  have hparallel : ∀ e f, e ≠ f → auxiliaryRestriction M K x e ≠ 0 →
      auxiliaryRestriction M K x f ≠ 0 →
      ((M.src e = M.src f ∧ M.dst e = M.dst f) ∨
        (M.src e = M.dst f ∧ M.dst e = M.src f)) → False := by
    intro e f hef he hf hends
    have heInternal : e ∈ internalEdges M K := by
      by_contra hn
      have hnot : ¬ (M.src e ∈ K ∧ M.dst e ∈ K) := by
        intro hp
        apply hn
        simp [internalEdges, hp]
      exact he (by unfold auxiliaryRestriction; rw [if_neg hn])
    have hfInternal : f ∈ internalEdges M K := by
      by_contra hn
      have hnot : ¬ (M.src f ∈ K ∧ M.dst f ∈ K) := by
        intro hp
        apply hn
        simp [internalEdges, hp]
      exact hf (by unfold auxiliaryRestriction; rw [if_neg hn])
    have heProps := (Finset.mem_filter.mp heInternal).2
    have hfProps := (Finset.mem_filter.mp hfInternal).2
    exact hef (h.2.2 e f (hKS heProps.1) (hKS heProps.2)
      (hKS hfProps.1) (hKS hfProps.2) hends)
  exact ⟨hloop, hparallel, hacyclic, hdegree⟩

theorem isLinearForestWord_auxiliary_iff_physical
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (x : M.CycleSpace) :
    IsLinearForestWord M (auxiliaryRestriction M K x) ↔
      IsLinearForestWord (Physical M S h) (physicalRestriction M S K h x hKS) := by
  constructor
  · exact isLinearForestWord_of_auxiliary_complete M S K h hKS x
  · exact isLinearForestWord_of_physical_restriction M S K h hKS x

/-- Exact equality of the auxiliary and expanded region probabilities. The
cycle-space equivalence transports the good-event subtype bijectively, and
preserves cycle rank for the normalization. -/
def auxiliaryForestEvent (M : FiniteMultiGraph) (K : Finset M.Vertex)
    (x : M.CycleSpace) : Prop :=
  IsLinearForestWord M (auxiliaryRestriction M K x)

def physicalForestEvent (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (y : (Physical M S h).CycleSpace) : Prop :=
    IsLinearForestWord (Physical M S h)
      (fun e => if e ∈ internalEdges (Physical M S h) (oldVertexImage M S h K)
        then y.1 e else 0)

noncomputable def auxiliaryForestEventFinset (M : FiniteMultiGraph)
    (K : Finset M.Vertex) : Finset M.CycleSpace := by
  classical
  letI : Fintype M.CycleSpace := FiniteMultiGraph.cycleSpaceFintype M
  exact Finset.univ.filter (auxiliaryForestEvent M K)

noncomputable def physicalForestEventFinset (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) :
    Finset (Physical M S h).CycleSpace := by
  classical
  letI : Fintype (Physical M S h).CycleSpace :=
    FiniteMultiGraph.cycleSpaceFintype (Physical M S h)
  exact Finset.univ.filter (physicalForestEvent M S K h)

noncomputable def rootPortForestEventEquiv
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    {x : M.CycleSpace // auxiliaryForestEvent M K x} ≃
      {y : (Physical M S h).CycleSpace // physicalForestEvent M S K h y} := by
  classical
  letI : Fintype M.CycleSpace := FiniteMultiGraph.cycleSpaceFintype M
  let f : {x : M.CycleSpace // auxiliaryForestEvent M K x} →
      {y : (Physical M S h).CycleSpace // physicalForestEvent M S K h y} := fun x =>
    ⟨rootPortCycleEquiv M S h x.1, by
      have hp := (isLinearForestWord_auxiliary_iff_physical M S K h hKS x.1).mp x.2
      simpa [auxiliaryForestEvent, physicalForestEvent,
        auxiliaryRestriction, physicalRestriction] using hp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      have hcycleEq : rootPortCycleEquiv M S h x.1 =
          rootPortCycleEquiv M S h y.1 := congrArg
            (fun z : {y : (Physical M S h).CycleSpace //
              physicalForestEvent M S K h y} => z.1) hxy
      exact (rootPortCycleEquiv M S h).injective hcycleEq
    · intro y
      let x := (rootPortCycleEquiv M S h).symm y.1
      have hcycle : rootPortCycleEquiv M S h x = y.1 :=
        (rootPortCycleEquiv M S h).apply_symm_apply y.1
      have hword : (rootPortCycleEquiv M S h x).1 = y.1.1 :=
        congrArg Subtype.val hcycle
      have hphysical : IsLinearForestWord (Physical M S h)
          (physicalRestriction M S K h x hKS) := by
        have hQ : IsLinearForestWord (Physical M S h)
            (fun e => if e ∈ internalEdges (Physical M S h)
              (oldVertexImage M S h K) then y.1.1 e else 0) := y.2
        have hrestrict : physicalRestriction M S K h x hKS =
            (fun e => if e ∈ internalEdges (Physical M S h)
              (oldVertexImage M S h K) then y.1.1 e else 0) := by
          funext e
          simp [physicalRestriction, hword]
        rw [hrestrict]
        exact hQ
      have hauxiliary : IsLinearForestWord M (auxiliaryRestriction M K x) :=
        (isLinearForestWord_auxiliary_iff_physical M S K h hKS x).mpr hphysical
      refine ⟨⟨x, ?_⟩, ?_⟩
      · simpa [auxiliaryForestEvent] using hauxiliary
      · apply Subtype.ext
        exact hcycle
  exact Equiv.ofBijective f hf

set_option maxHeartbeats 5000000

/-- These finite cardinality transfers unfold large cycle-space subtype
instances, so the local elaboration budget is larger than Lean's default. -/
theorem rootPortForestEvent_card_eq
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
      (auxiliaryForestEventFinset M K).card =
      (physicalForestEventFinset M S K h).card := by
  classical
  letI : Fintype M.CycleSpace := FiniteMultiGraph.cycleSpaceFintype M
  letI : Fintype (Physical M S h).CycleSpace :=
    FiniteMultiGraph.cycleSpaceFintype (Physical M S h)
  letI : DecidablePred (auxiliaryForestEvent M K) := Classical.decPred _
  letI : DecidablePred (physicalForestEvent M S K h) := Classical.decPred _
  have hcountAux : (auxiliaryForestEventFinset M K).card =
      Fintype.card {x : M.CycleSpace // auxiliaryForestEvent M K x} := by
    change (Finset.univ.filter (auxiliaryForestEvent M K)).card = _
    exact filter_univ_card_eq_subtype_card (auxiliaryForestEvent M K)
  have hcountPhysical :
      (physicalForestEventFinset M S K h).card =
        Fintype.card {y : (Physical M S h).CycleSpace //
          physicalForestEvent M S K h y} := by
    simpa only [physicalForestEventFinset] using
      (@filter_univ_card_eq_subtype_card
        ((Physical M S h).CycleSpace) (physicalForestEvent M S K h)
        (FiniteMultiGraph.cycleSpaceFintype (Physical M S h))
        (Classical.decPred _))
  rw [hcountAux, hcountPhysical]
  exact Fintype.card_congr (rootPortForestEventEquiv M S K h hKS)

theorem rootPort_cycleRank_eq
    (M : FiniteMultiGraph) (S : Finset M.Vertex) (h : IsCleanupRoot M S) :
    M.cycleRank = (Physical M S h).cycleRank := by
  unfold FiniteMultiGraph.cycleRank
  exact (rootPortCycleEquiv M S h).finrank_eq

set_option maxHeartbeats 5000000
theorem regionForestProbability_rootPort_eq
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    regionForestProbability M K =
      regionForestProbability (Physical M S h) (oldVertexImage M S h K) := by
  classical
  have hauxProbability : regionForestProbability M K =
      ((auxiliaryForestEventFinset M K).card : ℝ) /
        (2 : ℝ) ^ M.cycleRank := by
    rfl
  have hphysicalProbability :
      regionForestProbability (Physical M S h) (oldVertexImage M S h K) =
        ((physicalForestEventFinset M S K h).card : ℝ) /
          (2 : ℝ) ^ (Physical M S h).cycleRank := by
    unfold regionForestProbability physicalForestEventFinset physicalForestEvent
    rfl
  rw [hauxProbability, hphysicalProbability,
    rootPortForestEvent_card_eq M S K h hKS,
    ← rootPort_cycleRank_eq M S h]

end Erdos1016.Proof.PortSelectedDegree

end
