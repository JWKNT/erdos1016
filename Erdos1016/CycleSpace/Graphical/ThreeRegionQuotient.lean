import Erdos1016.CycleSpace.Graphical.QuotientTripleStar
import Erdos1016.CycleSpace.Graphical.SubdivisionTripleStar
import Erdos1016.CycleSpace.Graphical.InternalComponentParity
import Erdos1016.CycleSpace.Graphical.ConnectedFiberQuotient

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.ThreeRegionCrossingQuotientGeometry

open Erdos1016
open Erdos1016.Proof.PhysicalFiberQuotientConnected
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.PhysicalActualCutTripleQuotientPackage
open Erdos1016.Proof.ActualCutPairProbability
open Erdos1016.Proof.GraphicalActualCutMultigraphSurjective
open Erdos1016.Proof.InternalRegionBoundaryRepair
open Erdos1016.Proof.QuotientCycleInternalComponentParity
open Erdos1016.Proof.MultigraphSubdivisionTripleStar

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local notation "𝔽" => ZMod 2

/-- The three contracted regions. -/
inductive RegionTag
  | U | V | W
  deriving DecidableEq, Fintype

/-- A quotient with one vertex for each designated region and one vertex for
 each physical vertex outside their union. -/
def QuotientLabel (G : PhysicalGraph) (U V W : Finset G.Vertex) :=
  Sum RegionTag {x : G.Vertex // x ∉ U ∧ x ∉ V ∧ x ∉ W}

noncomputable instance outsideFintype (G : PhysicalGraph)
    (U V W : Finset G.Vertex) :
    Fintype {x : G.Vertex // x ∉ U ∧ x ∉ V ∧ x ∉ W} := Fintype.ofFinite _

noncomputable instance quotientLabelFintype (G : PhysicalGraph)
    (U V W : Finset G.Vertex) : Fintype (QuotientLabel G U V W) := by
  change Fintype (Sum RegionTag {x : G.Vertex // x ∉ U ∧ x ∉ V ∧ x ∉ W})
  infer_instance


def fiber (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hdisjUV : Disjoint U V) (hdisjUW : Disjoint U W)
    (hdisjVW : Disjoint V W) : G.Vertex → QuotientLabel G U V W := by
  classical
  intro x
  by_cases hxU : x ∈ U
  · exact Sum.inl RegionTag.U
  · by_cases hxV : x ∈ V
    · exact Sum.inl RegionTag.V
    · by_cases hxW : x ∈ W
      · exact Sum.inl RegionTag.W
      · exact Sum.inr ⟨x, hxU, hxV, hxW⟩

@[simp] theorem fiber_eq_U_iff (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (x : G.Vertex) :
    fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.U ↔ x ∈ U := by
  classical
  constructor
  · intro h
    by_contra hx
    by_cases hv : x ∈ V
    · have hnot : x ∉ U := hx
      simp [fiber, hnot, hv] at h
      cases h
    · by_cases hw : x ∈ W
      · simp [fiber, hx, hv, hw] at h
        cases h
      · simp [fiber, hx, hv, hw] at h
  · intro hx
    simp [fiber, hx]

@[simp] theorem fiber_eq_V_iff (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (x : G.Vertex) :
    fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.V ↔ x ∈ V := by
  classical
  constructor
  · intro h
    by_contra hxV
    by_cases hxU : x ∈ U
    · simp [fiber, hxU] at h
      cases h
    · by_cases hxW : x ∈ W
      · simp [fiber, hxU, hxV, hxW] at h
        cases h
      · simp [fiber, hxU, hxV, hxW] at h
  · intro hxV
    have hxU : x ∉ U := by
      intro hxU
      exact Finset.disjoint_left.mp hUV hxU hxV
    simp [fiber, hxU, hxV]

@[simp] theorem fiber_eq_W_iff (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (x : G.Vertex) :
    fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.W ↔ x ∈ W := by
  classical
  constructor
  · intro h
    by_contra hxW
    by_cases hxU : x ∈ U
    · simp [fiber, hxU] at h
      cases h
    · by_cases hxV : x ∈ V
      · simp [fiber, hxU, hxV] at h
        cases h
      · simp [fiber, hxU, hxV, hxW] at h
  · intro hxW
    have hxU : x ∉ U := by
      intro hxU
      exact Finset.disjoint_left.mp hUW hxU hxW
    have hxV : x ∉ V := by
      intro hxV
      exact Finset.disjoint_left.mp hVW hxV hxW
    simp [fiber, hxU, hxV, hxW]

/-- Every quotient label has a physical representative. -/
theorem fiber_surjective (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (hneU : U.Nonempty) (hneV : V.Nonempty) (hneW : W.Nonempty) :
    Function.Surjective (fiber G U V W hUV hUW hVW) := by
  classical
  intro q
  cases q with
  | inl tag =>
    cases tag with
    | U =>
      obtain ⟨x, hx⟩ := hneU
      exact ⟨x, (fiber_eq_U_iff G U V W hUV hUW hVW x).2 hx⟩
    | V =>
      obtain ⟨x, hx⟩ := hneV
      exact ⟨x, (fiber_eq_V_iff G U V W hUV hUW hVW x).2 hx⟩
    | W =>
      obtain ⟨x, hx⟩ := hneW
      exact ⟨x, (fiber_eq_W_iff G U V W hUV hUW hVW x).2 hx⟩
  | inr outside => exact ⟨outside.1, by simp [fiber, outside.2.1, outside.2.2.1, outside.2.2.2]⟩

/-- A connected induced region is the induced graph on its quotient fiber. -/
theorem regionFiber_connected (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (hW : (G.toSimpleGraph.induce (↑W : Set G.Vertex)).Connected) :
    ∀ q : QuotientLabel G U V W,
      (G.toSimpleGraph.induce {x | fiber G U V W hUV hUW hVW x = q}).Connected := by
  classical
  intro q
  cases q with
  | inl tag =>
      cases tag with
      | U =>
        have hs : {x : G.Vertex | fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.U} = ↑U := by
          ext x; simp [fiber_eq_U_iff]
        rw [hs]; exact hU
      | V =>
        have hs : {x : G.Vertex | fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.V} = ↑V := by
          ext x; simp [fiber_eq_V_iff]
        rw [hs]; exact hV
      | W =>
        have hs : {x : G.Vertex | fiber G U V W hUV hUW hVW x = Sum.inl RegionTag.W} = ↑W := by
          ext x; simp [fiber_eq_W_iff]
        rw [hs]; exact hW
  | inr outside =>
      have hs : {x : G.Vertex | fiber G U V W hUV hUW hVW x = Sum.inr outside} = {outside.1} := by
        ext x
        constructor
        · intro hx
          change fiber G U V W hUV hUW hVW x = Sum.inr outside at hx
          have hval := hx
          unfold fiber at hval
          by_cases hu : x ∈ U
          · simp [hu] at hval
          · by_cases hv : x ∈ V
            · simp [hu, hv] at hval
            · by_cases hw : x ∈ W
              · simp [hu, hv, hw] at hval
              · simp [hu, hv, hw] at hval
                have heq := Sum.inr.inj hval
                exact congrArg Subtype.val heq
        · intro hx
          rw [Set.mem_singleton_iff] at hx
          subst x
          simp [fiber, outside.2.1, outside.2.2.1, outside.2.2.2]
      rw [hs]
      haveI : Nonempty ({x : G.Vertex // x ∈ ({outside.1} : Set G.Vertex)}) :=
        ⟨⟨outside.1, by simp⟩⟩
      refine ⟨?_⟩
      intro a b
      have ha : a.1 = outside.1 := Set.mem_singleton_iff.mp a.2
      have hb : b.1 = outside.1 := Set.mem_singleton_iff.mp b.2
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      rw [hab]


private abbrev ClassFiber (G : PhysicalGraph) (M : FiniteMultiGraph)
    (classOf : G.Vertex → M.Vertex) (q : M.Vertex) :=
  {v : G.Vertex // classOf v = q}

private theorem classFiberEndpointSum
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (classOf : G.Vertex → M.Vertex) (q : M.Vertex)
    (a : G.Vertex) (x : 𝔽) :
    (∑ v : ClassFiber G M classOf q, if a = v.1 then x else 0) =
      if classOf a = q then x else 0 := by
  classical
  by_cases hq : classOf a = q
  · let w : ClassFiber G M classOf q := ⟨a, hq⟩
    have hiff : ∀ v : ClassFiber G M classOf q, a = v.1 ↔ v = w := by
      intro v
      constructor
      · intro hav
        apply Subtype.ext
        exact hav.symm
      · intro hvw
        exact (congrArg Subtype.val hvw).symm
    simp [hq, hiff, w]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro v hv
    have hne : a ≠ v.1 := by
      intro hav
      exact hq (hav ▸ v.2)
    simp [hne]

/-- Boundary aggregation for any physical word across a quotient partition.
This is the restriction identity needed to show a physical cycle maps to a
quotient cycle. -/
private theorem classFiberBoundary_eq_quotientBoundary
    (G : PhysicalGraph) (M : FiniteMultiGraph)
    (edgeMap : M.Edge → G.Edge) (hinj : Function.Injective edgeMap)
    (classOf : G.Vertex → M.Vertex)
    (hsrc : ∀ e, M.src e = classOf (G.src (edgeMap e)))
    (hdst : ∀ e, M.dst e = classOf (G.dst (edgeMap e)))
    (hcoverage : ∀ a : G.Edge,
      (∃ e, edgeMap e = a) ∨ classOf (G.src a) = classOf (G.dst a))
    (x : G.Word) (q : M.Vertex) :
    (∑ v : ClassFiber G M classOf q, G.boundary x v.1) =
      M.boundary (GraphicalActualCutMultigraphBridge.restrictWord M edgeMap x) q := by
  classical
  have hfiber (a : G.Edge) :
      (∑ v : ClassFiber G M classOf q,
        ((if G.src a = v.1 then x a else 0) +
         (if G.dst a = v.1 then x a else 0))) =
      (if classOf (G.src a) = q then x a else 0) +
      (if classOf (G.dst a) = q then x a else 0) := by
    rw [Finset.sum_add_distrib]
    rw [classFiberEndpointSum G M classOf q (G.src a) (x a)]
    rw [classFiberEndpointSum G M classOf q (G.dst a) (x a)]
  have hsumImage :
      (∑ a : G.Edge,
        ((if classOf (G.src a) = q then x a else 0) +
         (if classOf (G.dst a) = q then x a else 0))) =
      ∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then x a else 0) +
         (if classOf (G.dst a) = q then x a else 0)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _) ?_
    intro a ha hna
    have hsame := (hcoverage a).resolve_left (by
      intro hex
      apply hna
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact hex)
    by_cases hs : classOf (G.src a) = q
    · have ht : classOf (G.dst a) = q := hsame.symm.trans hs
      simp only [if_pos hs, if_pos ht]
      have htwo : (2 : 𝔽) = 0 := by decide
      calc
        x a + x a = (2 : 𝔽) * x a := by ring
        _ = 0 := by rw [htwo]; simp
    · have ht : classOf (G.dst a) ≠ q := by
        intro ht
        exact hs (hsame.trans ht)
      simp [hs, ht]
  have hedgeReindex :
      (∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then x a else 0) +
         (if classOf (G.dst a) = q then x a else 0))) =
      ∑ e : M.Edge,
        ((if M.src e = q then x (edgeMap e) else 0) +
         (if M.dst e = q then x (edgeMap e) else 0)) := by
    rw [Finset.sum_image (fun a ha b hb hab => hinj hab)]
    apply Fintype.sum_congr
    intro e
    rw [hsrc e, hdst e]
  calc
    (∑ v : ClassFiber G M classOf q, G.boundary x v.1) =
      ∑ a : G.Edge,
        ((if classOf (G.src a) = q then x a else 0) +
         (if classOf (G.dst a) = q then x a else 0)) := by
      change (∑ v : ClassFiber G M classOf q, ∑ a : G.Edge,
        ((if G.src a = v.1 then x a else 0) +
         (if G.dst a = v.1 then x a else 0))) = _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      exact hfiber a
    _ = ∑ a ∈ Finset.univ.image edgeMap,
        ((if classOf (G.src a) = q then x a else 0) +
         (if classOf (G.dst a) = q then x a else 0)) := hsumImage
    _ = ∑ e : M.Edge,
        ((if M.src e = q then x (edgeMap e) else 0) +
         (if M.dst e = q then x (edgeMap e) else 0)) := hedgeReindex
    _ = M.boundary (GraphicalActualCutMultigraphBridge.restrictWord M edgeMap x) q := rfl

private theorem incident_iff_xor_of_ne {α : Type*} [DecidableEq α]
    (a b u : α) (hab : a ≠ b) :
    (a = u ∨ b = u) ↔ (a = u ∧ b ≠ u) ∨ (a ≠ u ∧ b = u) := by
  by_cases ha : a = u <;> by_cases hb : b = u
  · exact False.elim (hab (ha.trans hb.symm))
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

private def sameClassEdges (G : PhysicalGraph) (M : FiniteMultiGraph)
    (classOf : G.Vertex → M.Vertex) : Finset G.Edge := by
  classical
  exact Finset.univ.filter fun e => classOf (G.src e) = classOf (G.dst e)

/-- The crossing quotient for the three-region/singleton-outside partition. -/
noncomputable def quotientGraph (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :=
  crossingQuotient G (QuotientLabel G U V W) (fiber G U V W hUV hUW hVW)

noncomputable def quotientVertex (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (t : RegionTag) : (quotientGraph G U V W hUV hUW hVW).Vertex :=
  quotientVertexEquiv (QuotientLabel G U V W) (Sum.inl t)

theorem quotient_designated_vertices_distinct (G : PhysicalGraph)
    (U V W : Finset G.Vertex) (hUV : Disjoint U V) (hUW : Disjoint U W)
    (hVW : Disjoint V W) :
    let u := quotientVertex G U V W hUV hUW hVW RegionTag.U
    let v := quotientVertex G U V W hUV hUW hVW RegionTag.V
    let w := quotientVertex G U V W hUV hUW hVW RegionTag.W
    u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  constructor
  · intro h
    have : Sum.inl RegionTag.U = Sum.inl RegionTag.V :=
      (quotientVertexEquiv (QuotientLabel G U V W)).injective h
    cases this
  constructor
  · intro h
    have : Sum.inl RegionTag.U = Sum.inl RegionTag.W :=
      (quotientVertexEquiv (QuotientLabel G U V W)).injective h
    cases this
  · intro h
    have : Sum.inl RegionTag.V = Sum.inl RegionTag.W :=
      (quotientVertexEquiv (QuotientLabel G U V W)).injective h
    cases this






/-- Contracting the three connected regions and retaining all outside
vertices preserves connectedness. -/
theorem quotient_connected (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (hneU : U.Nonempty) (hneV : V.Nonempty) (hneW : W.Nonempty)
    (hG : G.IsConnected) :
    (quotientGraph G U V W hUV hUW hVW).toSimpleGraph.Connected := by
  classical
  exact crossingQuotient_connected G (QuotientLabel G U V W)
    (fiber G U V W hUV hUW hVW)
    (fiber_surjective G U V W hUV hUW hVW hneU hneV hneW) hG






/-- The concrete quotient package required by the Section 9 adapter. Besides
the rank conclusion, this returns the actual `Data` witness for the canonical
three-region/singleton-outside quotient. -/
theorem threeRegionQuotientData_and_rank_bound
    (G : PhysicalGraph) (U V W : Finset G.Vertex)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W)
    (hneU : U.Nonempty) (hneV : V.Nonempty) (hneW : W.Nonempty)
    (hU : (G.toSimpleGraph.induce (↑U : Set G.Vertex)).Connected)
    (hV : (G.toSimpleGraph.induce (↑V : Set G.Vertex)).Connected)
    (hW : (G.toSimpleGraph.induce (↑W : Set G.Vertex)).Connected)
    (hG : G.IsConnected) :
    ∃ D : Data G (quotientGraph G U V W hUV hUW hVW) U V W,
      Module.finrank 𝔽
        (subspaceInter (subspaceInter (cutConstraintSpace G U)
          (cutConstraintSpace G V)) (cutConstraintSpace G W)) ≤ 1 := by
  classical
  let Q := QuotientLabel G U V W
  let f := fiber G U V W hUV hUW hVW
  let M := quotientGraph G U V W hUV hUW hVW
  let edgeMap := crossingQuotientEdgeMap G Q f
  let classOf := quotientClassOf G Q f
  let u := quotientVertex G U V W hUV hUW hVW RegionTag.U
  let v := quotientVertex G U V W hUV hUW hVW RegionTag.V
  let w := quotientVertex G U V W hUV hUW hVW RegionTag.W
  have hinj : Function.Injective edgeMap := crossingQuotientEdgeMap_injective G Q f
  have hsrc : ∀ e, M.src e = classOf (G.src (edgeMap e)) := by
    intro e
    change (crossingQuotient G Q f).src e =
      quotientClassOf G Q f (G.src (crossingQuotientEdgeMap G Q f e))
    exact crossingQuotient_src_edgeMap G Q f e
  have hdst : ∀ e, M.dst e = classOf (G.dst (edgeMap e)) := by
    intro e
    change (crossingQuotient G Q f).dst e =
      quotientClassOf G Q f (G.dst (crossingQuotientEdgeMap G Q f e))
    exact crossingQuotient_dst_edgeMap G Q f e
  have hcoverage : ∀ a : G.Edge,
      (∃ e, edgeMap e = a) ∨ classOf (G.src a) = classOf (G.dst a) := by
    intro a
    change (∃ e, crossingQuotientEdgeMap G Q f e = a) ∨
      quotientVertexEquiv Q (f (G.src a)) = quotientVertexEquiv Q (f (G.dst a))
    rcases crossingQuotient_edge_coverage G Q f a with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg (quotientVertexEquiv Q) h)
  have hfiber : ∀ q : M.Vertex,
      (G.toSimpleGraph.induce {x | classOf x = q}).Connected := by
    intro q
    let q' := (quotientVertexEquiv Q).symm q
    have hq : quotientVertexEquiv Q q' = q :=
      (quotientVertexEquiv Q).apply_symm_apply q
    have hc := regionFiber_connected G U V W hUV hUW hVW hU hV hW q'
    have hs : {x : G.Vertex | classOf x = q} =
        {x : G.Vertex | f x = q'} := by
      ext x
      change quotientVertexEquiv Q (f x) = q ↔ f x = q'
      constructor
      · intro hx
        apply (quotientVertexEquiv Q).injective
        exact hx.trans hq.symm
      · intro hx
        calc
          quotientVertexEquiv Q (f x) = quotientVertexEquiv Q q' :=
            congrArg (quotientVertexEquiv Q) hx
          _ = q := hq
    rw [hs]
    exact hc
  have hloopless : ∀ e : M.Edge, M.src e ≠ M.dst e := by
    intro e
    exact crossingQuotient_loopless G Q f e
  have hconn : M.toSimpleGraph.Connected :=
    quotient_connected G U V W hUV hUW hVW hneU hneV hneW hG
  have hdist : u ≠ v ∧ u ≠ w ∧ v ≠ w :=
    quotient_designated_vertices_distinct G U V W hUV hUW hVW
  have hUmem : ∀ a, a ∈ U ↔ classOf a = u := by
    intro a
    change a ∈ U ↔ quotientVertexEquiv Q (f a) =
      quotientVertexEquiv Q (Sum.inl RegionTag.U)
    rw [(quotientVertexEquiv Q).injective.eq_iff]
    exact (fiber_eq_U_iff G U V W hUV hUW hVW a).symm
  have hVmem : ∀ a, a ∈ V ↔ classOf a = v := by
    intro a
    change a ∈ V ↔ quotientVertexEquiv Q (f a) =
      quotientVertexEquiv Q (Sum.inl RegionTag.V)
    rw [(quotientVertexEquiv Q).injective.eq_iff]
    exact (fiber_eq_V_iff G U V W hUV hUW hVW a).symm
  have hWmem : ∀ a, a ∈ W ↔ classOf a = w := by
    intro a
    change a ∈ W ↔ quotientVertexEquiv Q (f a) =
      quotientVertexEquiv Q (Sum.inl RegionTag.W)
    rw [(quotientVertexEquiv Q).injective.eq_iff]
    exact (fiber_eq_W_iff G U V W hUV hUW hVW a).symm
  have hcycle : ∀ x : G.CycleSpace,
      M.boundary (GraphicalActualCutMultigraphBridge.restrictWord M edgeMap x.1) = 0 := by
    intro x
    funext q
    have hagg := classFiberBoundary_eq_quotientBoundary
      G M edgeMap hinj classOf hsrc hdst hcoverage x.1 q
    rw [← hagg]
    apply Finset.sum_eq_zero
    intro z hz
    exact congrFun x.2 z.1
  let I := sameClassEdges G M classOf
  have hI : ∀ e, e ∈ I ↔ classOf (G.src e) = classOf (G.dst e) := by
    intro e
    simp [I, sameClassEdges]
  have hdisjoint : ∀ e : M.Edge, edgeMap e ∉ I := by
    intro e he
    have hsame := (hI (edgeMap e)).mp he
    have hquot : M.src e = M.dst e := by
      calc
        M.src e = classOf (G.src (edgeMap e)) := hsrc e
        _ = classOf (G.dst (edgeMap e)) := hsame
        _ = M.dst e := (hdst e).symm
    exact hloopless e hquot
  have hrepair : ∀ y : M.CycleSpace, ∃ z : G.Word,
      G.boundary z = G.boundary
        (GraphicalActualCutMultigraphSurjective.rawLiftWord M edgeMap y.1) ∧
      ∀ e : M.Edge, z (edgeMap e) = 0 := by
    intro y
    have hfiberEven : ∀ y' : M.CycleSpace, ∀ q : M.Vertex,
        (∑ z : ClassFiber G M classOf q,
          G.boundary (GraphicalActualCutMultigraphSurjective.rawLiftWord
            M edgeMap y'.1) z.1) = 0 := by
      intro y' q
      exact QuotientCycleInternalComponentParity.fiberBoundarySum_eq_zero_of_quotientCycle_crossEdgeCorrespondence
        G M edgeMap hinj classOf hsrc hdst hcoverage y' q
    have hcomponent := internalComponents_are_fibers G M I classOf hI hfiber
    have hEven := rawLiftBoundary_componentEven_of_fiberSums
      G M edgeMap I classOf hcomponent hfiberEven y
    exact rawLift_boundary_repair_of_internalComponentEven
      G M edgeMap I hdisjoint y hEven
  have hrestrict : Function.Surjective
      (GraphicalActualCutMultigraphBridge.restrictCycles G M edgeMap hcycle) :=
    restrictCycles_surjective_of_internalBoundaryRepair
      G M edgeMap hinj hcycle hrepair
  let D : Data G M U V W := {
    edgeMap := edgeMap
    cycleRestriction := hcycle
    surjective := hrestrict
    u := u
    v := v
    w := w
    Uincident := by
      intro e
      change (M.src e = u ∨ M.dst e = u) ↔ edgeMap e ∈ G.cutEdges U
      have hneq : classOf (G.src (edgeMap e)) ≠ classOf (G.dst (edgeMap e)) := by
        intro heq
        apply hloopless e
        calc
          M.src e = classOf (G.src (edgeMap e)) := hsrc e
          _ = classOf (G.dst (edgeMap e)) := heq
          _ = M.dst e := (hdst e).symm
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [hUmem (G.src (edgeMap e)), hUmem (G.dst (edgeMap e)), hsrc e, hdst e]
      exact incident_iff_xor_of_ne _ _ _ hneq
    Ucovered := by
      intro a ha
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      have hneq : classOf (G.src a) ≠ classOf (G.dst a) := by
        rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · intro heq
          exact ht ((hUmem (G.dst a)).mpr
            (heq.symm.trans ((hUmem (G.src a)).mp hs)))
        · intro heq
          exact hs ((hUmem (G.src a)).mpr
            (heq.trans ((hUmem (G.dst a)).mp ht)))
      rcases hcoverage a with ⟨e, he⟩ | he
      · exact ⟨e, he⟩
      · exact False.elim (hneq he)
    Vinc := by
      intro e
      change (M.src e = v ∨ M.dst e = v) ↔ edgeMap e ∈ G.cutEdges V
      have hneq : classOf (G.src (edgeMap e)) ≠ classOf (G.dst (edgeMap e)) := by
        intro heq
        apply hloopless e
        calc
          M.src e = classOf (G.src (edgeMap e)) := hsrc e
          _ = classOf (G.dst (edgeMap e)) := heq
          _ = M.dst e := (hdst e).symm
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [hVmem (G.src (edgeMap e)), hVmem (G.dst (edgeMap e)), hsrc e, hdst e]
      exact incident_iff_xor_of_ne _ _ _ hneq
    Vcovered := by
      intro a ha
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      have hneq : classOf (G.src a) ≠ classOf (G.dst a) := by
        rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · intro heq
          exact ht ((hVmem (G.dst a)).mpr
            (heq.symm.trans ((hVmem (G.src a)).mp hs)))
        · intro heq
          exact hs ((hVmem (G.src a)).mpr
            (heq.trans ((hVmem (G.dst a)).mp ht)))
      rcases hcoverage a with ⟨e, he⟩ | he
      · exact ⟨e, he⟩
      · exact False.elim (hneq he)
    Winc := by
      intro e
      change (M.src e = w ∨ M.dst e = w) ↔ edgeMap e ∈ G.cutEdges W
      have hneq : classOf (G.src (edgeMap e)) ≠ classOf (G.dst (edgeMap e)) := by
        intro heq
        apply hloopless e
        calc
          M.src e = classOf (G.src (edgeMap e)) := hsrc e
          _ = classOf (G.dst (edgeMap e)) := heq
          _ = M.dst e := (hdst e).symm
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [hWmem (G.src (edgeMap e)), hWmem (G.dst (edgeMap e)), hsrc e, hdst e]
      exact incident_iff_xor_of_ne _ _ _ hneq
    Wcovered := by
      intro a ha
      simp only [PhysicalGraph.cutEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha
      have hneq : classOf (G.src a) ≠ classOf (G.dst a) := by
        rcases ha with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · intro heq
          exact ht ((hWmem (G.dst a)).mpr
            (heq.symm.trans ((hWmem (G.src a)).mp hs)))
        · intro heq
          exact hs ((hWmem (G.src a)).mpr
            (heq.trans ((hWmem (G.dst a)).mp ht)))
      rcases hcoverage a with ⟨e, he⟩ | he
      · exact ⟨e, he⟩
      · exact False.elim (hneq he) }
  have hrank : Module.finrank 𝔽 (GraphicalActualCutMultigraphBridge.multiTripleStarSpace M u v w) ≤ 1 :=
    MultigraphSubdivisionTripleStar.multiTripleStarSpace_finrank_le_one M hloopless hconn u v w
      hdist.1 hdist.2.1 hdist.2.2
  refine ⟨D, ?_⟩
  exact actualCutTripleIntersection_finrank_le_one G M U V W D hrank




end Erdos1016.Proof.ThreeRegionCrossingQuotientGeometry

end
