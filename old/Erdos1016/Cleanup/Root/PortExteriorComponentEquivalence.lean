import Erdos1016.Cleanup.Transport.PortExpansionCycleSpace

set_option autoImplicit false

/-!
# Root-port expansion exterior component comparison (scratch)

This file records the tag-separation and endpoint facts needed for the
surjection from auxiliary exterior components to physical exterior
components. The full component-map proof is still in progress.
-/

noncomputable section

namespace Erdos1016.Proof.PortExteriorComponentEquivalence

open Erdos1016
open Erdos1016.Proof.CleanupSpecification
open Erdos1016.Proof.PortExpansion
open Erdos1016.Proof.PortExpansionCycleSpace

theorem oldVertex_not_mem_oldVertexImage_of_not_mem
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (u : M.Vertex) (hu : u ∉ K) :
    oldVertex M S u ∉ oldVertexImage M S h K := by
  intro hv
  rcases Finset.mem_image.mp hv with ⟨v, hvK, huv⟩
  have heq := (vertexEquiv M S).injective huv
  have hval : v = u := Sum.inl.inj heq
  subst v
  exact hu hvK

theorem portVertex_not_mem_oldVertexImage
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    portVertex M S p ∉ oldVertexImage M S h K := by
  intro hv
  rcases Finset.mem_image.mp hv with ⟨v, hvK, huv⟩
  have heq := (vertexEquiv M S).injective huv
  cases heq

theorem loopVertex_not_mem_oldVertexImage
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) (i : Fin 2) :
    loopVertex M S l i ∉ oldVertexImage M S h K := by
  intro hv
  rcases Finset.mem_image.mp hv with ⟨v, hvK, huv⟩
  have heq := (vertexEquiv M S).injective huv
  cases heq



theorem exteriorLoop_base_outside_K
    (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (hKS : K ⊆ S) (l : ExteriorLoop M S) : M.src l.1 ∉ K := by
  intro hK
  exact l.2.2 (hKS hK)

abbrev AuxOutsideGraph (M : FiniteMultiGraph) (K : Finset M.Vertex) :=
  M.toSimpleGraph.induce (↑Kᶜ : Set M.Vertex)

abbrev AuxOutside (M : FiniteMultiGraph) (K : Finset M.Vertex) :=
  {u : M.Vertex // u ∈ (↑Kᶜ : Set M.Vertex)}

abbrev PortOutsideGraph (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) :=
  (graph M S h).toSimpleGraph.induce {v : (graph M S h).Vertex | v ∉ oldVertexImage M S h K}

abbrev PortOutside (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) :=
  {v : (graph M S h).Vertex // v ∉ oldVertexImage M S h K}

/-- Project every physical vertex to an original vertex. For a port midpoint,
choose an endpoint outside K; both vertices of an exterior-loop triangle
project to their common base. -/
noncomputable def baseVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (v : (graph M S h).Vertex) : M.Vertex := by
  classical
  exact match (vertexEquiv M S).symm v with
  | .inl u => u
  | .inr (.inl p) => if M.src p.1 ∈ K then M.dst p.1 else M.src p.1
  | .inr (.inr (l, _)) => M.src l.1

theorem baseVertex_outside_K (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) (v : (graph M S h).Vertex)
    (hv : v ∉ oldVertexImage M S h K) : baseVertex M S K h v ∉ K := by
  classical
  cases ht : (vertexEquiv M S).symm v with
  | inl u =>
      simp only [baseVertex, ht]
      intro hu
      apply hv
      apply Finset.mem_image.mpr
      refine ⟨u, hu, ?_⟩
      have heq := congrArg (vertexEquiv M S) ht.symm
      simpa [oldVertex] using heq
  | inr q =>
      cases q with
      | inl p =>
          by_cases hs : M.src p.1 ∈ K
          · simp only [baseVertex, ht, if_pos hs]
            intro ht
            apply p.2.2
            exact ⟨hKS hs, hKS ht⟩
          · simp only [baseVertex, ht, if_neg hs]
            exact hs
      | inr q =>
          rcases q with ⟨l, i⟩
          simp only [baseVertex, ht]
          exact exteriorLoop_base_outside_K M S K hKS l

@[simp] theorem baseVertex_oldVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (u : M.Vertex) :
    baseVertex M S K h (oldVertex M S u) = u := by
  simp [baseVertex, oldVertex]

@[simp] theorem baseVertex_portVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    baseVertex M S K h (portVertex M S p) =
      if M.src p.1 ∈ K then M.dst p.1 else M.src p.1 := by
  simp [baseVertex, portVertex]

@[simp] theorem baseVertex_loopVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) (i : Fin 2) :
    baseVertex M S K h (loopVertex M S l i) = M.src l.1 := by
  simp [baseVertex, loopVertex]

@[simp] theorem baseVertex_src_internal (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : InternalEdge M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inl e))) = M.src e.1 := by
  rw [src_internalEdge, baseVertex_oldVertex]

@[simp] theorem baseVertex_dst_internal (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (e : InternalEdge M S) :
    baseVertex M S K h ((graph M S h).dst (edgeEquiv M S (.inl e))) = M.dst e.1 := by
  rw [dst_internalEdge, baseVertex_oldVertex]

@[simp] theorem baseVertex_src_port_false (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inr (.inl (p, false))))) =
      M.src p.1 := by
  rw [src_portEdge_false, baseVertex_oldVertex]

@[simp] theorem baseVertex_src_port_true (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inr (.inl (p, true))))) =
      M.dst p.1 := by
  rw [src_portEdge_true, baseVertex_oldVertex]

@[simp] theorem baseVertex_dst_port (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (p : PortEdge M S) (b : Bool) :
    baseVertex M S K h ((graph M S h).dst (edgeEquiv M S (.inr (.inl (p, b))))) =
      if M.src p.1 ∈ K then M.dst p.1 else M.src p.1 := by
  rw [dst_portEdge, baseVertex_portVertex]

@[simp] theorem baseVertex_src_loop_zero (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inr (.inr (l, 0))))) =
      M.src l.1 := by
  rw [src_exteriorLoop_zero, baseVertex_oldVertex]

@[simp] theorem baseVertex_src_loop_one (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inr (.inr (l, 1))))) =
      M.src l.1 := by
  rw [src_exteriorLoop_one, baseVertex_loopVertex]

@[simp] theorem baseVertex_src_loop_two (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).src (edgeEquiv M S (.inr (.inr (l, 2))))) =
      M.src l.1 := by
  rw [src_exteriorLoop_two, baseVertex_loopVertex]

@[simp] theorem baseVertex_dst_loop_zero (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).dst (edgeEquiv M S (.inr (.inr (l, 0))))) =
      M.src l.1 := by
  rw [dst_exteriorLoop_zero, baseVertex_loopVertex]

@[simp] theorem baseVertex_dst_loop_one (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).dst (edgeEquiv M S (.inr (.inr (l, 1))))) =
      M.src l.1 := by
  rw [dst_exteriorLoop_one, baseVertex_loopVertex]

@[simp] theorem baseVertex_dst_loop_two (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (l : ExteriorLoop M S) :
    baseVertex M S K h ((graph M S h).dst (edgeEquiv M S (.inr (.inr (l, 2))))) =
      M.src l.1 := by
  rw [dst_exteriorLoop_two, baseVertex_oldVertex]
  exact l.2.1.symm

private theorem auxAdj_of_edge (M : FiniteMultiGraph) (K : Finset M.Vertex)
    (e : M.Edge) (hs : M.src e ∉ K) (ht : M.dst e ∉ K)
    (hne : M.src e ≠ M.dst e) :
    (AuxOutsideGraph M K).Adj ⟨M.src e, by simpa using hs⟩ ⟨M.dst e, by simpa using ht⟩ := by
  exact ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩



private theorem image_oldVertex_of_mem (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) {u : M.Vertex} (hu : u ∈ K) :
    oldVertex M S u ∈ oldVertexImage M S h K :=
  Finset.mem_image.mpr ⟨u, hu, rfl⟩

private theorem physicalEdge_baseReachable (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) (e : (graph M S h).Edge)
    (hs : (graph M S h).src e ∉ oldVertexImage M S h K)
    (ht : (graph M S h).dst e ∉ oldVertexImage M S h K) :
    (AuxOutsideGraph M K).Reachable
      ⟨baseVertex M S K h ((graph M S h).src e),
        by simpa using baseVertex_outside_K M S K h hKS _ hs⟩
      ⟨baseVertex M S K h ((graph M S h).dst e),
        by simpa using baseVertex_outside_K M S K h hKS _ ht⟩ := by
  classical
  let a : AuxOutside M K := ⟨baseVertex M S K h ((graph M S h).src e),
    by simpa using baseVertex_outside_K M S K h hKS _ hs⟩
  let b : AuxOutside M K := ⟨baseVertex M S K h ((graph M S h).dst e),
    by simpa using baseVertex_outside_K M S K h hKS _ ht⟩
  change (AuxOutsideGraph M K).Reachable a b
  let t := (edgeEquiv M S).symm e
  have het : edgeEquiv M S t = e := Equiv.apply_symm_apply _ _
  cases htg : (edgeEquiv M S).symm e with
  | inl i =>
      have heq : edgeEquiv M S (.inl i) = e := by simpa [t, htg] using het
      have hs' : oldVertex M S (M.src i.1) ∉ oldVertexImage M S h K := by
        simpa [← heq] using hs
      have ht' : oldVertex M S (M.dst i.1) ∉ oldVertexImage M S h K := by
        simpa [← heq] using ht
      have hsrcK : M.src i.1 ∉ K := by
        intro hk
        exact hs' (image_oldVertex_of_mem M S K h hk)
      have hdstK : M.dst i.1 ∉ K := by
        intro hk
        exact ht' (image_oldVertex_of_mem M S K h hk)
      have hneq : M.src i.1 ≠ M.dst i.1 := h.2.1 i.1 i.2.1 i.2.2
      have ha : a = ⟨M.src i.1, by simpa using hsrcK⟩ := by
        apply Subtype.ext
        simp [a, ← heq]
      have hb : b = ⟨M.dst i.1, by simpa using hdstK⟩ := by
        apply Subtype.ext
        simp [b, ← heq]
      rw [ha, hb]
      exact (auxAdj_of_edge M K i.1 hsrcK hdstK hneq).reachable
  | inr q =>
      cases q with
      | inl pside =>
          rcases pside with ⟨p, side⟩
          cases side with
          | false =>
              have heq : edgeEquiv M S (.inr (.inl (p, false))) = e := by
                simpa [t, htg] using het
              have hs' : oldVertex M S (M.src p.1) ∉ oldVertexImage M S h K := by
                simpa [← heq] using hs
              have hsrcK : M.src p.1 ∉ K := by
                intro hk
                exact hs' (image_oldVertex_of_mem M S K h hk)
              have ha : a = ⟨M.src p.1, by simpa using hsrcK⟩ := by
                apply Subtype.ext
                simp [a, ← heq]
              have hb : b = ⟨M.src p.1, by simpa using hsrcK⟩ := by
                apply Subtype.ext
                simp [b, ← heq, hsrcK]
              rw [ha, hb]
          | true =>
              have heq : edgeEquiv M S (.inr (.inl (p, true))) = e := by
                simpa [t, htg] using het
              have hs' : oldVertex M S (M.dst p.1) ∉ oldVertexImage M S h K := by
                simpa [← heq] using hs
              have hdstK : M.dst p.1 ∉ K := by
                intro hk
                exact hs' (image_oldVertex_of_mem M S K h hk)
              by_cases hsrcK : M.src p.1 ∈ K
              · have ha : a = ⟨M.dst p.1, by simpa using hdstK⟩ := by
                  apply Subtype.ext
                  simp [a, ← heq]
                have hb : b = ⟨M.dst p.1, by simpa using hdstK⟩ := by
                  apply Subtype.ext
                  simp [b, ← heq, hsrcK]
                rw [ha, hb]
              · have ha : a = ⟨M.dst p.1, by simpa using hdstK⟩ := by
                  apply Subtype.ext
                  simp [a, ← heq]
                have hb : b = ⟨M.src p.1, by simpa using hsrcK⟩ := by
                  apply Subtype.ext
                  simp [b, ← heq, hsrcK]
                rw [ha, hb]
                exact (auxAdj_of_edge M K p.1 hsrcK hdstK p.2.1).symm.reachable
      | inr q =>
          rcases q with ⟨l, i⟩
          fin_cases i
          · have heq : edgeEquiv M S (.inr (.inr (l, 0))) = e := by simpa [t, htg] using het
            have hout := exteriorLoop_base_outside_K M S K hKS l
            have ha : a = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [a, ← heq]
            have hb : b = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [b, ← heq]
            rw [ha, hb]
          · have heq : edgeEquiv M S (.inr (.inr (l, 1))) = e := by simpa [t, htg] using het
            have hout := exteriorLoop_base_outside_K M S K hKS l
            have ha : a = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [a, ← heq]
            have hb : b = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [b, ← heq]
            rw [ha, hb]
          · have heq : edgeEquiv M S (.inr (.inr (l, 2))) = e := by simpa [t, htg] using het
            have hout := exteriorLoop_base_outside_K M S K hKS l
            have ha : a = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [a, ← heq]
            have hb : b = ⟨M.src l.1, by simpa using hout⟩ := by apply Subtype.ext; simp [b, ← heq, l.2.1]
            rw [ha, hb]

noncomputable def outsideBaseVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (v : PortOutside M S K h) : AuxOutside M K :=
  ⟨baseVertex M S K h v.1,
    by simpa using baseVertex_outside_K M S K h hKS v.1 (by simpa using v.2)⟩

noncomputable def outsideOldVertex (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (u : AuxOutside M K) : PortOutside M S K h :=
  ⟨oldVertex M S u.1,
    oldVertex_not_mem_oldVertexImage_of_not_mem M S K h u.1 (by simpa using u.2)⟩

@[simp] theorem outsideBaseVertex_outsideOldVertex (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (u : AuxOutside M K) :
    outsideBaseVertex M S K h hKS (outsideOldVertex M S K h u) = u := by
  apply Subtype.ext
  simp [outsideBaseVertex, outsideOldVertex]

private theorem auxAdj_oldVertices_reachable_forward (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    {u v : AuxOutside M K} (e : M.Edge)
    (hdir : M.src e = u.1 ∧ M.dst e = v.1)
    (hne : u.1 ≠ v.1) :
    (PortOutsideGraph M S K h).Reachable
      (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) := by
  classical
  by_cases hbothS : M.src e ∈ S ∧ M.dst e ∈ S
  · let ie : InternalEdge M S := ⟨e, hbothS.1, hbothS.2⟩
    have hadj : (PortOutsideGraph M S K h).Adj
        (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) := by
      change (graph M S h).toSimpleGraph.Adj (oldVertex M S u.1) (oldVertex M S v.1)
      refine ⟨edgeEquiv M S (.inl ie), by simp [PhysicalGraph.toSimpleGraph,
        PhysicalGraph.selectedGraph], Or.inl ⟨?_, ?_⟩⟩
      · calc
          (graph M S h).src (edgeEquiv M S (.inl ie)) = oldVertex M S (M.src e) := src_internalEdge M S h ie
          _ = oldVertex M S u.1 := congrArg (oldVertex M S) hdir.1
      · calc
          (graph M S h).dst (edgeEquiv M S (.inl ie)) = oldVertex M S (M.dst e) := dst_internalEdge M S h ie
          _ = oldVertex M S v.1 := congrArg (oldVertex M S) hdir.2
    exact hadj.reachable
  · have hneq : M.src e ≠ M.dst e := by
      intro heq
      apply hne
      exact hdir.1.symm.trans (heq.trans hdir.2)
    have hnotboth : ¬ (M.src e ∈ S ∧ M.dst e ∈ S) := hbothS
    let p : PortEdge M S := ⟨e, hneq, hnotboth⟩
    have hpout : portVertex M S p ∉ oldVertexImage M S h K :=
      portVertex_not_mem_oldVertexImage M S K h p
    have h1 : (PortOutsideGraph M S K h).Adj
        (outsideOldVertex M S K h u) ⟨portVertex M S p, hpout⟩ := by
      change (graph M S h).toSimpleGraph.Adj (oldVertex M S u.1) (portVertex M S p)
      refine ⟨edgeEquiv M S (.inr (.inl (p, false))), by simp [PhysicalGraph.toSimpleGraph,
        PhysicalGraph.selectedGraph], Or.inl ⟨?_, ?_⟩⟩
      · calc
          (graph M S h).src (edgeEquiv M S (.inr (.inl (p, false)))) = oldVertex M S (M.src e) := src_portEdge_false M S h p
          _ = oldVertex M S u.1 := congrArg (oldVertex M S) hdir.1
      · exact dst_portEdge M S h p false
    have h2 : (PortOutsideGraph M S K h).Adj
        (outsideOldVertex M S K h v) ⟨portVertex M S p, hpout⟩ := by
      change (graph M S h).toSimpleGraph.Adj (oldVertex M S v.1) (portVertex M S p)
      refine ⟨edgeEquiv M S (.inr (.inl (p, true))), by simp [PhysicalGraph.toSimpleGraph,
        PhysicalGraph.selectedGraph], Or.inl ⟨?_, ?_⟩⟩
      · calc
          (graph M S h).src (edgeEquiv M S (.inr (.inl (p, true)))) = oldVertex M S (M.dst e) := src_portEdge_true M S h p
          _ = oldVertex M S v.1 := congrArg (oldVertex M S) hdir.2
      · exact dst_portEdge M S h p true
    exact h1.reachable.trans h2.reachable.symm

private theorem auxAdj_oldVertices_reachable (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    {u v : AuxOutside M K} (hadj : (AuxOutsideGraph M K).Adj u v) :
    (PortOutsideGraph M S K h).Reachable
      (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) := by
  rcases hadj with ⟨hne, e, hdir | hdir⟩
  · exact auxAdj_oldVertices_reachable_forward M S K h hKS e hdir hne
  · exact (auxAdj_oldVertices_reachable_forward M S K h hKS
      (u := v) (v := u) e hdir hne.symm).symm

private theorem outsideAdj_baseReachable (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    {u v : PortOutside M S K h}
    (hadj : (PortOutsideGraph M S K h).Adj u v) :
    (AuxOutsideGraph M K).Reachable
      (outsideBaseVertex M S K h hKS u) (outsideBaseVertex M S K h hKS v) := by
  change ((graph M S h).toSimpleGraph).Adj u.1 v.1 at hadj
  simp only [PhysicalGraph.toSimpleGraph, PhysicalGraph.selectedGraph] at hadj
  rcases hadj with ⟨e, _, hend | hend⟩
  · have hroute := physicalEdge_baseReachable M S K h hKS e
      (by simpa [hend.1] using u.2) (by simpa [hend.2] using v.2)
    have hu : outsideBaseVertex M S K h hKS ⟨(graph M S h).src e,
        by simpa [hend.1] using u.2⟩ = outsideBaseVertex M S K h hKS u := by
      apply Subtype.ext
      simp [outsideBaseVertex, hend.1]
    have hv : outsideBaseVertex M S K h hKS ⟨(graph M S h).dst e,
        by simpa [hend.2] using v.2⟩ = outsideBaseVertex M S K h hKS v := by
      apply Subtype.ext
      simp [outsideBaseVertex, hend.2]
    rw [← hu, ← hv]
    exact hroute
  · have hroute := physicalEdge_baseReachable M S K h hKS e
      (by simpa [hend.1] using v.2) (by simpa [hend.2] using u.2)
    have hv : outsideBaseVertex M S K h hKS ⟨(graph M S h).src e,
        by simpa [hend.1] using v.2⟩ = outsideBaseVertex M S K h hKS v := by
      apply Subtype.ext
      simp [outsideBaseVertex, hend.1]
    have hu : outsideBaseVertex M S K h hKS ⟨(graph M S h).dst e,
        by simpa [hend.2] using u.2⟩ = outsideBaseVertex M S K h hKS u := by
      apply Subtype.ext
      simp [outsideBaseVertex, hend.2]
    rw [← hu, ← hv]
    exact hroute.symm

private theorem physicalVertex_reachable_base (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (v : PortOutside M S K h) :
    (PortOutsideGraph M S K h).Reachable v
      (outsideOldVertex M S K h (outsideBaseVertex M S K h hKS v)) := by
  classical
  cases htag : (vertexEquiv M S).symm v.1 with
  | inl u =>
      have hv : v.1 = oldVertex M S u := by
        have hh := congrArg (vertexEquiv M S) htag.symm
        simpa [oldVertex] using hh.symm
      let ub := outsideBaseVertex M S K h hKS v
      have hbase : ub.1 = u := by
        change baseVertex M S K h v.1 = u
        rw [hv]
        exact baseVertex_oldVertex M S K h u
      have hEq : v = outsideOldVertex M S K h ub := by
        apply Subtype.ext
        change v.1 = oldVertex M S ub.1
        rw [hbase]
        exact hv
      rw [hEq]
      simpa only [outsideBaseVertex_outsideOldVertex] using SimpleGraph.Reachable.refl _
  | inr q =>
      cases q with
      | inl p =>
          have hv : v.1 = portVertex M S p := by
            have hh := congrArg (vertexEquiv M S) htag.symm
            simpa [portVertex] using hh.symm
          have hpout := portVertex_not_mem_oldVertexImage M S K h p
          by_cases hsrcK : M.src p.1 ∈ K
          · have hdstK : M.dst p.1 ∉ K := by
              intro hk
              exact p.2.2 ⟨hKS hsrcK, hKS hk⟩
            let u : AuxOutside M K := ⟨M.dst p.1, by simpa using hdstK⟩
            have hadj : (PortOutsideGraph M S K h).Adj
                (outsideOldVertex M S K h u) ⟨portVertex M S p, hpout⟩ := by
              change (graph M S h).toSimpleGraph.Adj (oldVertex M S (M.dst p.1))
                (portVertex M S p)
              refine ⟨edgeEquiv M S (.inr (.inl (p, true))), by simp [PhysicalGraph.toSimpleGraph,
                PhysicalGraph.selectedGraph], Or.inl ⟨src_portEdge_true M S h p, dst_portEdge M S h p true⟩⟩
            have hvEq : v = ⟨portVertex M S p, hpout⟩ := Subtype.ext hv
            rw [hvEq]
            simpa [outsideBaseVertex, baseVertex_portVertex, hsrcK] using hadj.reachable.symm
          · let u : AuxOutside M K := ⟨M.src p.1, by simpa using hsrcK⟩
            have hadj : (PortOutsideGraph M S K h).Adj
                (outsideOldVertex M S K h u) ⟨portVertex M S p, hpout⟩ := by
              change (graph M S h).toSimpleGraph.Adj (oldVertex M S (M.src p.1))
                (portVertex M S p)
              refine ⟨edgeEquiv M S (.inr (.inl (p, false))), by simp [PhysicalGraph.toSimpleGraph,
                PhysicalGraph.selectedGraph], Or.inl ⟨src_portEdge_false M S h p, dst_portEdge M S h p false⟩⟩
            have hvEq : v = ⟨portVertex M S p, hpout⟩ := Subtype.ext hv
            rw [hvEq]
            simpa [outsideBaseVertex, baseVertex_portVertex, hsrcK] using hadj.reachable.symm
      | inr q =>
          rcases q with ⟨l, i⟩
          have hv0 : v.1 = loopVertex M S l i := by
            have hh := congrArg (vertexEquiv M S) htag.symm
            simpa [loopVertex] using hh.symm
          have hout := exteriorLoop_base_outside_K M S K hKS l
          let u : AuxOutside M K := ⟨M.src l.1, by simpa using hout⟩
          have holdout : oldVertex M S (M.src l.1) ∉ oldVertexImage M S h K :=
            oldVertex_not_mem_oldVertexImage_of_not_mem M S K h _ hout
          let old : PortOutside M S K h := ⟨oldVertex M S (M.src l.1), holdout⟩
          let loop0 : PortOutside M S K h :=
            ⟨loopVertex M S l 0, loopVertex_not_mem_oldVertexImage M S K h l 0⟩
          let loop1 : PortOutside M S K h :=
            ⟨loopVertex M S l 1, loopVertex_not_mem_oldVertexImage M S K h l 1⟩
          have hadj0 : (PortOutsideGraph M S K h).Adj old loop0 := by
            change (graph M S h).toSimpleGraph.Adj old.1 loop0.1
            refine ⟨edgeEquiv M S (.inr (.inr (l, 0))), by simp [PhysicalGraph.toSimpleGraph,
              PhysicalGraph.selectedGraph], Or.inl ⟨src_exteriorLoop_zero M S h l,
              dst_exteriorLoop_zero M S h l⟩⟩
          have hadj1 : (PortOutsideGraph M S K h).Adj loop0 loop1 := by
            change (graph M S h).toSimpleGraph.Adj loop0.1 loop1.1
            refine ⟨edgeEquiv M S (.inr (.inr (l, 1))), by simp [PhysicalGraph.toSimpleGraph,
              PhysicalGraph.selectedGraph], Or.inl ⟨src_exteriorLoop_one M S h l,
              dst_exteriorLoop_one M S h l⟩⟩
          fin_cases i
          · have hvEq : v = loop0 := by apply Subtype.ext; exact hv0
            have oldEq : old = outsideOldVertex M S K h u := by
              apply Subtype.ext
              rfl
            rw [hvEq]
            simpa [outsideBaseVertex, baseVertex_loopVertex, loop0, u] using hadj0.reachable.symm
          · have hvEq : v = loop1 := by apply Subtype.ext; exact hv0
            have oldEq : old = outsideOldVertex M S K h u := by
              apply Subtype.ext
              rfl
            rw [hvEq]
            simpa [outsideBaseVertex, baseVertex_loopVertex, loop0, loop1, u] using
              hadj1.reachable.symm.trans hadj0.reachable.symm

private theorem portReachable_baseReachable (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    {u v : PortOutside M S K h}
    (p : (PortOutsideGraph M S K h).Reachable u v) :
    (AuxOutsideGraph M K).Reachable
      (outsideBaseVertex M S K h hKS u) (outsideBaseVertex M S K h hKS v) := by
  have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).1 p
  have hmapped : Relation.ReflTransGen (AuxOutsideGraph M K).Adj
      (outsideBaseVertex M S K h hKS u) (outsideBaseVertex M S K h hKS v) := by
    induction hrel with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hadj ih =>
        exact (ih ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hprev)).trans
          ((SimpleGraph.reachable_iff_reflTransGen _ _).1
            (outsideAdj_baseReachable M S K h hKS hadj))
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).2 hmapped

private theorem auxReachable_portReachable (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    {u v : AuxOutside M K} (p : (AuxOutsideGraph M K).Reachable u v) :
    (PortOutsideGraph M S K h).Reachable
      (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) := by
  have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).1 p
  have hmapped : Relation.ReflTransGen (PortOutsideGraph M S K h).Adj
      (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) := by
    induction hrel with
    | refl => exact Relation.ReflTransGen.refl
    | tail hprev hadj ih =>
        exact (ih ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hprev)).trans
          ((SimpleGraph.reachable_iff_reflTransGen _ _).1
            (auxAdj_oldVertices_reachable M S K h hKS hadj))
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).2 hmapped

theorem outsideOldVertex_reachable_iff_auxReachable (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S)
    (u v : AuxOutside M K) :
    (PortOutsideGraph M S K h).Reachable
      (outsideOldVertex M S K h u) (outsideOldVertex M S K h v) ↔
    (AuxOutsideGraph M K).Reachable u v := by
  constructor
  · intro hphys
    have hmapped := portReachable_baseReachable M S K h hKS hphys
    simpa only [outsideBaseVertex_outsideOldVertex] using hmapped
  · intro haux
    exact auxReachable_portReachable M S K h hKS haux

noncomputable def exteriorComponentMap (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    (AuxOutsideGraph M K).ConnectedComponent → (PortOutsideGraph M S K h).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.lift
    (fun u => (PortOutsideGraph M S K h).connectedComponentMk (outsideOldVertex M S K h u))
    (by
      intro u v p _
      exact SimpleGraph.ConnectedComponent.sound
        (auxReachable_portReachable M S K h hKS p.reachable))

@[simp] theorem exteriorComponentMap_mk (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) (u : AuxOutside M K) :
    exteriorComponentMap M S K h hKS ((AuxOutsideGraph M K).connectedComponentMk u) =
      (PortOutsideGraph M S K h).connectedComponentMk (outsideOldVertex M S K h u) := by
  simp [exteriorComponentMap]

theorem exteriorComponentMap_bijective (M : FiniteMultiGraph) (S K : Finset M.Vertex)
    (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    Function.Bijective (exteriorComponentMap M S K h hKS) := by
  constructor
  · intro c d hcd
    let u : AuxOutside M K := c.out
    let v : AuxOutside M K := d.out
    have hcu : (AuxOutsideGraph M K).connectedComponentMk u = c := Quot.out_eq c
    have hdv : (AuxOutsideGraph M K).connectedComponentMk v = d := Quot.out_eq d
    have hphysical :
        (PortOutsideGraph M S K h).connectedComponentMk (outsideOldVertex M S K h u) =
        (PortOutsideGraph M S K h).connectedComponentMk (outsideOldVertex M S K h v) := by
      rw [← hcu, ← hdv, exteriorComponentMap_mk] at hcd
      exact hcd
    have hreach := SimpleGraph.ConnectedComponent.exact hphysical
    have haux := (outsideOldVertex_reachable_iff_auxReachable M S K h hKS u v).1 hreach
    have hauxEq := SimpleGraph.ConnectedComponent.sound haux
    exact hcu.symm.trans (hauxEq.trans hdv)
  · intro c
    let v : PortOutside M S K h := c.out
    have hcv : (PortOutsideGraph M S K h).connectedComponentMk v = c := Quot.out_eq c
    refine ⟨(AuxOutsideGraph M K).connectedComponentMk (outsideBaseVertex M S K h hKS v), ?_⟩
    rw [exteriorComponentMap_mk]
    have hreach := physicalVertex_reachable_base M S K h hKS v
    have hsame := SimpleGraph.ConnectedComponent.sound hreach.symm
    exact hsame.trans hcv

theorem portExpansion_exteriorComponentCount_eq (M : FiniteMultiGraph)
    (S K : Finset M.Vertex) (h : IsCleanupRoot M S) (hKS : K ⊆ S) :
    Fintype.card (SimpleGraph.ConnectedComponent (PortOutsideGraph M S K h)) =
      exteriorComponentCount M K := by
  classical
  letI : Fintype (SimpleGraph.ConnectedComponent (PortOutsideGraph M S K h)) :=
    SetLike.instFintype
  letI : Fintype (SimpleGraph.ConnectedComponent (AuxOutsideGraph M K)) :=
    (AuxOutsideGraph M K).instFintypeConnectedComponent
  have hcard := Fintype.card_congr
    (Equiv.ofBijective (exteriorComponentMap M S K h hKS)
      (exteriorComponentMap_bijective M S K h hKS))
  rw [← hcard]
  simp [exteriorComponentCount, AuxOutsideGraph]

end Erdos1016.Proof.PortExteriorComponentEquivalence

end
