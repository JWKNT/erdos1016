import Erdos1016.Graph.RankNormalization
import Erdos1016.Boundary.NetworkRealization

set_option autoImplicit false

/-!
# Connecting a finite physical graph by one hub

The construction adds one fresh hub and a single bridge from it to a chosen
representative of every connected component. The representatives are the
quotient representatives `Quot.out`; no arbitrary choice of graph data is
left as an assumption.
-/

noncomputable section

namespace Erdos1016.PhysicalGraph

open Erdos1016.BoundaryTrace
open Erdos1016.BoundaryDecay

local instance hubDecidableProp (p : Prop) : Decidable p := Classical.propDecidable p

abbrev HubComponent (G : PhysicalGraph) := G.toSimpleGraph.ConnectedComponent

noncomputable instance hubComponentFintype (G : PhysicalGraph) :
    Fintype (HubComponent G) := Fintype.ofFinite _

/-- Network formed by retaining all old edges and adding one hub bridge per
old connected component. -/
def hubNetwork (G : PhysicalGraph) : Network (G.Vertex ⊕ Unit) (G.Edge ⊕ HubComponent G) where
  src
    | Sum.inl e => Sum.inl (G.src e)
    | Sum.inr c => Sum.inl (Quot.out c)
  dst
    | Sum.inl e => Sum.inl (G.dst e)
    | Sum.inr _ => Sum.inr ()
  noLoops := by
    intro e
    cases e with
    | inl e => exact fun h => G.noLoops e (Sum.inl.inj h)
    | inr c => intro h; exact Sum.inl_ne_inr h

/-- The hub network is simple when the original physical graph is simple. -/
theorem hubNetwork_simple (G : PhysicalGraph) :
    Erdos1016.BoundaryDecay.SimpleNetwork (hubNetwork G) := by
  intro e f h
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [hubNetwork, Sum.inl.injEq, Sum.inr.injEq] at h ⊢
      exact G.simple e f h
    | inr c =>
      simp [hubNetwork] at h
  | inr c =>
    cases f with
    | inl f =>
      simp [hubNetwork] at h
    | inr d =>
      simp only [hubNetwork, Sum.inl.injEq, Sum.inr.injEq] at h ⊢
      have hr : Quot.out c = Quot.out d := by
        rcases h with h | h
        · exact h.1
        · simp at h
      have hc : c = d := by
        calc
          c = G.toSimpleGraph.connectedComponentMk (Quot.out c) :=
            (Quot.out_eq c).symm
          _ = G.toSimpleGraph.connectedComponentMk (Quot.out d) := by rw [hr]
          _ = d := Quot.out_eq d
      exact hc

/-- The finite physical graph obtained by relabelling the hub network. -/
noncomputable def connectByHub (G : PhysicalGraph) : PhysicalGraph :=
  Erdos1016.BoundaryDecay.physicalize (hubNetwork G) (hubNetwork_simple G)

private def hubNetwork_oldHom (G : PhysicalGraph) :
    G.toSimpleGraph →g (hubNetwork G).graph where
  toFun := Sum.inl
  map_rel' := by
    intro u v huv
    rcases huv with ⟨e, _, h⟩
    refine ⟨Sum.inl e, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩
    · exact Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩

private theorem hubNetwork_vertex_reachable_hub (G : PhysicalGraph)
    (v : G.Vertex) : (hubNetwork G).graph.Reachable (Sum.inl v) (Sum.inr ()) := by
  let c : HubComponent G := G.toSimpleGraph.connectedComponentMk v
  let root : G.Vertex := Quot.out c
  have hc : G.toSimpleGraph.connectedComponentMk root = c := Quot.out_eq c
  have hreach : G.toSimpleGraph.Reachable v root := by
    apply SimpleGraph.ConnectedComponent.exact
    simpa [c, root] using hc.symm
  have hmap : (hubNetwork G).graph.Reachable (Sum.inl v) (Sum.inl root) :=
    by simpa [hubNetwork_oldHom] using hreach.map (hubNetwork_oldHom G)
  have hadj : (hubNetwork G).graph.Adj (Sum.inl root) (Sum.inr ()) := by
    refine ⟨Sum.inr c, ?_⟩
    exact Or.inl ⟨rfl, rfl⟩
  exact hmap.trans ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩

/-- The hub network is connected, including the zero-vertex input (then its
vertex type consists only of the hub). -/
theorem hubNetwork_connected (G : PhysicalGraph) :
    (hubNetwork G).graph.Connected := by
  classical
  letI : Nonempty (G.Vertex ⊕ Unit) := ⟨Sum.inr ()⟩
  refine ⟨?_⟩
  intro x y
  cases x with
  | inr _ =>
    cases y with
    | inr _ => exact ⟨SimpleGraph.Walk.nil⟩
    | inl v => exact (hubNetwork_vertex_reachable_hub G v).symm
  | inl u =>
    cases y with
    | inr _ => exact hubNetwork_vertex_reachable_hub G u
    | inl v =>
      exact (hubNetwork_vertex_reachable_hub G u).trans
        (hubNetwork_vertex_reachable_hub G v).symm

theorem connectByHub_connected (G : PhysicalGraph) :
    (connectByHub G).IsConnected := by
  change (connectByHub G).toSimpleGraph.Connected
  have h := (Erdos1016.BoundaryDecay.physicalReindex (hubNetwork G) (hubNetwork_simple G)).connected_iff.mp
    (hubNetwork_connected G)
  simpa [connectByHub, PhysicalGraph.traceNetwork_graph] using h

/-- The construction adds one vertex and one bridge per original component. -/
@[simp] theorem connectByHub_vertexCount (G : PhysicalGraph) :
    (connectByHub G).vertexCount = G.vertexCount + 1 := by
  simp [connectByHub, Erdos1016.BoundaryDecay.physicalize, hubNetwork]

@[simp] theorem connectByHub_edgeCount (G : PhysicalGraph) :
    (connectByHub G).edgeCount = G.edgeCount + Fintype.card (HubComponent G) := by
  simp [connectByHub, Erdos1016.BoundaryDecay.physicalize, hubNetwork]

/-- Adding the hub bridges preserves cycle rank. -/
theorem cycleRank_connectByHub (G : PhysicalGraph) :
    (connectByHub G).cycleRank = G.cycleRank := by
  have hG := cycleRank_euler_components G
  have hH := cycleRank_euler_components (connectByHub G)
  have hconn := connectByHub_connected G
  have hconnTrace : (connectByHub G).traceNetwork.graph.Connected := by
    simpa only [PhysicalGraph.traceNetwork_graph] using hconn
  have hcomp : Fintype.card (connectByHub G).traceNetwork.Component = 1 :=
    Erdos1016.BoundaryDecay.connected_component_card (connectByHub G).traceNetwork hconnTrace
  have hH' : (connectByHub G).cycleRank + (G.vertexCount + 1) =
      (G.edgeCount + Fintype.card (HubComponent G)) + 1 := by
    simpa [connectByHub_vertexCount, connectByHub_edgeCount, hcomp] using hH
  have hC : Fintype.card (HubComponent G) =
      Fintype.card G.traceNetwork.Component := by
    let eTrace : G.traceNetwork.Component ≃ HubComponent G :=
      Equiv.cast (congrArg (fun Q : SimpleGraph G.Vertex => Q.ConnectedComponent)
        (PhysicalGraph.traceNetwork_graph G))
    exact (Fintype.card_congr eTrace).symm
  rw [hC] at hH'
  omega


private def hubVertexMap (G : PhysicalGraph) :
    G.Vertex → (connectByHub G).Vertex := fun v =>
  Fintype.equivFin (G.Vertex ⊕ Unit) (Sum.inl v)

def hubOldEdgeEmbedding (G : PhysicalGraph) :
    G.Edge → (connectByHub G).Edge := fun e =>
  Fintype.equivFin (G.Edge ⊕ HubComponent G) (Sum.inl e)

private def liftHubWord (G : PhysicalGraph) (x : G.Word) :
    (connectByHub G).Word := by
  classical
  intro e
  match (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
  | Sum.inl f => exact x f
  | Sum.inr _ => exact 0

/-- The spoke-edge labels in the hub network, relabelled as physical edges. -/
def hubSpokeEmbedding (G : PhysicalGraph) :
    HubComponent G → (connectByHub G).Edge := fun c =>
  Fintype.equivFin (G.Edge ⊕ HubComponent G) (Sum.inr c)

@[simp] private theorem connectByHub_src_old (G : PhysicalGraph) (e : G.Edge) :
    (connectByHub G).src (hubOldEdgeEmbedding G e) = hubVertexMap G (G.src e) := by
  simp [connectByHub, hubOldEdgeEmbedding, hubVertexMap,
    Erdos1016.BoundaryDecay.physicalize, hubNetwork]

@[simp] private theorem connectByHub_dst_old (G : PhysicalGraph) (e : G.Edge) :
    (connectByHub G).dst (hubOldEdgeEmbedding G e) = hubVertexMap G (G.dst e) := by
  simp [connectByHub, hubOldEdgeEmbedding, hubVertexMap,
    Erdos1016.BoundaryDecay.physicalize, hubNetwork]

@[simp] private theorem liftHubWord_edge (G : PhysicalGraph) (x : G.Word)
    (e : G.Edge) : liftHubWord G x (hubOldEdgeEmbedding G e) = x e := by
  simp [liftHubWord, hubOldEdgeEmbedding]



private theorem hubVertexMap_injective (G : PhysicalGraph) :
    Function.Injective (hubVertexMap G) := by
  intro u v h
  apply Sum.inl.inj
  exact (Fintype.equivFin (G.Vertex ⊕ Unit)).injective h

private theorem hubOldEdgeEmbedding_injective (G : PhysicalGraph) :
    Function.Injective (hubOldEdgeEmbedding G) := by
  intro e f h
  apply Sum.inl.inj
  exact (Fintype.equivFin (G.Edge ⊕ HubComponent G)).injective h





theorem liftHubWord_usedVertices (G : PhysicalGraph) (x : G.Word) :
    (connectByHub G).usedVertices (liftHubWord G x) =
      (G.usedVertices x).image (hubVertexMap G) := by
  classical
  ext w
  simp only [PhysicalGraph.usedVertices, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hinc⟩
    cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
    | inl f =>
      have hedge : e = hubOldEdgeEmbedding G f := by
        dsimp [hubOldEdgeEmbedding]
        rw [← hdec]
        exact (Fintype.equivFin (G.Edge ⊕ HubComponent G)).apply_symm_apply e |>.symm
      subst e
      change (connectByHub G).src (hubOldEdgeEmbedding G f) = w ∨
        (connectByHub G).dst (hubOldEdgeEmbedding G f) = w at hinc
      rw [connectByHub_src_old, connectByHub_dst_old] at hinc
      rcases hinc with hinc | hinc
      · refine ⟨G.src f, ⟨f, ?_, Or.inl rfl⟩, hinc⟩
        simpa using he
      · refine ⟨G.dst f, ⟨f, ?_, Or.inr rfl⟩, hinc⟩
        simpa using he
    | inr c =>
      have hz : liftHubWord G x e = 0 := by simp [liftHubWord, hdec]
      exact (he hz).elim
  · rintro ⟨v, ⟨e, he, hinc⟩, rfl⟩
    refine ⟨hubOldEdgeEmbedding G e, ?_, ?_⟩
    · simpa using he
    · rcases hinc with hinc | hinc
      · exact Or.inl ((connectByHub_src_old G e).trans (congrArg (hubVertexMap G) hinc))
      · exact Or.inr ((connectByHub_dst_old G e).trans (congrArg (hubVertexMap G) hinc))

private theorem selectedIncidenceFinset_eq (G : PhysicalGraph) (x : G.Word)
    (v : G.Vertex) :
    (Finset.univ.filter (fun e : (connectByHub G).Edge =>
      liftHubWord G x e ≠ 0 ∧ (connectByHub G).incident e (hubVertexMap G v))) =
      (Finset.univ.filter (fun e : G.Edge => x e ≠ 0 ∧ G.incident e v)).image
        (hubOldEdgeEmbedding G) := by
  classical
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨he, hinc⟩
    cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
    | inl f =>
      have hedge : e = hubOldEdgeEmbedding G f := by
        dsimp [hubOldEdgeEmbedding]
        rw [← hdec]
        exact (Fintype.equivFin (G.Edge ⊕ HubComponent G)).apply_symm_apply e |>.symm
      subst e
      change (connectByHub G).src (hubOldEdgeEmbedding G f) = hubVertexMap G v ∨
        (connectByHub G).dst (hubOldEdgeEmbedding G f) = hubVertexMap G v at hinc
      rw [connectByHub_src_old, connectByHub_dst_old] at hinc
      rcases hinc with hinc | hinc
      · refine ⟨f, ⟨?_, Or.inl ?_⟩, rfl⟩
        · simpa using he
        · exact hubVertexMap_injective G hinc
      · refine ⟨f, ⟨?_, Or.inr ?_⟩, rfl⟩
        · simpa using he
        · exact hubVertexMap_injective G hinc
    | inr c =>
      have hz : liftHubWord G x e = 0 := by simp [liftHubWord, hdec]
      exact (he hz).elim
  · rintro ⟨f, ⟨he, hinc⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa using he
    · change (connectByHub G).src (hubOldEdgeEmbedding G f) = hubVertexMap G v ∨
        (connectByHub G).dst (hubOldEdgeEmbedding G f) = hubVertexMap G v
      rw [connectByHub_src_old, connectByHub_dst_old]
      rcases hinc with hinc | hinc
      · exact Or.inl (congrArg (hubVertexMap G) hinc)
      · exact Or.inr (congrArg (hubVertexMap G) hinc)

theorem selectedDegree_lift_eq (G : PhysicalGraph) (x : G.Word)
    (v : G.Vertex) :
    (connectByHub G).selectedDegree (liftHubWord G x) (hubVertexMap G v) =
      G.selectedDegree x v := by
  unfold PhysicalGraph.selectedDegree
  rw [selectedIncidenceFinset_eq]
  exact Finset.card_image_of_injective _ (hubOldEdgeEmbedding_injective G)

private def liftHubNetworkWord (G : PhysicalGraph) (x : G.Word) :
    (hubNetwork G).Word := fun e => match e with
      | Sum.inl f => x f
      | Sum.inr _ => 0

private theorem liftHubNetwork_boundary_old (G : PhysicalGraph) (x : G.Word)
    (v : G.Vertex) :
    (hubNetwork G).boundary (liftHubNetworkWord G x) (Sum.inl v) =
      G.traceNetwork.boundary x v := by
  classical
  rw [BoundaryTrace.Network.boundary_apply, G.traceNetwork_boundary,
    PhysicalGraph.boundary]
  simp_rw [Fintype.sum_sum_type]
  simp [hubNetwork, liftHubNetworkWord, Finset.sum_add_distrib, add_comm]

private theorem liftHubNetwork_boundary_hub (G : PhysicalGraph) (x : G.Word) :
    (hubNetwork G).boundary (liftHubNetworkWord G x) (Sum.inr ()) = 0 := by
  classical
  rw [BoundaryTrace.Network.boundary_apply]
  simp_rw [Fintype.sum_sum_type]
  simp [liftHubNetworkWord, hubNetwork]

private theorem liftHubNetwork_cycle (G : PhysicalGraph) (x : G.CycleSpace) :
    liftHubNetworkWord G x.1 ∈ (hubNetwork G).CycleSpace := by
  apply LinearMap.mem_ker.mpr
  funext w
  cases w with
  | inl v =>
    rw [liftHubNetwork_boundary_old, G.traceNetwork_boundary]
    exact congrFun (LinearMap.mem_ker.mp x.2) v
  | inr u => cases u; exact liftHubNetwork_boundary_hub G x.1

private theorem liftHubWord_cycleSpace (G : PhysicalGraph) (x : G.CycleSpace) :
    liftHubWord G x.1 ∈ (connectByHub G).CycleSpace := by
  let y : (hubNetwork G).CycleSpace :=
    ⟨liftHubNetworkWord G x.1, liftHubNetwork_cycle G x⟩
  let z := Erdos1016.BoundaryDecay.physicalCycleEquiv
    (hubNetwork G) (hubNetwork_simple G) y
  have hz : z.1 = liftHubWord G x.1 := by
    funext e
    change (liftHubNetworkWord G x.1)
        ((Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e) =
      liftHubWord G x.1 e
    simp [liftHubNetworkWord, liftHubWord]
  rw [← hz]
  exact z.2

/-- The old cycle space embeds linearly into the cycle space of the hub
extension by extending every spoke coordinate with zero. -/
noncomputable def liftHubCycleSpaceLinear (G : PhysicalGraph) :
    G.CycleSpace →ₗ[F₂] (connectByHub G).CycleSpace where
  toFun x := ⟨liftHubWord G x.1, liftHubWord_cycleSpace G x⟩
  map_add' x y := by
    apply Subtype.ext
    funext e
    cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e <;>
      simp [liftHubWord, hdec]
  map_smul' a x := by
    apply Subtype.ext
    funext e
    cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e <;>
      simp [liftHubWord, hdec]

theorem liftHubCycleSpaceLinear_injective (G : PhysicalGraph) :
    Function.Injective (liftHubCycleSpaceLinear G) := by
  intro x y h
  apply Subtype.ext
  funext e
  have he := congrFun (congrArg Subtype.val h) (hubOldEdgeEmbedding G e)
  simpa [liftHubCycleSpaceLinear, liftHubWord,
    hubOldEdgeEmbedding] using he

/-- The hub extension has exactly the same cycle space, after relabelling its
spokes to zero. This follows from injectivity and the already-proved equality
of cycle ranks. -/
noncomputable def hubCycleSpaceEquiv (G : PhysicalGraph) :
    G.CycleSpace ≃ₗ[F₂] (connectByHub G).CycleSpace := by
  have hdim : Module.finrank F₂ G.CycleSpace =
      Module.finrank F₂ (connectByHub G).CycleSpace := by
    change G.cycleRank = (connectByHub G).cycleRank
    exact (cycleRank_connectByHub G).symm
  exact LinearEquiv.ofBijective (liftHubCycleSpaceLinear G)
    ⟨liftHubCycleSpaceLinear_injective G,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (liftHubCycleSpaceLinear_injective G)⟩

theorem selected_adj_lift_iff (G : PhysicalGraph) (x : G.Word)
    (u v : G.Vertex) :
    ((connectByHub G).selectedGraph (liftHubWord G x)).Adj
      (hubVertexMap G u) (hubVertexMap G v) ↔
    (G.selectedGraph x).Adj u v := by
  classical
  constructor
  · rintro ⟨e, he, hend⟩
    cases hdec : (Fintype.equivFin (G.Edge ⊕ HubComponent G)).symm e with
    | inl f =>
      have hedge : e = hubOldEdgeEmbedding G f := by
        dsimp [hubOldEdgeEmbedding]
        rw [← hdec]
        exact (Fintype.equivFin (G.Edge ⊕ HubComponent G)).apply_symm_apply e |>.symm
      subst e
      refine ⟨f, ?_, ?_⟩
      · simpa using he
      · rw [connectByHub_src_old, connectByHub_dst_old] at hend
        rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl ⟨hubVertexMap_injective G h₁, hubVertexMap_injective G h₂⟩
        · exact Or.inr ⟨hubVertexMap_injective G h₁, hubVertexMap_injective G h₂⟩
    | inr c =>
      have hzero : liftHubWord G x e = 0 := by simp [liftHubWord, hdec]
      exact (he hzero).elim
  · rintro ⟨e, he, hend⟩
    refine ⟨hubOldEdgeEmbedding G e, ?_, ?_⟩
    · simpa using he
    · rw [connectByHub_src_old, connectByHub_dst_old]
      rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg (hubVertexMap G) h₁, congrArg (hubVertexMap G) h₂⟩
      · exact Or.inr ⟨congrArg (hubVertexMap G) h₁, congrArg (hubVertexMap G) h₂⟩

noncomputable def usedVertexEquiv (G : PhysicalGraph) (x : G.Word) :
    {v // v ∈ G.usedVertices x} ≃
      {v // v ∈ (connectByHub G).usedVertices (liftHubWord G x)} where
  toFun v := ⟨hubVertexMap G v.1, by
    rw [liftHubWord_usedVertices]
    exact Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  invFun w := by
    have hm : w.1 ∈ (G.usedVertices x).image (hubVertexMap G) := by
      rw [← liftHubWord_usedVertices]
      exact w.2
    let v := Classical.choose (Finset.mem_image.mp hm)
    exact ⟨v, (Classical.choose_spec (Finset.mem_image.mp hm)).1⟩
  left_inv v := by
    apply Subtype.ext
    apply hubVertexMap_injective G
    have hm : hubVertexMap G v.1 ∈ (G.usedVertices x).image (hubVertexMap G) :=
      Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩
    exact (Classical.choose_spec (Finset.mem_image.mp hm)).2
  right_inv w := by
    apply Subtype.ext
    have hm : w.1 ∈ (G.usedVertices x).image (hubVertexMap G) := by
      rw [← liftHubWord_usedVertices]
      exact w.2
    exact (Classical.choose_spec (Finset.mem_image.mp hm)).2

theorem selected_induce_connected_lift (G : PhysicalGraph) (x : G.Word)
    (hconn : ((G.selectedGraph x).induce (↑(G.usedVertices x) : Set G.Vertex)).Connected) :
    (((connectByHub G).selectedGraph (liftHubWord G x)).induce
      (↑((connectByHub G).usedVertices (liftHubWord G x)) : Set (connectByHub G).Vertex)).Connected := by
  let e := usedVertexEquiv G x
  let f : (G.selectedGraph x).induce (↑(G.usedVertices x) : Set G.Vertex) →g
      ((connectByHub G).selectedGraph (liftHubWord G x)).induce
        (↑((connectByHub G).usedVertices (liftHubWord G x)) : Set (connectByHub G).Vertex) :=
    { toFun := e
      map_rel' := by
        intro a b hab
        change (G.selectedGraph x).Adj a b at hab
        change ((connectByHub G).selectedGraph (liftHubWord G x)).Adj (e a) (e b)
        exact (selected_adj_lift_iff G x a b).2 hab }
  exact hconn.map f e.surjective



/-- A cycle word lifts through the hub extension, preserving its length. -/
def liftHubCycleWord (G : PhysicalGraph) (c : G.CycleWord) :
    (connectByHub G).CycleWord := by
  classical
  let x := c.1
  have hspace : liftHubWord G x ∈ (connectByHub G).CycleSpace :=
    liftHubWord_cycleSpace G ⟨x, by
      apply LinearMap.mem_ker.mpr
      funext v
      change G.boundary x v = 0
      exact congrFun c.2.2.1 v⟩
  refine ⟨liftHubWord G x, ?_⟩
  refine ⟨?_, ?_, selected_induce_connected_lift G x c.2.2.2.1, ?_⟩
  · intro hz
    apply c.2.1
    funext e
    have hz' := congrFun hz (hubOldEdgeEmbedding G e)
    simpa [liftHubWord, hubOldEdgeEmbedding] using hz'
  · change (connectByHub G).boundary (liftHubWord G x) = 0
    exact LinearMap.mem_ker.mp hspace
  · intro t ht
    let e := usedVertexEquiv G x
    let v := e.symm ⟨t, ht⟩
    have hvt : hubVertexMap G v.1 = t := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨t, ht⟩)
    rw [← hvt, selectedDegree_lift_eq]
    exact c.2.2.2.2 v.1 v.2

/-- The lifted cycle word agrees with the original word on every old edge. -/
@[simp] theorem liftHubCycleWord_old_edge (G : PhysicalGraph)
    (c : G.CycleWord) (e : G.Edge) :
    (liftHubCycleWord G c).1 (hubOldEdgeEmbedding G e) = c.1 e := by
  simp [liftHubCycleWord, liftHubWord, hubOldEdgeEmbedding]

/-- The lifted cycle word is zero on every newly added hub spoke. -/
@[simp] theorem liftHubCycleWord_spoke (G : PhysicalGraph)
    (c : G.CycleWord) (e : HubComponent G) :
    (liftHubCycleWord G c).1 (hubSpokeEmbedding G e) = 0 := by
  simp [liftHubCycleWord, liftHubWord, hubSpokeEmbedding]








end Erdos1016.PhysicalGraph
