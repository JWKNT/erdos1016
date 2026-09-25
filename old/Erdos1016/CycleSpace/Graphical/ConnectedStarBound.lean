import Erdos1016.CycleSpace.Graphical.AvoidingPairSpan
import Erdos1016.CycleSpace.Graphical.LinkKernel

set_option autoImplicit false

noncomputable section

namespace Erdos1016.Proof.GraphicalTripleStarBoundGraphConnected

open Erdos1016
open Erdos1016.Proof.GraphicalAbstractLinks
open Erdos1016.Proof.GraphicalCommonInformation
open Erdos1016.Proof.GraphicalLinkMap
open Erdos1016.Proof.GraphicalLinkKernelDecomposition
open Erdos1016.Proof.GraphicalTripleStarBoundGraph
open Erdos1016.Proof.GraphicalTripleReduction
open Erdos1016.Proof.GraphicalTripleStarBoundGraphAway

local notation "F₂" => ZMod 2

local instance graphPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

private theorem deletedWalk_exists_of_good (G : PhysicalGraph) (u v : G.Vertex)
    {a b : G.Vertex} (p : G.toSimpleGraph.Walk a b)
    (hgood : ∀ z ∈ p.support, z ≠ u ∧ z ≠ v) :
    ∃ ha : a ≠ u ∧ a ≠ v, ∃ hb : b ≠ u ∧ b ≠ v,
      Nonempty ((deletedGraph G u v).Walk ⟨a, ha⟩ ⟨b, hb⟩) := by
  induction p with
  | nil =>
      have ha := hgood _ (SimpleGraph.Walk.start_mem_support _)
      exact ⟨ha, ha, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons a c b hac q ih =>
      have ha := hgood a (by simp)
      have hc := hgood c (by simp)
      have htail : ∀ z ∈ q.support, z ≠ u ∧ z ≠ v := by
        intro z hz
        exact hgood z (by simp [hz])
      obtain ⟨hc', hb, ⟨q'⟩⟩ := ih htail
      refine ⟨ha, hb, ⟨SimpleGraph.Walk.cons ?_ q'⟩⟩
      change (deletedGraph G u v).Adj ⟨a, ha⟩ ⟨c, hc⟩
      exact hac

/-- Any path between distinct vertices yields either a direct link or a
component link through its interior. -/
theorem nonempty_linkIndex_of_path (G : PhysicalGraph) (u v : G.Vertex)
    (huv : u ≠ v) (p : G.toSimpleGraph.Walk u v) (hp : p.IsPath) :
    Nonempty (LinkIndex G u v) := by
  classical
  cases p with
  | nil => exact (huv rfl).elim
  | @cons a x b hax q =>
    cases q with
    | nil =>
      let e := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hax
      let d : DirectLink G u v := ⟨e, by
        exact Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj_spec G hax⟩
      exact ⟨Sum.inl d⟩
    | @cons _ y _ hxy r =>
      let t : G.toSimpleGraph.Walk x v := SimpleGraph.Walk.cons hxy r
      have htpath : t.IsPath := by
        exact SimpleGraph.Walk.IsPath.of_cons hp
      have htlen : 0 < t.length := by
        simp [t, SimpleGraph.Walk.length]
      let y0 : G.Vertex := t.penultimate
      have hyMem : y0 ∈ t.support := by
        apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
        refine ⟨t.length - 1, ?_, by omega⟩
        simp [y0, SimpleGraph.Walk.penultimate]
      have hyv : y0 ≠ v := by
        intro h
        have hinj := htpath.getVert_injOn (by omega : t.length - 1 ≤ t.length)
          (by omega : t.length ≤ t.length)
          (by simpa [y0, SimpleGraph.Walk.penultimate,
            SimpleGraph.Walk.getVert_length] using h)
        omega
      have huNot : u ∉ t.support := by
        have hnd := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons] at hnd
        exact (List.nodup_cons.mp hnd).1
      let qxy := t.takeUntil y0 hyMem
      have hqavoid : ∀ z ∈ qxy.support, z ≠ u ∧ z ≠ v := by
        intro z hz
        have hzt : z ∈ t.support :=
          SimpleGraph.Walk.support_takeUntil_subset t hyMem hz
        constructor
        · intro hzu
          exact huNot (hzu ▸ hzt)
        · have hz' : z ∈ (t.takeUntil y0 hyMem).support := by simpa [qxy] using hz
          exact fun hzv =>
            (SimpleGraph.Walk.endpoint_not_mem_support_takeUntil htpath hyMem hyv.symm) <|
              hzv ▸ hz'
      obtain ⟨hx, hy, ⟨walkXY⟩⟩ :=
        deletedWalk_exists_of_good G u v qxy hqavoid
      let c0 := (deletedGraph G u v).connectedComponentMk ⟨x, hx⟩
      have hreach : (deletedGraph G u v).Reachable ⟨x, hx⟩ ⟨y0, hy⟩ :=
        walkXY.reachable
      have hcomp : (deletedGraph G u v).connectedComponentMk ⟨y0, hy⟩ = c0 :=
        (SimpleGraph.ConnectedComponent.sound hreach).symm
      have hAdjYV : G.toSimpleGraph.Adj y0 v := by
        have hadj := SimpleGraph.Walk.adj_getVert_succ t
          (by omega : t.length - 1 < t.length)
        simpa [y0, SimpleGraph.Walk.penultimate,
          show t.length - 1 + 1 = t.length by omega,
          SimpleGraph.Walk.getVert_length] using hadj
      let eu := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hax
      let ev := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj G hAdjYV
      have heu := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj_spec G hax
      have hev := Erdos1016.Proof.GraphicalLinkPairWitnesses.physicalEdgeOfAdj_spec G hAdjYV
      let c : ComponentLink G u v := ⟨c0, ?_⟩
      · refine ⟨Sum.inr c⟩
      · constructor
        · refine ⟨eu, ⟨x, hx⟩, ?_, ?_⟩
          · rcases heu with h | h
            · refine Or.inl ⟨h.1, ?_⟩
              simpa [eu] using h.2
            · refine Or.inr ⟨h.2, ?_⟩
              simpa [eu] using h.1
          · rfl
        · refine ⟨ev, ⟨y0, hy⟩, ?_, ?_⟩
          · rcases hev with h | h
            · refine Or.inr ⟨h.2, ?_⟩
              simpa [ev] using h.1
            · refine Or.inl ⟨h.1, ?_⟩
              simpa [ev] using h.2
          · exact hcomp

/-- Once the pair (u,v) has a link, choose the distinguished link to be the
component containing w when that component is a link. If it is not a link,
any link works. This gives the component-separation premise needed by the
avoiding-range theorem. -/
theorem exists_link_and_component_separation
    (G : PhysicalGraph) (u v w : G.Vertex)
    [Nonempty (LinkIndex G u v)] :
    ∃ k : LinkIndex G u v,
      ∀ c : ComponentLink G u v,
        (Sum.inr c : LinkIndex G u v) ≠ k →
          w ∉ componentVertices G u v c.1 := by
  classical
  by_cases hwlink : ∃ c : ComponentLink G u v,
      w ∈ componentVertices G u v c.1
  · obtain ⟨c₀, hc₀⟩ := hwlink
    refine ⟨Sum.inr c₀, ?_⟩
    intro c hck hwc
    obtain ⟨hwc', hcomp⟩ := componentVertices_spec G u v c.1 hwc
    obtain ⟨hw₀', hcomp₀⟩ := componentVertices_spec G u v c₀.1 hc₀
    have hbase : c.1 = c₀.1 := hcomp.symm.trans hcomp₀
    have hcc₀ : c = c₀ := Subtype.ext hbase
    apply hck
    exact congrArg Sum.inr hcc₀
  · let k : LinkIndex G u v := Classical.choice ‹Nonempty (LinkIndex G u v)›
    refine ⟨k, ?_⟩
    intro c _ hwc
    exact hwlink ⟨c, hwc⟩

/-- A connected physical graph has at least one link between any two distinct
vertices: a simple path is either a direct edge or passes through a component
of the graph with its endpoints deleted. -/
theorem nonempty_linkIndex_of_connected (G : PhysicalGraph) (u v : G.Vertex)
    (hconn : G.IsConnected) (huv : u ≠ v) :
    Nonempty (LinkIndex G u v) := by
  have hconn' : G.toSimpleGraph.Connected := hconn
  obtain ⟨p, hp⟩ := hconn'.preconnected.exists_isPath u v
  exact nonempty_linkIndex_of_path G u v huv p hp

/-- Connected-graph three-star bound, given the nonemptiness of the (u,v)
link index. This link-existence premise is the only connectedness bridge
needed by the link-space argument. -/
theorem tripleStar_finrank_le_one_of_connected_and_link_nonempty
    (G : PhysicalGraph) (u v w : G.Vertex)
    (_hconn : G.IsConnected)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    [Nonempty (LinkIndex G u v)] :
    Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1 := by
  classical
  obtain ⟨k, hcomp⟩ := exists_link_and_component_separation G u v w
  exact tripleStar_finrank_le_one_of_linkFactorization G u v w huv huw hvw k
    (linkMap_ker_eq_avoiding_sup G u v huv)
    (evenAssignmentsAway_le_avoiding_range G u v w huv huw hvw k hcomp)

/-- Three distinct vertices in a connected physical graph have triple-star
rank at most one. -/
theorem tripleStar_finrank_le_one_of_connected
    (G : PhysicalGraph) (u v w : G.Vertex)
    (hconn : G.IsConnected)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Module.finrank F₂ (tripleStarSpace G u v w) ≤ 1 := by
  letI : Nonempty (LinkIndex G u v) :=
    nonempty_linkIndex_of_connected G u v hconn huv
  exact tripleStar_finrank_le_one_of_connected_and_link_nonempty
    G u v w hconn huv huw hvw

end Erdos1016.Proof.GraphicalTripleStarBoundGraphConnected
