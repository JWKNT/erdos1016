import Erdos1016.Cycles.Geometry.BoundaryContactGeometry
import Erdos1016.Decomposition.Regions.SingleAttachmentComponents

set_option autoImplicit false

/-!
# Exterior-component preservation for an isolated retained cycle

A newly deleted cycle far from the already selected cycles cannot touch any
small complementary tree: such a tree would need three exits, while all of
its exits would have to go to this single cycle. Thus the cycle attaches
only to the giant component when added back, preserving the exterior count.
-/

noncomputable section
namespace Erdos1016.Proof.IsolatedCycleExterior

open Erdos1016.SafeCore
open Erdos1016.Proof.ConditionalMoments
open Erdos1016.Proof.ConditionalComplementGeometry
open Erdos1016.Proof.ConnectedComponentAttachment

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Contacts through a connected region give a short path in any ambient
induced region containing the contacts and that region. This uses the
ordinary graph with the protector removed, so an apex shortcut is irrelevant. -/
theorem contacts_give_short_walk_within
    {G : PhysicalGraph} (J R A B : Finset G.Vertex)
    (hRJ : R ⊆ J) (hAJ : A ⊆ J) (hBJ : B ⊆ J)
    (hR : ConnectedRegion G R)
    (hA : (crossing G R A).Nonempty) (hB : (crossing G R B).Nonempty) :
    ∃ (u v : J), u.1 ∈ A ∧ v.1 ∈ B ∧
      ∃ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u v,
        p.length ≤ R.card + 1 := by
  obtain ⟨r, hr, u, hu, hru⟩ := (crossing_nonempty_iff G R A).mp hA
  obtain ⟨s, hs, v, hv, hsv⟩ := (crossing_nonempty_iff G R B).mp hB
  have hconn := (connectedRegion_iff_induce_connected G R).mp hR
  obtain ⟨p, hp, _⟩ := hconn.exists_path_of_dist ⟨r, hr⟩ ⟨s, hs⟩
  let incl : G.toSimpleGraph.induce (↑R : Set G.Vertex) →g
      G.toSimpleGraph.induce (↑J : Set G.Vertex) :=
    { toFun := fun z => ⟨z.1, hRJ z.2⟩, map_rel' := fun h => h }
  have hfirst : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Adj
      ⟨u, hAJ hu⟩ (incl ⟨r, hr⟩) := hru.symm
  have hlast : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Adj
      (incl ⟨s, hs⟩) ⟨v, hBJ hv⟩ := hsv
  let w : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk
      ⟨u, hAJ hu⟩ ⟨v, hBJ hv⟩ :=
    .cons hfirst ((p.map incl).concat hlast)
  have hlen : w.length = p.length + 2 := by simp [w]
  have hcardInduced : Fintype.card (↑R : Set G.Vertex) = R.card :=
    Fintype.card_ofFinset R (by intro v; rfl)
  have hpLen : p.length < R.card := by simpa only [hcardInduced] using hp.length_lt
  exact ⟨⟨u, hAJ hu⟩, ⟨v, hBJ hv⟩, hu, hv, w, by omega⟩

/-- A small cubic tree with at most one edge to `D` cannot meet `D` when
`D` is far from every other deleted vertex. -/
theorem small_tree_no_contact_to_far_region
    {G : PhysicalGraph} (J U D R : Finset G.Vertex) (q : ℕ)
    (hUJ : U ⊆ J) (hDJ : D ⊆ J) (hRJ : R ⊆ J)
    (hR : R ∈ components G (U ∪ D)ᶜ)
    (htree : (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic)
    (hcubic : ∀ v ∈ R, G.degree v = 3)
    (hsize : R.card + 1 ≤ q)
    (hunique : ∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f)
    (hfar : ∀ (u d : J), u.1 ∈ U → d.1 ∈ D →
      ∀ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u d, q < p.length) :
    crossing G R D = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro e he
  have hconn := component_connected G hR
  have hnoU : crossing G R U = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro f hf
    obtain ⟨u, d, hu, hd, p, hclose⟩ := contacts_give_short_walk_within
      J R U D hRJ hUJ hDJ hconn ⟨f, hf⟩ ⟨e, he⟩
    have := hfar u d hu hd p
    omega
  have htip : ∀ f : ownerCut G R, boundaryTip G R f ∈ D := by
    intro f
    have hUD : boundaryTip G R f ∈ U ∪ D := by
      by_contra hout
      exact boundaryTip_not_mem G R f
        (component_closed G hR _ (boundaryBase G R f).2 _
          (Finset.mem_compl.mpr hout) (boundary_adj G R f))
    rcases Finset.mem_union.mp hUD with hu | hd
    · have hc := (crossing_nonempty_iff G R U).mpr
        ⟨_, (boundaryBase G R f).2, _, hu, boundary_adj G R f⟩
      simp only [hnoU, Finset.not_nonempty_empty] at hc
    · exact hd
  have hsub : ownerCut G R ⊆ crossing G R D := by
    intro f hf
    let f' : ownerCut G R := ⟨f, hf⟩
    apply (mem_crossing G R D f).mpr
    rcases boundary_endpoints G R f' with h | h
    · exact Or.inl ⟨h.1 ▸ (boundaryBase G R f').2, h.2 ▸ htip f'⟩
    · exact Or.inr ⟨h.1 ▸ htip f', h.2 ▸ (boundaryBase G R f').2⟩
  have hcut : cutSize G R ≤ 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_le_one.mpr (fun e he f hf => hunique e f he hf))
  rw [cubic_tree_cut G hcubic hconn htree] at hcut
  omega

/-- The exterior count is unchanged when a connected deleted region is far
from the previous deletion and every other new component is a small cubic
tree with at most one contact to that region. No assumptions on the old
complement components are required. -/
theorem originalExteriorComponents_union_eq_of_far_region
    {G : PhysicalGraph} (hG : G.IsConnected)
    (J U D B : Finset G.Vertex) (q : ℕ) (hq : 1 ≤ q)
    (hUJ : U ⊆ J) (hDJ : D ⊆ J)
    (hdisj : Disjoint U D) (hD : ConnectedRegion G D)
    (hB : B ∈ components G (U ∪ D)ᶜ)
    (hsmall : ∀ R ∈ components G (U ∪ D)ᶜ, R ≠ B →
      R ⊆ J ∧ (G.toSimpleGraph.induce (↑R : Set G.Vertex)).IsAcyclic ∧
      (∀ v ∈ R, G.degree v = 3) ∧ R.card + 1 ≤ q ∧
      (∀ e f, e ∈ crossing G R D → f ∈ crossing G R D → e = f))
    (hfar : ∀ (u d : J), u.1 ∈ U → d.1 ∈ D →
      ∀ p : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Walk u d, q < p.length) :
    G.originalExteriorComponents (U ∪ D) = G.originalExteriorComponents U := by
  let V := (U ∪ D)ᶜ
  have hnoSmall : ∀ R ∈ components G V, R ≠ B → crossing G R D = ∅ := by
    intro R hR hRB
    obtain ⟨hRJ, htree, hcubic, hsize, hunique⟩ := hsmall R hR hRB
    exact small_tree_no_contact_to_far_region J U D R q hUJ hDJ hRJ hR htree hcubic
      hsize hunique hfar
  have honly : ∀ d ∈ D, ∀ v ∈ V, G.toSimpleGraph.Adj d v → v ∈ B := by
    intro d hd v hv hdv
    obtain ⟨R, hR, hvR⟩ := components_cover G hv
    by_cases hRB : R = B
    · simpa only [hRB] using hvR
    · have hedge := (crossing_nonempty_iff G R D).mpr ⟨v, hvR, d, hd, hdv.symm⟩
      simp only [hnoSmall R hR hRB, Finset.not_nonempty_empty] at hedge
  have hDproper : Dᶜ.Nonempty := by
    obtain ⟨v, hvB⟩ := (component_connected G hB).1
    have hv := Finset.mem_compl.mp (component_subset G hB hvB)
    exact ⟨v, Finset.mem_compl.mpr (fun hvD => hv (Finset.mem_union_right _ hvD))⟩
  obtain ⟨d, hd, v, hv, hdv⟩ := (crossing_nonempty_iff G D Dᶜ).mp
    (ownerCut_nonempty G hG hD.1 hDproper)
  have hvU : v ∉ U := by
    intro hvU
    have hstep : (G.toSimpleGraph.induce (↑J : Set G.Vertex)).Adj
        ⟨v, hUJ hvU⟩ ⟨d, hDJ hd⟩ := hdv.symm
    have hf := hfar ⟨v, hUJ hvU⟩ ⟨d, hDJ hd⟩ hvU hd
      (SimpleGraph.Walk.cons hstep SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hf
    omega
  have hvV : v ∈ V := by
    apply Finset.mem_compl.mpr
    intro hvUnion
    rcases Finset.mem_union.mp hvUnion with h | h
    · exact hvU h
    · exact Finset.mem_compl.mp hv h
  have htouch : (crossing G B D).Nonempty :=
    (crossing_nonempty_iff G B D).mpr ⟨v, honly d hd v hvV hdv, d, hd, hdv.symm⟩
  have hVD : Disjoint V D := by
    apply Finset.disjoint_left.mpr
    intro v hvV hvD
    exact Finset.mem_compl.mp hvV (Finset.mem_union_right _ hvD)
  have hcomp := componentCount_union_eq_of_single_attachment G V D B hVD hD hB htouch honly
  have hset : V ∪ D = Uᶜ := by
    ext v
    simp only [V, Finset.mem_union, Finset.mem_compl]
    have hd : v ∈ D → v ∉ U := fun hvD hvU => Finset.disjoint_left.mp hdisj hvU hvD
    tauto
  rw [hset] at hcomp
  rw [← exteriorCount_eq_original, ← exteriorCount_eq_original]
  exact hcomp.symm

end Erdos1016.Proof.IsolatedCycleExterior

end
