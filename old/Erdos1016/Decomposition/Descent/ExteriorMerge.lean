import Erdos1016.Decomposition.Regions.Cuts

set_option autoImplicit false

/-!
# Exact ORIGINAL exterior update and the safe-sibling lemma

If connected S,T partition J, the components of G-S are the single component
formed by T and all old exterior components touching T, together with the
untouched old exterior components. This is proved as an equality of actual
component vertex sets before taking cardinalities.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.SafeCore
local instance instSafeCoreExteriorMergePropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable (G : PhysicalGraph)

/-- Both shores are actual, nonempty, connected induced vertex regions. -/
structure BondSplit (U : Finset G.Vertex) where
  left : Finset G.Vertex
  right : Finset G.Vertex
  disjoint : Disjoint left right
  union_eq : left ∪ right = U
  left_connected : ConnectedRegion G left
  right_connected : ConnectedRegion G right

namespace BondSplit
variable {G} {U : Finset G.Vertex}

def symm (s : BondSplit G U) : BondSplit G U where
  left := s.right
  right := s.left
  disjoint := s.disjoint.symm
  union_eq := by rw [Finset.union_comm, s.union_eq]
  left_connected := s.right_connected
  right_connected := s.left_connected

theorem left_subset (s : BondSplit G U) : s.left ⊆ U := by
  calc
    s.left ⊆ s.left ∪ s.right := Finset.subset_union_left
    _ = U := s.union_eq

theorem right_subset (s : BondSplit G U) : s.right ⊆ U := by
  calc
    s.right ⊆ s.left ∪ s.right := Finset.subset_union_right
    _ = U := s.union_eq

theorem card_add (s : BondSplit G U) : s.left.card + s.right.card = U.card := by
  rw [← Finset.card_union_of_disjoint s.disjoint, s.union_eq]

theorem left_card_lt (s : BondSplit G U) : s.left.card < U.card := by
  have := Finset.card_pos.2 s.right_connected.1
  have := s.card_add
  omega

theorem right_card_lt (s : BondSplit G U) : s.right.card < U.card := by
  have := Finset.card_pos.2 s.left_connected.1
  have := s.card_add
  omega

theorem right_subset_left_compl (s : BondSplit G U) : s.right ⊆ s.leftᶜ := by
  intro v hv
  exact Finset.mem_compl.2 fun h => Finset.disjoint_left.1 s.disjoint h hv



end BondSplit

def touchingComponents (J T : Finset G.Vertex) : Finset (Finset G.Vertex) :=
  (components G Jᶜ).filter fun C => (crossing G C T).Nonempty

@[simp] theorem mem_touchingComponents (J T C : Finset G.Vertex) :
    C ∈ touchingComponents G J T ↔
      C ∈ components G Jᶜ ∧ (crossing G C T).Nonempty := by
  simp only [touchingComponents, Finset.mem_filter]

def mergedExterior (J T : Finset G.Vertex) : Finset G.Vertex :=
  T ∪ (touchingComponents G J T).biUnion id

theorem connected_attach_family (T : Finset G.Vertex) (P : Finset (Finset G.Vertex))
    (hT : ConnectedRegion G T)
    (hc : ∀ C ∈ P, ConnectedRegion G C)
    (ht : ∀ C ∈ P, (crossing G T C).Nonempty) :
    ConnectedRegion G (T ∪ P.biUnion id) := by
  induction P using Finset.induction_on with
  | empty => simpa using hT
  | @insert C P hCP ih =>
      have hcC := hc C (Finset.mem_insert_self _ _)
      have hcP : ∀ D ∈ P, ConnectedRegion G D :=
        fun D hD => hc D (Finset.mem_insert_of_mem hD)
      have htP : ∀ D ∈ P, (crossing G T D).Nonempty :=
        fun D hD => ht D (Finset.mem_insert_of_mem hD)
      have hp := ih hcP htP
      have hedge : (crossing G (T ∪ P.biUnion id) C).Nonempty :=
        (ht C (Finset.mem_insert_self _ _)).mono
          (crossing_mono G Finset.subset_union_left (Finset.Subset.refl _))
      simpa only [Finset.biUnion_insert, id_eq, Finset.union_assoc,
        Finset.union_left_comm, Finset.union_comm] using
        connected_union_of_edge G hp hcC hedge

theorem mergedExterior_connected {J : Finset G.Vertex} (s : BondSplit G J) :
    ConnectedRegion G (mergedExterior G J s.right) := by
  apply connected_attach_family G s.right (touchingComponents G J s.right)
    s.right_connected
  · intro C hC
    exact component_connected G ((mem_touchingComponents G J s.right C).1 hC).1
  · intro C hC
    rw [crossing_comm]
    exact ((mem_touchingComponents G J s.right C).1 hC).2

theorem outside_left_cases {J : Finset G.Vertex} (s : BondSplit G J)
    {v : G.Vertex} (hv : v ∈ s.leftᶜ) : v ∈ s.right ∨ v ∈ Jᶜ := by
  by_cases h : v ∈ s.right
  · exact Or.inl h
  · right
    apply Finset.mem_compl.2
    intro hvJ
    rw [← s.union_eq] at hvJ
    rcases Finset.mem_union.1 hvJ with hL | hR
    · exact (Finset.mem_compl.1 hv) hL
    · exact h hR

theorem mergedExterior_isComponent {J : Finset G.Vertex} (s : BondSplit G J) :
    IsComponent G s.leftᶜ (mergedExterior G J s.right) := by
  refine ⟨?_, mergedExterior_connected G s, ?_⟩
  · intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact s.right_subset_left_compl hv
    · obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hv
      have hvJ := component_subset G ((mem_touchingComponents G J s.right C).1 hC).1 hvC
      exact Finset.mem_compl.2 fun hvL => (Finset.mem_compl.1 hvJ) (s.left_subset hvL)
  · intro v hv w hw hvw
    rcases outside_left_cases G s hw with hwT | hwO
    · exact Finset.mem_union_left _ hwT
    · rcases Finset.mem_union.1 hv with hvT | hvOld
      · obtain ⟨C, hC, hwC⟩ := components_cover G hwO
        have ht : C ∈ touchingComponents G J s.right :=
          (mem_touchingComponents G J s.right C).2
            ⟨hC, (crossing_nonempty_iff G C s.right).2 ⟨w, hwC, v, hvT, hvw.symm⟩⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨C, ht, hwC⟩)
      · obtain ⟨C, hC, hvC⟩ := Finset.mem_biUnion.1 hvOld
        have hwC := component_closed G
          ((mem_touchingComponents G J s.right C).1 hC).1 v hvC w hwO hvw
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨C, hC, hwC⟩)

theorem untouched_isComponent {J C : Finset G.Vertex} (s : BondSplit G J)
    (hC : C ∈ components G Jᶜ) (hn : C ∉ touchingComponents G J s.right) :
    IsComponent G s.leftᶜ C := by
  refine ⟨?_, component_connected G hC, ?_⟩
  · intro v hv
    have hvJ := component_subset G hC hv
    exact Finset.mem_compl.2 fun hvS => (Finset.mem_compl.1 hvJ) (s.left_subset hvS)
  · intro v hv w hw hvw
    rcases outside_left_cases G s hw with hwT | hwO
    · exact False.elim (hn ((mem_touchingComponents G J s.right C).2
        ⟨hC, (crossing_nonempty_iff G C s.right).2 ⟨v, hv, w, hwT, hvw⟩⟩))
    · exact component_closed G hC v hv w hwO hvw

/-- Exact component partition after discarding the right shore. -/
theorem exterior_components_after_split {J : Finset G.Vertex} (s : BondSplit G J) :
    components G s.leftᶜ =
      insert (mergedExterior G J s.right)
        (components G Jᶜ \ touchingComponents G J s.right) := by
  apply components_eq_of_cover G
  · intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact mergedExterior_isComponent G s
    · obtain ⟨hC, hn⟩ := Finset.mem_sdiff.1 hC
      exact untouched_isComponent G s hC hn
  · intro v hv
    rcases outside_left_cases G s hv with hvT | hvO
    · exact ⟨mergedExterior G J s.right, Finset.mem_insert_self _ _,
        Finset.mem_union_left _ hvT⟩
    · obtain ⟨C, hC, hvC⟩ := components_cover G hvO
      by_cases ht : C ∈ touchingComponents G J s.right
      · exact ⟨mergedExterior G J s.right, Finset.mem_insert_self _ _,
          Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨C, ht, hvC⟩)⟩
      · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨hC, ht⟩), hvC⟩

theorem mergedExterior_not_old {J : Finset G.Vertex} (s : BondSplit G J) :
    mergedExterior G J s.right ∉ components G Jᶜ := by
  intro h
  obtain ⟨v, hv⟩ := s.right_connected.1
  have ho := component_subset G h (Finset.mem_union_left _ hv)
  exact (Finset.mem_compl.1 ho) (s.right_subset hv)

/-- The subtraction-free exact update is safe even at the zero-touch endpoint. -/
theorem exteriorCount_split_add {J : Finset G.Vertex} (s : BondSplit G J) :
    exteriorCount G s.left + (touchingComponents G J s.right).card =
      exteriorCount G J + 1 := by
  have hsub : touchingComponents G J s.right ⊆ components G Jᶜ :=
    Finset.filter_subset _ _
  have hparts := Finset.card_sdiff_add_card_eq_card hsub
  have hn : mergedExterior G J s.right ∉
      components G Jᶜ \ touchingComponents G J s.right := by
    intro h
    exact mergedExterior_not_old G s (Finset.mem_sdiff.1 h).1
  have hc := exterior_components_after_split G s
  unfold exteriorCount componentCount
  rw [hc, Finset.card_insert_of_not_mem hn]
  omega

/-- Formula (14.1), now with the original graph component count. -/
theorem originalExteriorComponents_split_add {J : Finset G.Vertex} (s : BondSplit G J) :
    G.originalExteriorComponents s.left + (touchingComponents G J s.right).card =
      G.originalExteriorComponents J + 1 := by
  simpa only [exteriorCount_eq_original] using exteriorCount_split_add G s

/-- Nonempty contact, not a low-deficit assumption, prevents count growth. -/
theorem exteriorCount_left_le_of_touch {J : Finset G.Vertex} (s : BondSplit G J)
    (ht : (touchingComponents G J s.right).Nonempty) :
    exteriorCount G s.left ≤ exteriorCount G J := by
  have h := exteriorCount_split_add G s
  have hpos := Finset.card_pos.2 ht
  omega

theorem component_touches_removed (hG : G.IsConnected) {J C : Finset G.Vertex}
    (hJ : J.Nonempty) (hC : C ∈ components G Jᶜ) : (crossing G C J).Nonempty := by
  have hproper : Cᶜ.Nonempty := by
    obtain ⟨v, hv⟩ := hJ
    refine ⟨v, Finset.mem_compl.2 ?_⟩
    intro hvC
    exact (Finset.mem_compl.1 (component_subset G hC hvC)) hv
  have hcut := ownerCut_nonempty G hG (component_connected G hC).1 hproper
  obtain ⟨v, hv, w, hw, hvw⟩ := (crossing_nonempty_iff G C Cᶜ).1 hcut
  have hwJ : w ∈ J := by
    by_contra hn
    have hwC := component_closed G hC v hv w (Finset.mem_compl.2 hn) hvw
    exact (Finset.mem_compl.1 hw) hwC
  exact (crossing_nonempty_iff G C J).2 ⟨v, hv, w, hwJ, hvw⟩

theorem no_touch_iff_no_original_contact {J T : Finset G.Vertex} :
    touchingComponents G J T = ∅ ↔ crossing G T Jᶜ = ∅ := by
  constructor
  · intro hn
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro e he
    obtain ⟨v, hv, w, hw, hvw⟩ := (crossing_nonempty_iff G T Jᶜ).1 ⟨e, he⟩
    obtain ⟨C, hC, hwC⟩ := components_cover G hw
    have ht := (mem_touchingComponents G J T C).2
      ⟨hC, (crossing_nonempty_iff G C T).2 ⟨w, hwC, v, hv, hvw.symm⟩⟩
    simpa only [hn, Finset.not_mem_empty] using ht
  · intro hn
    apply Finset.eq_empty_iff_forall_not_mem.2
    intro C hC
    obtain ⟨hC, ht⟩ := (mem_touchingComponents G J T C).1 hC
    obtain ⟨v, hv, w, hw, hvw⟩ := (crossing_nonempty_iff G C T).1 ht
    have hedge := (crossing_nonempty_iff G T Jᶜ).2
      ⟨w, hw, v, component_subset G hC hv, hvw.symm⟩
    simpa only [hn, Finset.not_nonempty_empty] using hedge

/-- Every old exterior component touches the retained shore at an unsafe step. -/
theorem all_touch_left_of_no_touch_right (hG : G.IsConnected)
    {J : Finset G.Vertex} (s : BondSplit G J)
    (hn : touchingComponents G J s.right = ∅) :
    touchingComponents G J s.left = components G Jᶜ := by
  apply Finset.Subset.antisymm (Finset.filter_subset _ _)
  intro C hC
  have hJ : J.Nonempty := s.left_connected.1.mono s.left_subset
  obtain ⟨v, hv, w, hw, hvw⟩ := (crossing_nonempty_iff G C J).1
    (component_touches_removed G hG hJ hC)
  rw [← s.union_eq] at hw
  rcases Finset.mem_union.1 hw with hwL | hwR
  · exact (mem_touchingComponents G J s.left C).2
      ⟨hC, (crossing_nonempty_iff G C s.left).2 ⟨v, hv, w, hwL, hvw⟩⟩
  · have ht := (mem_touchingComponents G J s.right C).2
      ⟨hC, (crossing_nonempty_iff G C s.right).2 ⟨v, hv, w, hwR, hvw⟩⟩
    exact False.elim (by simpa only [hn, Finset.not_mem_empty] using ht)

/-- An unsafe retained child has a SAFE sibling with connected ORIGINAL exterior.
No low-potential hypothesis on J is present. -/
theorem safe_sibling (hG : G.IsConnected) {J : Finset G.Vertex}
    (s : BondSplit G J) (hn : touchingComponents G J s.right = ∅) :
    exteriorCount G s.left = exteriorCount G J + 1 ∧
    exteriorCount G s.right = 1 ∧
    ConnectedRegion G s.rightᶜ ∧
    cutSize G s.right = crossSize G s.left s.right := by
  have hl := exteriorCount_split_add G s
  have hr := exteriorCount_split_add G s.symm
  have hall := all_touch_left_of_no_touch_right G hG s hn
  have hr1 : exteriorCount G s.right = 1 := by
    change exteriorCount G s.right + (touchingComponents G J s.left).card =
      exteriorCount G J + 1 at hr
    rw [hall] at hr
    change exteriorCount G s.right + exteriorCount G J = exteriorCount G J + 1 at hr
    omega
  refine ⟨?_, hr1, connected_of_componentCount_eq_one G hr1, ?_⟩
  · simpa only [hn, Finset.card_empty, Nat.add_zero] using hl
  · apply child_cut_eq_cross_of_no_outside G s.left s.right s.disjoint
    rw [s.union_eq]
    exact (no_touch_iff_no_original_contact G).1 hn

end Erdos1016.SafeCore
