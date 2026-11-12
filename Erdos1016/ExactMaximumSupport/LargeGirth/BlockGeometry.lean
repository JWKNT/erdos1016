import Erdos1016.ExactMaximumSupport.LargeGirth.ChainSelection
import Erdos1016.Graph.Multigraph.RegionBoundaryUnion

set_option autoImplicit false

/-!
# Physical boundaries of separator blocks

Blocks use the original vertex labels after deletion of one cycle.
Cleaning removes their neighbours of the deleted cycle. Every remaining
boundary edge then ends on one of the two end cycles.
-/

noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth

open SimpleGraph PolynomialBound.Separation FiniteMultiGraph

local instance blockGeometryDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem block_deleted_not_mem {V : Type*} (H : SimpleGraph V) (A B C : Set V)
    {u x : V} (hu : u ∉ A)
    (hx : x ∈ block (deletedGraph H A) u B C) : x ∉ A := by
  exact ((reachable_deleted_iff H A hu).mp hx.1.reachable).right_not_mem

/-- A clean block has no deleted-edge exception in its boundary. -/
theorem clean_block_boundary {V : Type*} (H : SimpleGraph V) (A B C : Set V)
    {u x y : V} (hu : u ∉ A)
    (hclean : ∀ z ∈ block (deletedGraph H A) u B C, ∀ a ∈ A, ¬ H.Adj z a)
    (hx : x ∈ block (deletedGraph H A) u B C) (hxy : H.Adj x y)
    (hy : y ∉ block (deletedGraph H A) u B C) : y ∈ B ∨ y ∈ C := by
  have hxA := block_deleted_not_mem H A B C hu hx
  have hyA : y ∉ A := fun hyA => hclean x hx y hyA hxy
  exact mem_separator_of_adj_block hx ⟨hxy, hxA, hyA⟩ hy

/-- A block avoids every connected marked set containing the far anchor. -/
theorem block_deleted_disjoint_marker {V : Type*} (H : SimpleGraph V)
    (A B C P : Set V) {u p : V}
    (hsep : Separates (deletedGraph H A) C u p)
    (hP : IsConnectedSet H P) (hp : p ∈ P)
    (hPA : Disjoint P A) (hPC : Disjoint P C) :
    Disjoint (block (deletedGraph H A) u B C) P := by
  apply Set.disjoint_left.mpr
  intro x hx hxP
  exact (block_no_neighbor_anchor hsep (connectedSet_deleted H A P hP hPA)
    hp hPC hx hxP).1 rfl

def blockVertices (G : FiniteMultiGraph) (A B C : Finset G.Vertex) (u : G.Vertex) :
    Finset G.Vertex :=
  Finset.univ.filter fun x => x ∈ block (deletedGraph G.toSimpleGraph (↑A)) u (↑B) (↑C)

@[simp] theorem mem_blockVertices (G : FiniteMultiGraph) (A B C : Finset G.Vertex)
    (u x : G.Vertex) :
    x ∈ blockVertices G A B C u ↔
      x ∈ block (deletedGraph G.toSimpleGraph (↑A)) u (↑B) (↑C) := by
  simp [blockVertices]

/-- The inclusion counts physical labels, including parallel boundary edges. -/
theorem clean_block_cut_subset (G : FiniteMultiGraph) (A B C : Finset G.Vertex)
    (u : G.Vertex) (hu : u ∉ A)
    (hclean : ∀ x ∈ blockVertices G A B C u, ∀ a ∈ A, ¬ G.toSimpleGraph.Adj x a) :
    G.cutEdges (blockVertices G A B C u) ⊆ G.cutEdges B ∪ G.cutEdges C := by
  intro e he
  have step {x y : G.Vertex}
      (hx : x ∈ blockVertices G A B C u) (hy : y ∉ blockVertices G A B C u)
      (hxy : G.toSimpleGraph.Adj x y) :
      (x ∉ B ∧ x ∉ C) ∧ (y ∈ B ∨ y ∈ C) := by
    have hx' := (mem_blockVertices G A B C u x).mp hx
    refine ⟨⟨fun h => hx'.2 (Or.inr h), hx'.1.right_not_mem⟩, ?_⟩
    exact clean_block_boundary G.toSimpleGraph (↑A) (↑B) (↑C) hu
      (fun z hz a ha => hclean z ((mem_blockVertices G A B C u z).mpr hz) a ha)
      hx' hxy (fun h => hy ((mem_blockVertices G A B C u y).mpr h))
  have hc := (Finset.mem_filter.mp he).2
  rcases hc with h | h
  · have hne : G.src e ≠ G.dst e := fun heq => h.2 (heq ▸ h.1)
    have hh := step h.1 h.2 ⟨hne, e, Or.inl ⟨rfl, rfl⟩⟩
    simp only [cutEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · have hne : G.dst e ≠ G.src e := fun heq => h.1 (heq ▸ h.2)
    have hh := step h.2 h.1 ⟨hne, e, Or.inr ⟨rfl, rfl⟩⟩
    simp only [cutEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

theorem clean_block_cut_card_le (G : FiniteMultiGraph) (A B C : Finset G.Vertex)
    (u : G.Vertex) (hu : u ∉ A)
    (hclean : ∀ x ∈ blockVertices G A B C u, ∀ a ∈ A, ¬ G.toSimpleGraph.Adj x a)
    (b c : G.EdgeWord)
    (hb : ∀ v ∈ B, G.selectedDegree b v = 2)
    (hc : ∀ v ∈ C, G.selectedDegree c v = 2)
    (hbs : ∀ e, e ∉ G.internalEdges B → b e = 0)
    (hcs : ∀ e, e ∉ G.internalEdges C → c e = 0)
    (hmax : ∀ v, G.degree v ≤ 3) :
    (G.cutEdges (blockVertices G A B C u)).card ≤ B.card + C.card := by
  exact (Finset.card_le_card (clean_block_cut_subset G A B C u hu hclean)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add
      (G.cutEdges_card_le_of_two_regular B b hb hbs (fun v _ => hmax v))
      (G.cutEdges_card_le_of_two_regular C c hc hcs (fun v _ => hmax v))))

/-- Disjoint inner supports give the size of a block without a connectivity
assumption on the block itself. -/
theorem card_ge_disjoint_supports {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (F : Finset ι) (U : ι → Finset V) (X : Finset V) (d : ℕ)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (U i) (U j))
    (hsub : ∀ i ∈ F, U i ⊆ X) (hsize : ∀ i ∈ F, d ≤ (U i).card) :
    F.card * d ≤ X.card := by
  have hsum : F.card * d ≤ ∑ i ∈ F, (U i).card := by
    calc
      _ = ∑ _i ∈ F, d := by simp
      _ ≤ _ := Finset.sum_le_sum hsize
  have hcard : (F.biUnion U).card = ∑ i ∈ F, (U i).card :=
    Finset.card_biUnion (by intro i hi j hj hij; exact hd i hi j hj hij)
  rw [← hcard] at hsum
  exact hsum.trans (Finset.card_le_card (Finset.biUnion_subset.mpr hsub))

/-- Each discarded disjoint block consumes a different bad vertex. -/
theorem bad_blocks_card_le {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (F : Finset ι) (X : ι → Finset V) (B : Finset V)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (X i) (X j)) :
    (F.filter fun i => ¬ Disjoint (X i) B).card ≤ B.card := by
  classical
  let T := F.filter fun i => ¬ Disjoint (X i) B
  have hhit : ∀ i ∈ T, ∃ v ∈ X i, v ∈ B := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    exact Finset.not_disjoint_iff.mp hh
  choose v hvX hvB using hhit
  let f : T → B := fun i => ⟨v i.1 i.2, hvB i.1 i.2⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    have he' : v i.1 i.2 = v j.1 j.2 := congrArg Subtype.val he
    exact Finset.disjoint_left.mp
      (hd i.1 (Finset.mem_filter.mp i.2).1 j.1 (Finset.mem_filter.mp j.2).1 hij)
      (hvX i.1 i.2) (he' ▸ hvX j.1 j.2)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem clean_blocks_card_ge {ι V : Type*} [DecidableEq ι] [DecidableEq V]
    (F : Finset ι) (X : ι → Finset V) (B : Finset V)
    (hd : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (X i) (X j)) :
    F.card ≤ (F.filter fun i => Disjoint (X i) B).card + B.card := by
  have hb := bad_blocks_card_le F X B hd
  have he := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (fun i => Disjoint (X i) B)
  omega

/-- Cut the actual separator chain into large blocks and discard those
meeting the extra forbidden set or a neighbour of the deleted cycle.
The remaining blocks have physical boundary at most twice the cycle length. -/
theorem exists_clean_chain_blocks {ι : Type*} [DecidableEq ι]
    (G : FiniteMultiGraph) (A P S : Finset G.Vertex) (u p : G.Vertex)
    (F : Finset ι) (U : ι → Finset G.Vertex) (seed : ι → G.EdgeWord)
    (q m d L : ℕ)
    (hfamily : SeparatorFamily (deletedGraph G.toSimpleGraph (↑A)) u p F (fun i => ↑(U i)))
    (hu : u ∉ A) (hm : m*q < F.card)
    (hP : IsConnectedSet G.toSimpleGraph (↑P)) (hp : p ∈ P)
    (hPA : Disjoint P A) (hPU : ∀ i ∈ F, Disjoint P (U i))
    (hsize : ∀ i ∈ F, d ≤ (U i).card) (hlen : ∀ i ∈ F, (U i).card ≤ L)
    (htwo : ∀ i ∈ F, ∀ v ∈ U i, G.selectedDegree (seed i) v = 2)
    (hsupport : ∀ i ∈ F, ∀ e, e ∉ G.internalEdges (U i) → seed i e = 0)
    (hmax : ∀ v, G.degree v ≤ 3) :
    ∃ (X : Fin m → Finset G.Vertex) (J : Finset (Fin m)),
      m ≤ J.card + (G.cutEdges A).card + S.card ∧
      (∀ l l', l ≠ l' → Disjoint (X l) (X l')) ∧
      (∀ l ∈ J, (q-1)*d ≤ (X l).card ∧ (G.cutEdges (X l)).card ≤ 2*L ∧
        Disjoint (X l) (P ∪ S)) := by
  classical
  obtain ⟨lo, hi, inner, hends, hdisj, hin⟩ := hfamily.exists_blocks q m hm
  let X : Fin m → Finset G.Vertex := fun l => blockVertices G A (U (lo l)) (U (hi l)) u
  let bad := cutOutsideVertices G A ∪ S
  let J := Finset.univ.filter fun l : Fin m => Disjoint (X l) bad
  have hXdisj : ∀ l l', l ≠ l' → Disjoint (X l) (X l') := by
    intro l l' hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact Set.disjoint_left.mp (hdisj l l' hne)
      ((mem_blockVertices G A (U (lo l)) (U (hi l)) u v).mp hv)
      ((mem_blockVertices G A (U (lo l')) (U (hi l')) u v).mp hv')
  refine ⟨X, J, ?_, hXdisj, ?_⟩
  · have hh := clean_blocks_card_ge (Finset.univ : Finset (Fin m)) X bad
      (fun i _ j _ hij => hXdisj i j hij)
    have hb := Finset.card_union_le (cutOutsideVertices G A) S
    have hc := cutOutsideVertices_card_le G A
    have hh' : m ≤ J.card + bad.card := by simpa only [Finset.card_univ, Fintype.card_fin] using hh
    dsimp only [bad] at hh'
    omega
  · intro l hl
    have hgood : Disjoint (X l) bad := (Finset.mem_filter.mp hl).2
    have hclean : ∀ x ∈ X l, ∀ a ∈ A, ¬ G.toSimpleGraph.Adj x a := by
      intro x hx a ha hadj
      have hxA : x ∉ A := block_deleted_not_mem G.toSimpleGraph (↑A)
        (↑(U (lo l))) (↑(U (hi l))) hu ((mem_blockVertices _ _ _ _ _ _).mp hx)
      have hout := mem_cutOutsideVertices_of_adj G A ha hxA hadj.symm
      exact Finset.disjoint_left.mp hgood hx (Finset.mem_union_left S hout)
    have hbound := clean_block_cut_card_le G A (U (lo l)) (U (hi l)) u hu hclean
      (seed (lo l)) (seed (hi l)) (htwo _ (hends l).1) (htwo _ (hends l).2)
      (hsupport _ (hends l).1) (hsupport _ (hends l).2) hmax
    refine ⟨?_, hbound.trans (by have := hlen _ (hends l).1; have := hlen _ (hends l).2; omega), ?_⟩
    · have hh := card_ge_disjoint_supports (inner l) U (X l) d
        (fun i hi j hj hij => by exact_mod_cast hfamily.disj i ((hin l).1 hi) j ((hin l).1 hj) hij)
        (fun i hi v hv => (mem_blockVertices _ _ _ _ _ _).mpr ((hin l).2.2 i hi hv))
        (fun i hi => hsize i ((hin l).1 hi))
      rw [(hin l).2.1] at hh
      exact hh
    · have hmarker := block_deleted_disjoint_marker G.toSimpleGraph (↑A)
        (↑(U (lo l))) (↑(U (hi l))) (↑P) (hfamily.sep _ (hends l).2) hP hp
        (by exact_mod_cast hPA) (by exact_mod_cast hPU _ (hends l).2)
      apply Finset.disjoint_left.mpr
      intro v hv hvbad
      rcases Finset.mem_union.mp hvbad with hvP | hvS
      · exact Set.disjoint_left.mp hmarker ((mem_blockVertices _ _ _ _ _ _).mp hv) hvP
      · exact Finset.disjoint_left.mp hgood hv (Finset.mem_union_right _ hvS)

end Erdos1016.ExactMaximumSupport.LargeGirth
