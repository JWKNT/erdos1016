import Erdos1016.ExactMaximumSupport.LargeGirth.PackingStrings

set_option autoImplicit false

/-! The finite covering count closes the packing estimate once strings are short. -/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingCoverCount
open PackingLocalSpaces TerminalStrings
local instance packingCoverDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem card_le_of_cover {V : Type*} [DecidableEq V]
    (marks A Z E : Finset V) (n : ℕ) (length : Fin n→ℕ)
    (vertex : (c : Fin n)→Fin (length c)→V)
    (hcover : ∀v∈marks,v∈A ∨ v∈Z ∨ v∈E ∨ ∃c i,vertex c i=v) :
    marks.card≤A.card+Z.card+E.card+∑c,length c := by
  let C : Finset V := Finset.univ.biUnion fun c => Finset.univ.image (vertex c)
  have hsub : marks⊆((A∪Z)∪E)∪C := by
    intro v hv
    rcases hcover v hv with hA | hZ | hE | ⟨c,i,rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hA))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hZ))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hE)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨c,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  have hC : C.card≤∑c,length c := by
    calc
      _ ≤ ∑c : Fin n,(Finset.univ.image (vertex c)).card := Finset.card_biUnion_le
      _ ≤ ∑c,length c := Finset.sum_le_sum fun c _ =>
        (Finset.card_image_le).trans (by simp)
  have h1 := Finset.card_union_le A Z
  have h2 := Finset.card_union_le (A∪Z) E
  have h3 := Finset.card_union_le ((A∪Z)∪E) C
  have h4 := Finset.card_le_card hsub
  omega

/-- Count selected marks, zero spaces, exceptions, and all string positions. -/
theorem card_le_of_short_strings (Q : FiniteMultiGraph) (marks A E : Finset Q.Vertex)
    (n d bad : ℕ) (s : Fin n→OrderedString Q.toSimpleGraph ∅ (marks\A))
    (hd : 2≤d) (hA : A.card<2^d) (hcut : (Q.cutEdges A).card≤d*A.card)
    (hzero : (marks.filter fun v => localSpace Q v=⊥).card≤1)
    (hE : E.card≤2*(Q.cutEdges A).card) (hn : n≤2*(Q.cutEdges A).card)
    (hcover : ∀v∈marks,v∉A→localSpace Q v≠⊥→v∉E→∃c i,(s c).vertex i=v)
    (hshort : ∀c,(s c).length≤258*(bad+3)) :
    marks.card≤1551*d*(bad+1)*2^d := by
  let Z := marks.filter fun v => localSpace Q v=⊥
  have hc := card_le_of_cover marks A Z E n (fun c => (s c).length)
    (fun c => (s c).vertex) (by
      intro v hv
      by_cases hvA : v∈A
      · exact Or.inl hvA
      right
      by_cases hv0 : localSpace Q v=⊥
      · exact Or.inl (Finset.mem_filter.mpr ⟨hv,hv0⟩)
      right
      by_cases hvE : v∈E
      · exact Or.inl hvE
      exact Or.inr (hcover v hv hvA hv0 hvE))
  dsimp only at hc
  have hs : (∑c,(s c).length)≤2*(Q.cutEdges A).card*258*(bad+3) := by
    calc
      _ ≤ ∑_c : Fin n,258*(bad+3) := Finset.sum_le_sum fun c _ => hshort c
      _ = n*(258*(bad+3)) := by simp
      _ ≤ _ := by nlinarith
  apply PackingSelection.packing_count marks.card A.card (Q.cutEdges A).card d bad hd hA hcut
  change Z.card≤1 at hzero
  omega

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingCoverCount
