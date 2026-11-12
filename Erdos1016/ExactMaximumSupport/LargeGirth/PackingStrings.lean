import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings
import Erdos1016.ExactMaximumSupport.LargeGirth.PackingMarkedFamily

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Actual quotient strings from local parity relevance

The terminal strings live outside the selected vertices. Their interval
regions contain no feet, so their boundary statement holds in the full graph.
-/
noncomputable section
open scoped BigOperators
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingStrings
open PackingLocalSpaces TerminalStrings
local instance packingStringsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (Q : FiniteMultiGraph) (A : Finset Q.Vertex)
local instance packingOutsideDecidableEq : DecidableEq (Outside Q A) := Classical.decEq _

def ambient (M : Finset (Outside Q A)) : Finset Q.Vertex := M.image Subtype.val

@[simp] theorem mem_ambient (M : Finset (Outside Q A)) (v : Outside Q A) :
    v.1 ∈ ambient Q A M ↔ v ∈ M := by
  simp [ambient,v.2]

theorem ambient_connected (M : Finset (Outside Q A))
    (hM : ((exterior Q A).induce (↑M : Set (Outside Q A))).Connected) :
    (Q.toSimpleGraph.induce (↑(ambient Q A M) : Set Q.Vertex)).Connected := by
  let f : (exterior Q A).induce (↑M : Set (Outside Q A)) →g
      Q.toSimpleGraph.induce (↑(ambient Q A M) : Set Q.Vertex) :=
    { toFun := fun v => ⟨v.1.1, (mem_ambient Q A M v.1).mpr v.2⟩
      map_rel' := fun h => h }
  apply hM.map f
  intro v
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp v.2
  exact ⟨⟨w,hw⟩,Subtype.ext he⟩

/-- The no-feet condition removes every possible edge to the selected set. -/
def ambientString (R : Finset (Outside Q A))
    (s : OrderedString (exterior Q A) (feet Q A) R) :
    OrderedString Q.toSimpleGraph ∅ (ambient Q A R) where
  length := s.length
  vertex := fun i => (s.vertex i).1
  injective := fun i j h => s.injective (Subtype.ext h)
  relevant := fun i => (mem_ambient Q A R (s.vertex i)).mpr (s.relevant i)
  region := fun i j h => ambient Q A (s.region i j h)
  connected := fun i j h => ambient_connected Q A _ (s.connected i j h)
  no_feet := fun _ _ _ => Finset.disjoint_empty_right _
  avoids := by
    intro i j h
    simpa using s.avoids i j h
  between := by
    intro i j h k hik hkj
    exact (mem_ambient Q A _ _).mpr (s.between i j h k hik hkj)
  boundary := by
    intro i j h u hu w hadj hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have hwA : w∉A := by
      intro hwA
      have hf : v∈feet Q A := by
        simp only [feet,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨v.2,w,hwA,hadj⟩
      exact (Finset.disjoint_left.mp (s.no_feet i j h)) hv hf
    have hwM : (⟨w,hwA⟩ : Outside Q A)∉s.region i j h := by
      intro hm
      exact hw ((mem_ambient Q A _ ⟨w,hwA⟩).mpr hm)
    exact (s.boundary i j h v hv ⟨w,hwA⟩ hadj hwM).imp
      (congrArg Subtype.val) (congrArg Subtype.val)
  disjoint := by
    intro i j h k l h' hjk
    exact (Finset.disjoint_image Subtype.val_injective).mpr (s.disjoint i j h k l h' hjk)

/-- Every nonzero omitted mark lies on a bounded family of actual strings,
apart from a bounded exceptional set. -/
theorem exists_strings (marks : Finset Q.Vertex)
    (hrel : ∀v∈marks,v∉A→localSpace Q v=⊥ ∨ Relevant Q A v) :
    ∃E : Finset Q.Vertex,E⊆marks ∧ E.card≤2*(Q.cutEdges A).card ∧
      ∃n : ℕ,n≤2*(Q.cutEdges A).card ∧
        ∃s : Fin n→OrderedString Q.toSimpleGraph ∅ (marks\A),
          ∀v∈marks,v∉A→localSpace Q v≠⊥→v∉E→∃c i,(s c).vertex i=v := by
  let R : Finset (Outside Q A) := Finset.univ.filter fun v =>
    v.1∈marks ∧ localSpace Q v.1≠⊥
  have hr (v : Outside Q A) (hv : v∈R) (hfoot : v∉feet Q A) :
      2≤Nat.card (ExceptionalPartners.TerminalBranch (exterior Q A) (feet Q A) v) := by
    have hh := (Finset.mem_filter.mp hv).2
    apply relevant_terminalBranch_card Q A v
    · exact (hrel v.1 hh.1 v.2).resolve_left hh.2
    · intro hf
      exact hfoot (by simp [feet,hf])
  obtain ⟨E,hER,hE,n,hn,s,hs⟩ := TerminalStrings.exists_strings_of_card_le
    (exterior Q A) (feet Q A) R (Q.cutEdges A).card (feet_card_le_cut Q A) hr
  have hsub : ambient Q A (R\E) ⊆ marks\A := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hwR := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).2.1
    exact Finset.mem_sdiff.mpr ⟨hwR,w.2⟩
  let ss : Fin n → OrderedString Q.toSimpleGraph ∅ (marks\A) := fun c =>
    { ambientString Q A (R\E) (s c) with
      relevant := fun i => hsub ((ambientString Q A (R\E) (s c)).relevant i) }
  refine ⟨ambient Q A E,?_,(Finset.card_image_le).trans hE,n,hn,ss,?_⟩
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp (hER hw)).2.1
  · intro v hv hvA hv0 hvE
    let w : Outside Q A := ⟨v,hvA⟩
    have hwR : w∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,hv0⟩
    have hwE : w∉E := fun h => hvE ((mem_ambient Q A E w).mpr h)
    obtain ⟨c,i,hi⟩ := hs w hwR hwE
    exact ⟨c,i,congrArg Subtype.val hi⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingStrings
