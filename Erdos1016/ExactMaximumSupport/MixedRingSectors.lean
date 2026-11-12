import Erdos1016.ExactMaximumSupport.MixedRingPartial
import Erdos1016.ExactMaximumSupport.MixedRingLocalCycles

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The four physical cycle sectors of a mixed ring

Three sectors have derived counting bounds.
The all-interface sector remains an explicit actual cycle count in the main ledger.
The coarser local-fiber bound for that count does not claim the required halving result.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- Both physical labels are used at every interface. -/
def HasFullInterfaces (z : RingEdge T → Bit) : Prop :=
  ∀ q b,z (interfaceEdge T q b)=1

/-- Every actual ring cycle belongs to one of the four sectors in the paper. -/
theorem cycle_sector_cases (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : (ring T hk twist).IsCycleWord z) :
    HasOddInterfaces T z ∨ HasZeroInterfaces T z ∨ HasFullInterfaces T z ∨
      IsPartialEvenCycle T hk twist z := by
  rcases even_or_odd_interfaces T hk twist z hz.boundary_eq_zero with heven | hodd
  · by_cases hfull : HasFullInterfaces T z
    · exact Or.inr (Or.inr (Or.inl hfull))
    · have hunused : ∃ c,∀ b,z (interfaceEdge T c b)=0 := by
        by_contra h
        push_neg at h
        apply hfull
        intro q b
        rcases even_interface_dichotomy T z heven q with hzero | hone
        · obtain ⟨a,ha⟩ := h q
          exact False.elim (ha (hzero a))
        · exact hone b
      by_cases hused : ∃ q b,z (interfaceEdge T q b)≠0
      · exact Or.inr (Or.inr (Or.inr ⟨hz,heven,hused,hunused⟩))
      · have hzero : ∀ q b,z (interfaceEdge T q b)=0 := by
          intro q b
          by_contra h
          exact hused ⟨q,b,h⟩
        exact Or.inr (Or.inl ⟨(fun i b => by
          simpa only [interfaceEdge_castSucc] using hzero i.castSucc b),
          (fun b => by simpa only [interfaceEdge_last] using hzero (Fin.last k) b)⟩)
  · exact Or.inl hodd

/-- A coarse all-interface bound follows from the proved local fiber estimate. -/
theorem full_interface_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z} ≤ 2^(squares T) := by
  classical
  let f : {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z} →
      {z : (ring T hk twist).Word // (ring T hk twist).IsCycleWord z ∧
        (∀ i b,z (Sum.inl (link T i b))=1) ∧
        (∀ b,z (Sum.inr b)=1) ∧ WithinTiles T Finset.univ z} := fun z =>
    ⟨z.1,z.2.1,(fun i b => by simpa only [interfaceEdge_castSucc] using z.2.2 i.castSucc b),
      (fun b => by simpa only [interfaceEdge_last] using z.2.2 (Fin.last k) b),
      (fun i hi => False.elim (hi (Finset.mem_univ i)))⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh
  have hb := (Nat.card_le_card_of_injective f hf).trans
    (fixed_interface_cycles_card_le T hk twist Finset.univ (fun _ _ => 1) (fun _ => 1))
  simpa only [squares] using hb

/-- The complete sector ledger retains only the actual all-interface count unresolved. -/
theorem numCycles_le_sector_ledger (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    (ring T hk twist).numCycles ≤ 2^(weight T)+squares T+
      Nat.card {z : (ring T hk twist).Word //
        (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z}+
      RingOmega.partialSum (Finset.univ.filter fun q => T q=Kind.square) := by
  classical
  let C := Finset.univ.filter (ring T hk twist).IsCycleWord
  let O := Finset.univ.filter fun z => (ring T hk twist).IsCycleWord z ∧ HasOddInterfaces T z
  let L := Finset.univ.filter fun z => (ring T hk twist).IsCycleWord z ∧ HasZeroInterfaces T z
  let F := Finset.univ.filter fun z => (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z
  let P := Finset.univ.filter (IsPartialEvenCycle T hk twist)
  have hcover : C ⊆ ((O ∪ L) ∪ F) ∪ P := by
    intro z hz
    have hcycle := (Finset.mem_filter.mp hz).2
    rcases cycle_sector_cases T hk twist z hcycle with ho | hl | hf | hp
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcycle,ho⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcycle,hl⟩)))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcycle,hf⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
  have hc : C.card≤O.card+L.card+F.card+P.card := by
    have h0 := Finset.card_le_card hcover
    have h1 := Finset.card_union_le O L
    have h2 := Finset.card_union_le (O ∪ L) F
    have h3 := Finset.card_union_le ((O ∪ L) ∪ F) P
    omega
  have ho : O.card≤2^(weight T) := by
    have hh := odd_cycles_card_le T hk twist
    rw [natCard_subtype_eq_card_filter] at hh
    convert hh using 1
    congr 1
    ext z
    simp only [O,Finset.mem_filter,Finset.mem_univ,true_and]
  have hl : L.card≤squares T := by
    have hh := zero_interface_cycles_card_le T hk twist
    rw [natCard_subtype_eq_card_filter] at hh
    convert hh using 1
    congr 1
    ext z
    simp only [L,Finset.mem_filter,Finset.mem_univ,true_and]
  have hp : P.card≤RingOmega.partialSum (Finset.univ.filter fun q => T q=Kind.square) := by
    simpa only [P,natCard_subtype_eq_card_filter] using partial_even_cycles_card_le T hk twist
  have hC : (ring T hk twist).numCycles=C.card := natCard_subtype_eq_card_filter _
  have hF : Nat.card {z : (ring T hk twist).Word //
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z}=F.card := by
    have hh := natCard_subtype_eq_card_filter (fun z : (ring T hk twist).Word =>
      (ring T hk twist).IsCycleWord z ∧ HasFullInterfaces T z)
    convert hh using 1
    congr 1
    ext z
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [hC,hF]
  omega

end Erdos1016.ExactMaximumSupport.MixedTiles
