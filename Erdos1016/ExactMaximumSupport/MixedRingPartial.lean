import Erdos1016.ExactMaximumSupport.MixedRingIntervals
import Erdos1016.ExactMaximumSupport.RingOmegaArcs

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# The partial even sector of a physical mixed ring

An unused interface opens the cycle into its derived tile interval.
The exact endpoint arcs cover every such cycle and give the finite weighted sum.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

variable {k : ℕ} (T : Fin (k+1) → Kind)

/-- A cyclic arc becomes an ordinary interval when its endpoints are in opened order. -/
theorem mem_arc_iff_levels (c i j q : Fin (k+1))
    (hij : tileLevel c i≤tileLevel c j) :
    q∈RingOmega.closedArc i j ↔ tileLevel c i≤tileLevel c q ∧ tileLevel c q≤tileLevel c j := by
  rw [RingOmega.mem_closedArc_iff]
  have := c.isLt
  have := i.isLt
  have := j.isLt
  have := q.isLt
  by_cases hi : i.val≤c.val <;> by_cases hj : j.val≤c.val <;> by_cases hq : q.val≤c.val <;>
    simp only [tileLevel,hi,hj,hq,if_true,if_false] at hij ⊢ <;> split_ifs <;> omega

/-- Active interfaces are the same arc with its last tile removed. -/
theorem active_arc_iff_levels (c i j q : Fin (k+1))
    (hij : tileLevel c i<tileLevel c j) :
    (q∈RingOmega.closedArc i j ∧ q≠j) ↔
      tileLevel c i≤tileLevel c q ∧ tileLevel c q<tileLevel c j := by
  rw [mem_arc_iff_levels c i j q (le_of_lt hij)]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hne⟩
    refine ⟨hlo,lt_of_le_of_ne hhi ?_⟩
    exact fun h => hne (tileLevel_injective c h)
  · rintro ⟨hlo,hhi⟩
    exact ⟨⟨hlo,le_of_lt hhi⟩,fun h => (ne_of_lt hhi) (congrArg (tileLevel c) h)⟩

/-- The common physical value on an active or inactive interface. -/
def arcValue (i j q : Fin (k+1)) : Bit :=
  if q∈RingOmega.closedArc i j ∧ q≠j then 1 else 0

/-- The actual cycle sector with some used and some unused even interfaces. -/
def IsPartialEvenCycle (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) : Prop :=
  (ring T hk twist).IsCycleWord z ∧ HasEvenInterfaces T z ∧
    (∃ q b,z (interfaceEdge T q b)≠0) ∧ ∃ c,∀ b,z (interfaceEdge T c b)=0

/-- Each partial even-sector cycle has distinct actual endpoint tiles. -/
theorem exists_active_arc (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (z : (ring T hk twist).Word) (hz : IsPartialEvenCycle T hk twist z) :
    ∃ i j : Fin (k+1),i≠j ∧ WithinTiles T (RingOmega.closedArc i j) z ∧
      ∀ q b,z (interfaceEdge T q b)=arcValue i j q := by
  obtain ⟨c,hcut⟩ := hz.2.2.2
  obtain ⟨i,j,hlt,hne,hwithin,hpattern⟩ :=
    exists_active_interval T hk twist z hz.1 hz.2.1 c hcut hz.2.2.1
  have hset : (Finset.univ.filter fun q =>
      tileLevel c i≤tileLevel c q ∧ tileLevel c q≤tileLevel c j)=RingOmega.closedArc i j := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (mem_arc_iff_levels c i j q (le_of_lt hlt)).symm
  refine ⟨i,j,hne,by simpa only [hset] using hwithin,?_⟩
  intro q b
  rw [hpattern]
  simp only [arcValue,active_arc_iff_levels c i j q hlt]

/-- A fixed endpoint arc prescribes every interface and allows only its own tile labels. -/
def HasArcPattern (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (i j : Fin (k+1)) (z : (ring T hk twist).Word) : Prop :=
  (ring T hk twist).IsCycleWord z ∧
    (∀ q b,z (interfaceEdge T q b)=arcValue i j q) ∧
    WithinTiles T (RingOmega.closedArc i j) z

/-- The cycle count of one actual arc is at most one bit per square in that arc. -/
theorem arc_pattern_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool)
    (i j : Fin (k+1)) :
    Nat.card {z : (ring T hk twist).Word // HasArcPattern T hk twist i j z} ≤
      2^(RingOmega.squareCount (Finset.univ.filter fun q => T q=Kind.square) i j) := by
  classical
  let I := RingOmega.closedArc i j
  let links : Fin k → Bool → Bit := fun q _ => arcValue i j q.castSucc
  let closing : Bool → Bit := fun _ => arcValue i j (Fin.last k)
  let f : {z : (ring T hk twist).Word // HasArcPattern T hk twist i j z} →
      {z : (ring T hk twist).Word // (ring T hk twist).IsCycleWord z ∧
        (∀ q b,z (Sum.inl (link T q b))=links q b) ∧
        (∀ b,z (Sum.inr b)=closing b) ∧ WithinTiles T I z} := fun z =>
    ⟨z.1,z.2.1,(fun q b => by simpa only [interfaceEdge_castSucc] using z.2.2.1 q.castSucc b),
      (fun b => by simpa only [interfaceEdge_last] using z.2.2.1 (Fin.last k) b),z.2.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    exact hh
  have hbound := (Nat.card_le_card_of_injective f hf).trans
    (fixed_interface_cycles_card_le T hk twist I links closing)
  have hset : I.filter (fun q => T q=Kind.square)=
      (Finset.univ.filter fun q => T q=Kind.square) ∩ RingOmega.closedArc i j := by
    ext q
    simp only [I,Finset.mem_filter,Finset.mem_inter,Finset.mem_univ,true_and]
    tauto
  simpa only [hset,RingOmega.squareCount] using hbound

/-- All partial even-sector cycles are bounded by the paper's literal cyclic weighted sum. -/
theorem partial_even_cycles_card_le (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Nat.card {z : (ring T hk twist).Word // IsPartialEvenCycle T hk twist z} ≤
      RingOmega.partialSum (Finset.univ.filter fun q => T q=Kind.square) := by
  classical
  let S := Finset.univ.filter (IsPartialEvenCycle T hk twist)
  let F (i j : Fin (k+1)) := Finset.univ.filter (HasArcPattern T hk twist i j)
  have hcover : S ⊆ Finset.univ.biUnion
      (fun i => (Finset.univ.erase i).biUnion (F i)) := by
    intro z hz
    obtain ⟨i,j,hne,hw,hp⟩ := exists_active_arc T hk twist z (Finset.mem_filter.mp hz).2
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,?_,?_⟩⟩
    · exact Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_univ _⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2.1,hp,hw⟩
  calc
    Nat.card {z : (ring T hk twist).Word // IsPartialEvenCycle T hk twist z}=S.card :=
      natCard_subtype_eq_card_filter _
    _ ≤ (Finset.univ.biUnion (fun i => (Finset.univ.erase i).biUnion (F i))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ i : Fin (k+1),((Finset.univ.erase i).biUnion (F i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin (k+1),∑ j ∈ Finset.univ.erase i,(F i j).card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_biUnion_le
    _ ≤ ∑ i : Fin (k+1),∑ j ∈ Finset.univ.erase i,
        2^(RingOmega.squareCount (Finset.univ.filter fun q => T q=Kind.square) i j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [F,←natCard_subtype_eq_card_filter] using arc_pattern_cycles_card_le T hk twist i j
    _ = _ := rfl

end Erdos1016.ExactMaximumSupport.MixedTiles
