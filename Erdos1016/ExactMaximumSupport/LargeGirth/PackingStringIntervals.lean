import Erdos1016.ExactMaximumSupport.LargeGirth.TerminalStrings

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Deterministic packets along an actual terminal string

A packet uses 258 ordered marked vertices. Its first and last vertices are
endpoints; the other 256 vertices lie in the actual between-region.
Successive packets have nonoverlapping endpoints. OrderedString supplies
connectedness, the physical endpoint boundary, and disjointness in the
original graph.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringIntervals
open TerminalStrings
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {B R : Finset V}
local instance packetDecidable (p : Prop) : Decidable p := Classical.propDecidable p

variable (s : OrderedString G B R) (m : ℕ) (hlen : 258*m ≤ s.length)

/-- First marked vertex in packet b. -/
def leftIndex (b : Fin m) : Fin s.length := ⟨258*b.val, by have := b.isLt; omega⟩

/-- Last marked vertex in packet b. -/
def rightIndex (b : Fin m) : Fin s.length := ⟨258*b.val+257, by have := b.isLt; omega⟩

/-- The 256 strict interior marked vertices of packet b. -/
def middleIndex (b : Fin m) (t : Fin 256) : Fin s.length :=
  ⟨258*b.val+1+t.val, by have := b.isLt; have := t.isLt; omega⟩

theorem index_gap (b : Fin m) :
    (leftIndex s m hlen b).val+2 ≤ (rightIndex s m hlen b).val := by
  simp only [leftIndex, rightIndex]
  omega

theorem middle_between (b : Fin m) (t : Fin 256) :
    leftIndex s m hlen b < middleIndex s m hlen b t ∧
      middleIndex s m hlen b t < rightIndex s m hlen b := by
  change 258*b.val < 258*b.val+1+t.val ∧ 258*b.val+1+t.val < 258*b.val+257
  have := t.isLt
  omega

theorem ordered_endpoints {b c : Fin m} (hbc : b < c) :
    rightIndex s m hlen b ≤ leftIndex s m hlen c := by
  change 258*b.val+257 ≤ 258*c.val
  have : b.val < c.val := hbc
  omega

/-- The region is the one supplied by the original-graph string geometry. -/
def interval (b : Fin m) : Finset V :=
  s.region (leftIndex s m hlen b) (rightIndex s m hlen b) (index_gap s m hlen b)

/-- The explicit marked vertices inside each packet. -/
def interiorVertex (b : Fin m) (t : Fin 256) : V :=
  s.vertex (middleIndex s m hlen b t)

theorem interior_injective (b : Fin m) :
    Function.Injective (interiorVertex s m hlen b) := by
  intro t u he
  have hh := congrArg Fin.val (s.injective he)
  apply Fin.ext
  change 258*b.val+1+t.val = 258*b.val+1+u.val at hh
  omega

theorem interior_relevant (b : Fin m) (t : Fin 256) :
    interiorVertex s m hlen b t ∈ R := s.relevant _

theorem interior_mem (b : Fin m) (t : Fin 256) :
    interiorVertex s m hlen b t ∈ interval s m hlen b := by
  exact s.between _ _ _ _ (middle_between s m hlen b t).1
    (middle_between s m hlen b t).2

theorem interval_connected (b : Fin m) :
    (G.induce (↑(interval s m hlen b) : Set V)).Connected := s.connected _ _ _

theorem interval_no_feet (b : Fin m) : Disjoint (interval s m hlen b) B := s.no_feet _ _ _

theorem interval_avoids (b : Fin m) :
    s.vertex (leftIndex s m hlen b) ∉ interval s m hlen b ∧
      s.vertex (rightIndex s m hlen b) ∉ interval s m hlen b := s.avoids _ _ _

theorem interval_boundary (b : Fin m) {u w : V}
    (hu : u ∈ interval s m hlen b) (huw : G.Adj u w)
    (hw : w ∉ interval s m hlen b) :
    w = s.vertex (leftIndex s m hlen b) ∨ w = s.vertex (rightIndex s m hlen b) :=
  s.boundary _ _ _ u hu w huw hw

theorem intervals_disjoint : Pairwise (fun b c =>
    Disjoint (interval s m hlen b) (interval s m hlen c)) := by
  intro b c hbc
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact s.disjoint _ _ _ _ _ _ (ordered_endpoints s m hlen hlt)
  · exact (s.disjoint _ _ _ _ _ _ (ordered_endpoints s m hlen hgt)).symm

/-- At least 256 distinct relevant marks lie in each actual interval. -/
theorem relevant_card_ge (b : Fin m) :
    256 ≤ ((interval s m hlen b).filter fun v => v ∈ R).card := by
  let f : Fin 256 → {v // v ∈ (interval s m hlen b).filter fun v => v ∈ R} :=
    fun t => ⟨interiorVertex s m hlen b t,
      Finset.mem_filter.mpr ⟨interior_mem s m hlen b t, interior_relevant s m hlen b t⟩⟩
  have hf : Function.Injective f := by
    intro t u he
    exact interior_injective s m hlen b (congrArg Subtype.val he)
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

include s hlen in
/-- Finite interface for lifting the selected packets to the ambient graph. -/
theorem exists_intervals :
    ∃ (X : Fin m → Finset V) (l r : Fin m → V),
      Pairwise (fun b c => Disjoint (X b) (X c)) ∧
      (∀ b, (G.induce (↑(X b) : Set V)).Connected) ∧
      (∀ b, Disjoint (X b) B) ∧
      (∀ b, l b ∈ R ∧ r b ∈ R ∧ l b ∉ X b ∧ r b ∉ X b) ∧
      (∀ b, ∀ u ∈ X b, ∀ w, G.Adj u w → w ∉ X b → w=l b ∨ w=r b) ∧
      (∀ b, ∃ f : Fin 256 → V, Function.Injective f ∧ ∀ t, f t ∈ R ∧ f t ∈ X b) := by
  refine ⟨interval s m hlen, (fun b => s.vertex (leftIndex s m hlen b)),
    (fun b => s.vertex (rightIndex s m hlen b)), intervals_disjoint s m hlen,
    interval_connected s m hlen, interval_no_feet s m hlen, ?_, ?_, ?_⟩
  · intro b
    exact ⟨s.relevant _, s.relevant _, (interval_avoids s m hlen b).1,
      (interval_avoids s m hlen b).2⟩
  · intro b u hu w huw hw
    exact interval_boundary s m hlen b hu huw hw
  · intro b
    exact ⟨interiorVertex s m hlen b, interior_injective s m hlen b,
      fun t => ⟨interior_relevant s m hlen b t, interior_mem s m hlen b t⟩⟩

end Erdos1016.ExactMaximumSupport.LargeGirth.PackingStringIntervals
