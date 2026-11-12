import Erdos1016.ExactMaximum.NetJoin
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# Physical mixed-tile chains, capped ladders, and rings

Each tile has distinct physical edge labels and two Bool-indexed port pairs.
A rung shares its left and right pair. A square keeps these pairs disjoint.
The same tile coordinates define chains, capped ladders, and closed rings.
-/

noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedTiles
open BoundaryTrace BoundaryTrace.Network

/-- The two tile kinds in the paper. -/
inductive Kind where
  | rung
  | square
  deriving DecidableEq, Fintype

namespace Kind

/-- A rung has one rail position; a square has two. -/
def weight : Kind → ℕ
  | rung => 1
  | square => 2

/-- Local physical vertices. The first square coordinate selects its side. -/
abbrev Vertex : Kind → Type
  | rung => Bool
  | square => Bool × Bool

/-- Local physical edge labels. -/
abbrev Edge : Kind → Type
  | rung => Unit
  | square => Bool × Bool

instance (t : Kind) : Fintype t.Vertex := by cases t <;> infer_instance
instance (t : Kind) : Fintype t.Edge := by cases t <;> infer_instance
instance (t : Kind) : DecidableEq t.Vertex := by cases t <;> infer_instance
instance (t : Kind) : DecidableEq t.Edge := by cases t <;> infer_instance

/-- The left port pair. -/
def left : (t : Kind) → Bool → t.Vertex
  | rung, b => b
  | square, b => (false,b)

/-- The right port pair. -/
def right : (t : Kind) → Bool → t.Vertex
  | rung, b => b
  | square, b => (true,b)

/-- The first end of a local edge. -/
def src : (t : Kind) → t.Edge → t.Vertex
  | rung, _ => false
  | square, e => (false,e.1)

/-- The second end of a local edge. -/
def dst : (t : Kind) → t.Edge → t.Vertex
  | rung, _ => true
  | square, e => (true,e.2)

theorem src_ne_dst (t : Kind) (e : t.Edge) : t.src e ≠ t.dst e := by
  cases t with
  | rung => exact Bool.false_ne_true
  | square => exact fun h => Bool.false_ne_true (congrArg Prod.fst h)

/-- The actual local network, with all edge labels retained. -/
def network (t : Kind) : Network t.Vertex t.Edge where
  src := t.src
  dst := t.dst
  noLoops := t.src_ne_dst

theorem left_injective (t : Kind) : Function.Injective t.left := by
  cases t with
  | rung => exact fun _ _ h => h
  | square => exact fun _ _ h => congrArg Prod.snd h

theorem right_injective (t : Kind) : Function.Injective t.right := by
  cases t with
  | rung => exact fun _ _ h => h
  | square => exact fun _ _ h => congrArg Prod.snd h

theorem vertex_card (t : Kind) : Fintype.card t.Vertex = 2*t.weight := by
  cases t <;> norm_num [Vertex,weight]

theorem edge_card (t : Kind) : Fintype.card t.Edge+2 = 3*t.weight := by
  cases t <;> norm_num [Edge,weight]

theorem weight_pos (t : Kind) : 1 ≤ t.weight := by cases t <;> decide

theorem weight_le_two (t : Kind) : t.weight ≤ 2 := by cases t <;> decide

end Kind

variable {k : ℕ}

/-- Vertices of a nonempty sequence of disjoint tiles. -/
abbrev Vertex (T : Fin (k+1) → Kind) := (i : Fin (k+1)) × (T i).Vertex

/-- The physical labels inside the tiles. -/
abbrev InnerEdge (T : Fin (k+1) → Kind) := (i : Fin (k+1)) × (T i).Edge

/-- Local labels and the two labels at each chain interface. -/
abbrev ChainEdge (T : Fin (k+1) → Kind) := InnerEdge T ⊕ (Fin k × Bool)

/-- The global left port of a tile. -/
def left (T : Fin (k+1) → Kind) (i : Fin (k+1)) (b : Bool) : Vertex T :=
  ⟨i,(T i).left b⟩

/-- The global right port of a tile. -/
def right (T : Fin (k+1) → Kind) (i : Fin (k+1)) (b : Bool) : Vertex T :=
  ⟨i,(T i).right b⟩

/-- A local edge retains its tile index. -/
def inner (T : Fin (k+1) → Kind) (i : Fin (k+1)) (e : (T i).Edge) : ChainEdge T :=
  Sum.inl ⟨i,e⟩

/-- An interface label joins corresponding rails of consecutive tiles. -/
def link (T : Fin (k+1) → Kind) (i : Fin k) (b : Bool) : ChainEdge T :=
  Sum.inr (i,b)

def chainSrc (T : Fin (k+1) → Kind) : ChainEdge T → Vertex T
  | Sum.inl ⟨i,e⟩ => ⟨i,(T i).src e⟩
  | Sum.inr (i,b) => right T i.castSucc b

def chainDst (T : Fin (k+1) → Kind) : ChainEdge T → Vertex T
  | Sum.inl ⟨i,e⟩ => ⟨i,(T i).dst e⟩
  | Sum.inr (i,b) => left T i.succ b

theorem chainSrc_ne_chainDst (T : Fin (k+1) → Kind) (e : ChainEdge T) :
    chainSrc T e ≠ chainDst T e := by
  rcases e with ⟨i,e⟩ | ⟨i,b⟩
  · intro h
    have he : (T i).src e = (T i).dst e := by simpa [chainSrc,chainDst] using h
    exact (T i).src_ne_dst e he
  · intro h
    have hi := congrArg Sigma.fst h
    have he : i.castSucc = i.succ := hi
    exact (ne_of_lt (Fin.castSucc_lt_succ i)) he

/-- The physical chain with corresponding-rail interfaces. -/
def chain (T : Fin (k+1) → Kind) : Network (Vertex T) (ChainEdge T) where
  src := chainSrc T
  dst := chainDst T
  noLoops := chainSrc_ne_chainDst T

theorem joins_inner (T : Fin (k+1) → Kind) (i : Fin (k+1)) (e : (T i).Edge) :
    (chain T).Joins (inner T i e) ⟨i,(T i).src e⟩ ⟨i,(T i).dst e⟩ :=
  Or.inl ⟨rfl,rfl⟩

theorem joins_link (T : Fin (k+1) → Kind) (i : Fin k) (b : Bool) :
    (chain T).Joins (link T i b) (right T i.castSucc b) (left T i.succ b) :=
  Or.inl ⟨rfl,rfl⟩

/-- Two new vertices cap the chain. -/
abbrev CappedVertex (T : Fin (k+1) → Kind) := Vertex T ⊕ Bool

/-- The capped chain keeps its old labels and adds two labels at each cap. -/
abbrev CappedEdge (T : Fin (k+1) → Kind) := ChainEdge T ⊕ (Bool ⊕ Bool)

def cappedSrc (T : Fin (k+1) → Kind) : CappedEdge T → CappedVertex T
  | Sum.inl e => Sum.inl ((chain T).src e)
  | Sum.inr (Sum.inl _) => Sum.inr false
  | Sum.inr (Sum.inr b) => Sum.inl (right T (Fin.last k) b)

def cappedDst (T : Fin (k+1) → Kind) : CappedEdge T → CappedVertex T
  | Sum.inl e => Sum.inl ((chain T).dst e)
  | Sum.inr (Sum.inl b) => Sum.inl (left T 0 b)
  | Sum.inr (Sum.inr _) => Sum.inr true

theorem cappedSrc_ne_cappedDst (T : Fin (k+1) → Kind) (e : CappedEdge T) :
    cappedSrc T e ≠ cappedDst T e := by
  rcases e with e | b | b
  · intro h
    exact (chain T).noLoops e (Sum.inl.inj h)
  · simp [cappedSrc,cappedDst]
  · simp [cappedSrc,cappedDst]

/-- The actual capped ladder on the mixed tile sequence. -/
def capped (T : Fin (k+1) → Kind) : Network (CappedVertex T) (CappedEdge T) where
  src := cappedSrc T
  dst := cappedDst T
  noLoops := cappedSrc_ne_cappedDst T

/-- A ring adds two closing labels to the chain. -/
abbrev RingEdge (T : Fin (k+1) → Kind) := ChainEdge T ⊕ Bool

def ringSrc (T : Fin (k+1) → Kind) : RingEdge T → Vertex T
  | Sum.inl e => (chain T).src e
  | Sum.inr b => right T (Fin.last k) b

def ringDst (T : Fin (k+1) → Kind) (twist : Equiv.Perm Bool) : RingEdge T → Vertex T
  | Sum.inl e => (chain T).dst e
  | Sum.inr b => left T 0 (twist b)

theorem ringSrc_ne_ringDst (T : Fin (k+1) → Kind) (hk : 1 ≤ k)
    (twist : Equiv.Perm Bool) (e : RingEdge T) : ringSrc T e ≠ ringDst T twist e := by
  rcases e with e | b
  · exact (chain T).noLoops e
  · intro h
    have hi := congrArg Sigma.fst h
    have he : (Fin.last k : Fin (k+1)) = 0 := hi
    have he' := congrArg Fin.val he
    simp only [Fin.val_last,Fin.val_zero] at he'
    omega

/-- A physical ring with at least two tiles and an explicit closing twist. -/
def ring (T : Fin (k+1) → Kind) (hk : 1 ≤ k) (twist : Equiv.Perm Bool) :
    Network (Vertex T) (RingEdge T) where
  src := ringSrc T
  dst := ringDst T twist
  noLoops := ringSrc_ne_ringDst T hk twist

/-- Total tile weight. -/
def weight (T : Fin (k+1) → Kind) : ℕ := ∑ i, (T i).weight

/-- Number of square tiles. -/
def squares (T : Fin (k+1) → Kind) : ℕ :=
  (Finset.univ.filter fun i => T i = Kind.square).card

/-- Number of single rungs. -/
def rungs (T : Fin (k+1) → Kind) : ℕ :=
  (Finset.univ.filter fun i => T i = Kind.rung).card

/-- The two tile counts partition the sequence. -/
theorem squares_add_rungs (T : Fin (k+1) → Kind) : squares T+rungs T=k+1 := by
  unfold squares rungs
  rw [Finset.card_filter,Finset.card_filter,← Finset.sum_add_distrib]
  calc
    (∑ i : Fin (k+1), ((if T i=Kind.square then 1 else 0) +
      (if T i=Kind.rung then 1 else 0))) = ∑ _ : Fin (k+1), 1 := by
        apply Finset.sum_congr rfl
        intro i _
        cases T i <;> simp
    _ = k+1 := by simp

/-- The weight is twice the number of squares plus the number of rungs. -/
theorem weight_eq (T : Fin (k+1) → Kind) : weight T=2*squares T+rungs T := by
  unfold weight squares rungs
  rw [Finset.card_filter,Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases T i <;> simp [Kind.weight]

/-- Exact physical vertex count of the chain and ring. -/
theorem vertex_card (T : Fin (k+1) → Kind) : Fintype.card (Vertex T)=2*weight T := by
  rw [Fintype.card_sigma]
  simp_rw [Kind.vertex_card]
  exact (Finset.mul_sum _ _ _).symm

/-- Exact chain edge count, stated without truncated subtraction. -/
theorem chain_edge_card (T : Fin (k+1) → Kind) :
    Fintype.card (ChainEdge T)+2=3*weight T := by
  rw [Fintype.card_sum,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  have h : (∑ i : Fin (k+1), (Fintype.card (T i).Edge+2))=3*weight T := by
    simp_rw [Kind.edge_card]
    exact (Finset.mul_sum _ _ _).symm
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  omega

/-- Capping adds exactly two vertices. -/
theorem capped_vertex_card (T : Fin (k+1) → Kind) :
    Fintype.card (CappedVertex T)=2*weight T+2 := by
  rw [Fintype.card_sum,Fintype.card_bool,vertex_card]

/-- Capping adds exactly four physical labels. -/
theorem capped_edge_card (T : Fin (k+1) → Kind) :
    Fintype.card (CappedEdge T)=3*weight T+2 := by
  rw [Fintype.card_sum]
  rw [show Fintype.card (Bool ⊕ Bool)=4 by simp]
  have h := chain_edge_card T
  omega

/-- Closing adds exactly two physical labels. -/
theorem ring_edge_card (T : Fin (k+1) → Kind) :
    Fintype.card (RingEdge T)=3*weight T := by
  rw [Fintype.card_sum,Fintype.card_bool]
  exact chain_edge_card T

end Erdos1016.ExactMaximumSupport.MixedTiles
