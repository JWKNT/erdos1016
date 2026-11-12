import Erdos1016.ExactMaximumSupport.NetworkIso
import Erdos1016.ExactMaximumSupport.LadderPermutation

set_option autoImplicit false

/-!
# A physical ladder with an explicit matching permutation

Both ordered rails retain their physical labels. Matching labels join the two rails.
The zero-position model is the two-edge parallel pole.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PermutationLadder
open BoundaryTrace BoundaryTrace.Network

abbrev Vertex (n : ℕ) := (Fin n × Bool) ⊕ Bool
abbrev Edge (n : ℕ) := (Fin (n+1) × Bool) ⊕ Fin n

/-- The two cap vertices. -/
def left (n : ℕ) : Vertex n := Sum.inr false
def right (n : ℕ) : Vertex n := Sum.inr true

/-- A rail position includes both cap vertices. -/
def railVertex {n : ℕ} (i : Fin (n+2)) (b : Bool) : Vertex n :=
  Fin.cases (Sum.inr false)
    (fun j => Fin.lastCases (Sum.inr true) (fun h => Sum.inl (h,b)) j) i

@[simp] theorem railVertex_first {n : ℕ} (b : Bool) :
    railVertex (0 : Fin (n+2)) b=left n := rfl

@[simp] theorem railVertex_last {n : ℕ} (b : Bool) :
    railVertex (Fin.last (n+1)) b=right n := by
  have h : Fin.last (n+1)=(Fin.last n).succ := Fin.ext rfl
  rw [h]
  simp only [railVertex,Fin.cases_succ,Fin.lastCases_last,right]

@[simp] theorem railVertex_inner {n : ℕ} (i : Fin n) (b : Bool) :
    railVertex i.succ.castSucc b=Sum.inl (i,b) := by
  have h : i.succ.castSucc=i.castSucc.succ := rfl
  rw [h]
  simp [railVertex]

/-- The original linear position of a vertex on either rail. -/
def position {n : ℕ} : Vertex n → ℕ
  | Sum.inl (i,_) => i.val+1
  | Sum.inr false => 0
  | Sum.inr true => n+1

@[simp] theorem position_railVertex {n : ℕ} (i : Fin (n+2)) (b : Bool) :
    position (railVertex i b)=i.val := by
  cases i using Fin.cases with
  | zero => rfl
  | succ j =>
    cases j using Fin.lastCases with
    | last =>
      change position (railVertex (Fin.last (n+1)) b)=n+1
      rw [railVertex_last]
      rfl
    | cast i => simp [railVertex,position]

theorem railVertex_injective {n : ℕ} (b : Bool) : Function.Injective (fun i : Fin (n+2) => railVertex i b) := by
  intro i j hij
  apply Fin.ext
  simpa only [position_railVertex] using congrArg position hij

/-- Physical edge orientations in the canonical model. -/
def src {n : ℕ} (_π : Equiv.Perm (Fin n)) : Edge n → Vertex n
  | Sum.inl (i,b) => railVertex i.castSucc b
  | Sum.inr i => Sum.inl (i,false)

def dst {n : ℕ} (π : Equiv.Perm (Fin n)) : Edge n → Vertex n
  | Sum.inl (i,b) => railVertex i.succ b
  | Sum.inr i => Sum.inl (π i,true)

theorem src_ne_dst {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Edge n) : src π e≠dst π e := by
  rcases e with ⟨i,b⟩ | i
  · intro h
    have hi := railVertex_injective b h
    exact (ne_of_lt (Fin.castSucc_lt_succ i)) hi
  · intro h
    have hb : false=true := congrArg Prod.snd (Sum.inl.inj h)
    exact Bool.false_ne_true hb

/-- The actual loopless network with the specified physical matching. -/
def network {n : ℕ} (π : Equiv.Perm (Fin n)) : Network (Vertex n) (Edge n) where
  src := src π
  dst := dst π
  noLoops := src_ne_dst π

@[simp] theorem joins_rail {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin (n+1)) (b : Bool) :
    (network π).Joins (Sum.inl (i,b)) (railVertex i.castSucc b) (railVertex i.succ b) :=
  Or.inl ⟨rfl,rfl⟩

@[simp] theorem joins_matching {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (network π).Joins (Sum.inr i) (Sum.inl (i,false)) (Sum.inl (π i,true)) :=
  Or.inl ⟨rfl,rfl⟩

end Erdos1016.ExactMaximumSupport.PermutationLadder
