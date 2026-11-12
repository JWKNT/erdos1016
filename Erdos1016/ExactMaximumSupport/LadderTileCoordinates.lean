import Erdos1016.ExactMaximumSupport.LadderTileOrder

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Physical vertex coordinates of the canonical ladder tiles

Each canonical tile retains its actual rail positions and its two rails.
Disjointness and coverage of the permutation blocks give an exact vertex equivalence.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.LadderTileCoordinates
open LadderPermutation LadderTileOrder MixedTiles
variable {n : ℕ}

/-- Local coordinates use the actual start and its matched position. -/
def localMap (a b : Fin n) : (t : Kind) → t.Vertex → Fin n × Bool
  | .rung,x => (a,x)
  | .square,x => (if x.1 then b else a,x.2)

/-- The original rail position and rail of a vertex in a canonical tile. -/
def coordinate (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card) :
    (kind π i).Vertex → Fin n × Bool :=
  localMap (start π i) (π (start π i)) (kind π i)

/-- A rung corresponds exactly to a fixed point of the actual permutation. -/
theorem rung_fixed (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card)
    (hi : kind π i = .rung) : π (start π i) = start π i := by
  by_contra h
  simp [kind,h] at hi

/-- A square has two distinct actual rail positions. -/
theorem square_moved (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card)
    (hi : kind π i = .square) : π (start π i) ≠ start π i := by
  intro h
  simp [kind,h] at hi

/-- Every local coordinate lies in its actual canonical block. -/
theorem coordinate_mem (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card)
    (x : (kind π i).Vertex) : (coordinate π i x).1 ∈ tile π (start π i) := by
  unfold coordinate
  generalize hk : kind π i = t at x ⊢
  cases t with
  | rung => simp [localMap,tile]
  | square => rcases x with ⟨b,c⟩; cases b <;> simp [localMap,tile]

/-- A local tile map is injective on its physical vertices. -/
theorem coordinate_injective (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card) :
    Function.Injective (coordinate π i) := by
  have hmove := square_moved π i
  intro x y h
  unfold coordinate at h
  generalize hk : kind π i = t at x y h
  cases t with
  | rung => exact congrArg Prod.snd h
  | square =>
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    have hne := hmove hk
    cases a <;> cases c
    all_goals simp only [localMap,Bool.false_eq_true,if_false,if_true,Prod.mk.injEq] at h
    · exact Prod.ext rfl h.2
    · exact (hne h.1.symm).elim
    · exact (hne h.1).elim
    · exact Prod.ext rfl h.2

/-- Every rail vertex of the block has a physical vertex in that tile. -/
theorem coordinate_covers (π : Equiv.Perm (Fin n)) (i : Fin (tileStarts π).card)
    (j : Fin n) (b : Bool) (hj : j ∈ tile π (start π i)) :
    ∃ x : (kind π i).Vertex, coordinate π i x = (j,b) := by
  have hfixed := rung_fixed π i
  unfold coordinate
  generalize hk : kind π i = t
  cases t with
  | rung =>
    have hfix := hfixed hk
    have he : j = start π i := by simpa [tile,hfix] using hj
    exact ⟨b,by rw [he]; rfl⟩
  | square =>
    simp only [tile,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨(false,b),rfl⟩
    · exact ⟨(true,b),rfl⟩

/-- Assemble local coordinates without losing the physical tile index. -/
def vertexMap (π : Equiv.Perm (Fin n)) :
    ((i : Fin (tileStarts π).card) × (kind π i).Vertex) → Fin n × Bool :=
  fun x => coordinate π x.1 x.2

/-- Distinct blocks and distinct local vertices have distinct rail coordinates. -/
theorem vertexMap_injective {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    Function.Injective (vertexMap π) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hp : (coordinate π i x).1 = (coordinate π j y).1 := congrArg Prod.fst h
  have hij : i = j := by
    by_contra hne
    have hsne : start π i ≠ start π j := fun hh => hne ((start π).injective hh)
    have hd := tiles_pairwise_disjoint hπ (start_mem π i) (start_mem π j) hsne
    exact Finset.disjoint_left.mp hd (coordinate_mem π i x) (hp.symm ▸ coordinate_mem π j y)
  subst j
  exact congrArg (Sigma.mk i) (coordinate_injective π i h)

/-- Every actual rail coordinate is supplied by a canonical physical tile. -/
theorem vertexMap_surjective {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    Function.Surjective (vertexMap π) := by
  rintro ⟨j,b⟩
  have hmem : j ∈ (tileStarts π).biUnion (tile π) := by rw [tiles_cover hπ]; simp
  obtain ⟨a,ha,hja⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨i,rfl⟩ := exists_start π ha
  obtain ⟨x,hx⟩ := coordinate_covers π i j b hja
  exact ⟨⟨i,x⟩,hx⟩

/-- The canonical tiles and the actual ordered rail vertices are equivalent. -/
def vertexEquiv {π : Equiv.Perm (Fin n)} (hπ : AvoidsLadderPatterns π) :
    ((i : Fin (tileStarts π).card) × (kind π i).Vertex) ≃ Fin n × Bool :=
  Equiv.ofBijective (vertexMap π) ⟨vertexMap_injective hπ,vertexMap_surjective hπ⟩

end Erdos1016.ExactMaximumSupport.LadderTileCoordinates
