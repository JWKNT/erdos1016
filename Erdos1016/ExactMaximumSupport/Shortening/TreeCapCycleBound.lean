import Erdos1016.ExactMaximumSupport.FourPoleCaps
import Erdos1016.ExactMaximum.CycleBoundMargin

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# A cubic tree cap bounds all four-pole states at once

Three degree-two vertex additions implement the tree cap with its central
edge subdivided. Old cycles, six path families, and two disjoint-path families
inject into its cycles. The rank grows by at most three.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.TreeCapCycleBound
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- Old cycles and paths closed through the new vertex give disjoint cycle families. -/
theorem cycles_add_paths_le (a b : V) :
    N.numCycles+N.numPaths a b≤(N.addVertex a b).numCycles := by
  classical
  let R := N.addVertexEmbed a b
  let f₀ : {z : N.Word // N.IsCycleWord z} →
      {z : (N.addVertex a b).Word // (N.addVertex a b).IsCycleWord z} :=
    fun z => ⟨R.push z.val,(R.isCycleWord_push_iff z.val).mpr z.property⟩
  let f₁ : {p : N.Word // N.IsPathWord a b p} →
      {z : (N.addVertex a b).Word // (N.addVertex a b).IsCycleWord z} :=
    fun p => ⟨R.push p.val+unitWord (Sum.inr true)+unitWord (Sum.inr false),
      N.isCycleWord_addVertex a b p.property⟩
  apply natCard_add_le_of_injective f₀ f₁
  · intro z w h
    exact Subtype.ext (R.push_injective (congrArg Subtype.val h))
  · intro p q h
    have hh := congrArg Subtype.val h
    change R.push p.val+unitWord (Sum.inr true)+unitWord (Sum.inr false)=
      R.push q.val+unitWord (Sum.inr true)+unitWord (Sum.inr false) at hh
    exact Subtype.ext (R.push_injective (add_right_cancel (add_right_cancel hh)))
  · intro z p h
    have hh := congrArg (fun z => z.val (Sum.inr false)) h
    change R.push z.val (Sum.inr false)=
      (R.push p.val+unitWord (Sum.inr true)+unitWord (Sum.inr false) : E⊕Bool → Bit)
        (Sum.inr false) at hh
    have hne : (Sum.inr true : E⊕Bool)≠Sum.inr false := by simp
    simp only [R,Pi.add_apply,N.addVertex_push_inr,unitWord_apply,
      if_neg hne,if_pos rfl,zero_add] at hh
    exact zero_ne_one hh

/-- Adding a physical cap retains the old cycle space injectively. -/
theorem rank_le_addVertex (a b : V) :
    networkRank N≤networkRank (N.addVertex a b) := by
  let R := N.addVertexEmbed a b
  let f : {z : N.Word // N.boundary z=0} →
      {z : (N.addVertex a b).Word // (N.addVertex a b).boundary z=0} :=
    fun z => ⟨R.push z.val,(R.boundary_push_eq_zero_iff z.val).mpr z.property⟩
  have hh := Nat.card_le_card_of_injective f (by
    intro z w h
    exact Subtype.ext (R.push_injective (congrArg Subtype.val h)))
  rw [N.natCard_even,(N.addVertex a b).natCard_even] at hh
  exact (Nat.pow_le_pow_iff_right (by decide : 1<(2 : ℕ))).mp hh

/-- The central edge is subdivided; this preserves the tree-cap cycle count. -/
def closed (a b c d : V) :
    Network (Option (Option (Option V))) (((E⊕Bool)⊕Bool)⊕Bool) :=
  (FourPoleCaps.capped N a b c d).addVertex FourPoleCaps.left FourPoleCaps.right

/-- The families counted in the cap: all old cycles, all six paths, and two pairings. -/
def load (a b c d : V) : ℕ :=
  N.numCycles+N.numPaths a b+N.numPaths c d+
    N.numPathPairs c a b d+N.numPathPairs c b a d+
    N.numPaths a c+N.numPaths b c+N.numPaths a d+N.numPaths b d

theorem load_le_cycles (a b c d : V) : load N a b c d≤(closed N a b c d).numCycles := by
  have h₁ := cycles_add_paths_le N a b
  have h₂ := cycles_add_paths_le (N.addVertex a b) (some c) (some d)
  have h₃ := cycles_add_paths_le (FourPoleCaps.capped N a b c d)
    FourPoleCaps.left FourPoleCaps.right
  have hpair := N.numPaths_pairs_le_numPaths_addVertex a b c d
  have hcross := FourPoleCaps.four_paths_le N a b c d
  change (FourPoleCaps.capped N a b c d).numCycles+
    (FourPoleCaps.capped N a b c d).numPaths FourPoleCaps.left FourPoleCaps.right≤
    (closed N a b c d).numCycles at h₃
  change (N.addVertex a b).numCycles+(N.addVertex a b).numPaths (some c) (some d)≤
    (FourPoleCaps.capped N a b c d).numCycles at h₂
  unfold load
  omega

theorem rank_bounds (a b c d : V) :
    networkRank N≤networkRank (closed N a b c d) ∧
      networkRank (closed N a b c d)≤networkRank N+3 := by
  have hl₁ := rank_le_addVertex N a b
  have hl₂ := rank_le_addVertex (N.addVertex a b) (some c) (some d)
  have hl₃ := rank_le_addVertex (FourPoleCaps.capped N a b c d)
    FourPoleCaps.left FourPoleCaps.right
  have hu₁ := FourPoleCaps.rank_le N a b c d
  have hu₂ := (FourPoleCaps.capped N a b c d).networkRank_addVertex_le
    FourPoleCaps.left FourPoleCaps.right
  change networkRank (FourPoleCaps.capped N a b c d)≤networkRank (closed N a b c d) at hl₃
  change networkRank (closed N a b c d)≤networkRank (FourPoleCaps.capped N a b c d)+1 at hu₂
  change networkRank (N.addVertex a b)≤networkRank (FourPoleCaps.capped N a b c d) at hl₂
  omega

/-- The physical cap gives the normalized bound `z+S+F-u_alpha ≤ 4.001` at large rank. -/
theorem exists_thousandth_bound :
    ∃ B : ℕ,∀ (V E : Type) [Fintype V] [Fintype E] (N : Network V E),
      B≤networkRank N → ∀ a b c d : V,
      1000*load N a b c d≤4001*2^networkRank N := by
  obtain ⟨B,hB⟩ := ExactMaximum.numCycles_le_of_large_rank_margin 12
  refine ⟨B,?_⟩
  intro V E _ _ N hr a b c d
  have hrank := rank_bounds N a b c d
  have hc := hB _ _ (closed N a b c d) (hr.trans hrank.1)
  have hload := load_le_cycles N a b c d
  have hpow : 2^networkRank (closed N a b c d)≤8*2^networkRank N := by
    have hp := Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) hrank.2
    simpa only [pow_add,show (2 : ℕ)^3=8 by norm_num,mul_comm] using hp
  norm_num at hc
  nlinarith

end Erdos1016.ExactMaximumSupport.Shortening.TreeCapCycleBound
