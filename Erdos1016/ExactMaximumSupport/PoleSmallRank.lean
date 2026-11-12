import Erdos1016.ExactMaximumSupport.PolePathRank
import Erdos1016.ExactMaximum.PoleReduce
import Erdos1016.ExactMaximum.PoleLayers

set_option autoImplicit false

/-!
# The rank-one base case for poles with two ports

The exact order formula leaves only the two ports at rank one.
The two physical edges then give two distinct singleton path words.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.PoleSmallRank
open BoundaryTrace BoundaryTrace.Network BoundaryDecay
local instance smallRankDecidable (p : Prop) : Decidable p := Classical.propDecidable p
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

/-- A connected pole with two distinct ports has positive cycle rank. -/
theorem rank_pos (s t : V) (hN : N.IsBridgelessTwoPole s t) : 0 < networkRank N := by
  have horder := PolePathRank.bridgeless_order N s t hN
  have hh := Finset.card_le_card (Finset.subset_univ ({s,t} : Finset V))
  rw [Finset.card_pair hN.ne,Finset.card_univ] at hh
  omega

/-- At rank one, all vertices are the two ports. -/
theorem vertex_eq_port_of_rank_one (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (hrank : networkRank N = 1) (v : V) : v = s ∨ v = t := by
  have horder := PolePathRank.bridgeless_order N s t hN
  have heq : ({s,t} : Finset V) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hN.ne,Finset.card_univ,horder,hrank]
  have hv : v ∈ ({s,t} : Finset V) := by rw [heq]; exact Finset.mem_univ _
  simpa only [Finset.mem_insert,Finset.mem_singleton] using hv

/-- The rank-one pair is full, with both parallel edge labels counted. -/
theorem full_of_rank_one (s t : V) (hN : N.IsBridgelessTwoPole s t)
    (hrank : networkRank N = 1) : N.IsFullPair s t := by
  classical
  obtain ⟨e,f,u,w,hef,he,hf,honly⟩ := N.exists_two_edges_of_deg_two hN.deg_s
  have hu : u = t := (vertex_eq_port_of_rank_one N s t hN hrank u).resolve_left he.ne
  have hw : w = t := (vertex_eq_port_of_rank_one N s t hN hrank w).resolve_left hf.ne.symm
  subst u
  subst w
  have hne : (unitWord e : N.Word) ≠ unitWord f := by
    intro h
    have hh := congrFun h e
    simp only [unitWord_apply,ite_true,if_neg hef.symm] at hh
    exact one_ne_zero hh
  have hsub : ({unitWord e,unitWord f} : Finset N.Word) ⊆
      Finset.univ.filter (N.IsPathWord s t) := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,N.isPathWord_unitWord he.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,N.isPathWord_unitWord hf⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hh
  have hlow : 2 ≤ N.numPaths s t := by
    simpa only [numPaths,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hupp := N.numPaths_le_two_pow s t
  change N.numPaths s t = 2 ^ networkRank N
  rw [hrank,pow_one] at hupp ⊢
  omega

end Erdos1016.ExactMaximumSupport.PoleSmallRank
