import Erdos1016.ExactMaximumSupport.MixedCappedEntry
import Erdos1016.ExactMaximumSupport.MixedCappedTileCut
import Erdos1016.ExactMaximumSupport.NetworkLeafRank

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # The actual prefix with its two pendant tile-entry vertices -/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedStem
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles MixedCappedTailEmbed
open MixedCappedEntry MixedCappedTileCut NetworkLeafRank
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

/-- Prefix labels together with the two labels entering the next tile. -/
def stem (T : Fin (k+1) → Kind) (p : Fin (k+1)) : CappedEdge T → Prop
  | Sum.inl (Sum.inl e) => e.1.val < p.val
  | Sum.inl (Sum.inr e) => e.1.val < p.val
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

@[simp] theorem entry_mem (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool) :
    stem T p (entryEdge T p b) := by
  unfold entryEdge
  split
  · simp only [stem,link]
    omega
  · trivial

/-- The retained entry vertex has just its original incoming physical label. -/
theorem incident_entry (T : Fin (k+1) → Kind) (p : Fin (k+1)) (b : Bool)
    (e : CappedEdge T) (he : stem T p e)
    (hi : (capped T).src e=Sum.inl (left T p b) ∨
      (capped T).dst e=Sum.inl (left T p b)) : e=entryEdge T p b := by
  rcases e with (⟨i,e⟩ | ⟨i,c⟩) | (c | c)
  · have hidx : i=p := by
      rcases hi with hi | hi <;>
        exact congrArg Sigma.fst (Sum.inl.inj hi)
    subst i
    exact False.elim (Nat.lt_irrefl _ he)
  · rcases hi with hi | hi
    · have hip : i.castSucc=p := congrArg Sigma.fst (Sum.inl.inj hi)
      have he' : i.val<p.val := he
      have hh := congrArg Fin.val hip
      simp only [Fin.coe_castSucc] at hh
      omega
    · have hip : i.succ=p := congrArg Sigma.fst (Sum.inl.inj hi)
      subst p
      have hcb : c=b := by
        apply Kind.left_injective (T i.succ)
        exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj hi)).2
      subst c
      simp [entryEdge,link]
  · rcases hi with hi | hi
    · contradiction
    · have hip : (0 : Fin (k+1))=p := congrArg Sigma.fst (Sum.inl.inj hi)
      subst p
      have hcb : c=b := by
        apply Kind.left_injective (T 0)
        exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj hi)).2
      subst c
      simp [entryEdge]
  · exact False.elim he

/-- The two new entry leaves are distinct. -/
theorem entries_ne (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    (Sum.inl (left T p false) : CappedVertex T)≠Sum.inl (left T p true) := by
  intro h
  have hh := Kind.left_injective (T p) (eq_of_heq (Sigma.mk.inj (Sum.inl.inj h)).2)
  exact Bool.false_ne_true hh

/-- Deleting the two entry leaves retains exactly the literal prefix labels. -/
theorem remove_entries (T : Fin (k+1) → Kind) (p : Fin (k+1)) (e : CappedEdge T) :
    (stem T p e ∧ (capped T).outside (fun v => v=Sum.inl (left T p false)) e) ∧
      (capped T).outside (fun v => v=Sum.inl (left T p true)) e ↔
      (capped T).inside (before T p) e := by
  rcases e with (⟨i,e⟩ | ⟨i,b⟩) | (b | b)
  · by_cases hip : i=p
    · subst i
      simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,chain,chainSrc,
        chainDst,before]
    · have hip' : i.val≠p.val := fun h => hip (Fin.ext h)
      simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,chain,chainSrc,
        chainDst,before,left,hip]
  · by_cases hip : i.succ=p
    · subst p
      cases b <;> simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,
        chain,chainSrc,chainDst,before,left,right]
    · have hidx : i.val+1≠p.val := fun h => hip (Fin.ext h)
      by_cases hi : i.castSucc=p
      · subst p
        simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,
          chain,chainSrc,chainDst,before,left,right]
      · simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,
          chain,chainSrc,chainDst,before,left,right,hip,hi]
        omega
  · by_cases hp : p=0
    · subst p
      cases b <;> simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,
        before,left]
    · have hp' : (0 : Fin (k+1))≠p := Ne.symm hp
      have hpos : 0<p.val := by have hh : p.val≠0 := fun h => hp (Fin.ext h); omega
      simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,before,left,hp',hpos]
  · simp [stem,Network.inside,Network.outside,capped,cappedSrc,cappedDst,before]

/-- The prefix with two pendant entry vertices has the preceding tile weight as rank. -/
theorem rank (T : Fin (k+1) → Kind) (p : Fin (k+1)) :
    networkRank ((capped T).sub (stem T p))=precedingWeight T p := by
  let N := (capped T).sub (stem T p)
  let x : CappedVertex T := Sum.inl (left T p false)
  let y : CappedVertex T := Sum.inl (left T p true)
  let e : {e : CappedEdge T // stem T p e} := ⟨entryEdge T p false,entry_mem T p false⟩
  let f : {e : CappedEdge T // stem T p e} := ⟨entryEdge T p true,entry_mem T p true⟩
  have he : N.Joins e x (entryVertex T p false) := entry_joins T p false
  have hf : N.Joins f y (entryVertex T p true) := entry_joins T p true
  have hxe (q : {e : CappedEdge T // stem T p e}) (hq : N.src q=x ∨ N.dst q=x) : q=e :=
    Subtype.ext (incident_entry T p false q.val q.property hq)
  have hyf (q : {e : CappedEdge T // stem T p e}) (hq : N.src q=y ∨ N.dst q=y) : q=f :=
    Subtype.ext (incident_entry T p true q.val q.property hq)
  have hyx : y≠x := (entries_ne T p).symm
  have hux : entryVertex T p true≠x := by
    change entryVertex T p true≠Sum.inl (left T p false)
    intro h
    exact left_not_before T p false (h ▸ entry_before T p true)
  have hfo : N.outside (fun v => v=x) f := by
    rcases hf with ⟨hs,hd⟩ | ⟨hs,hd⟩
    · exact ⟨hs ▸ hyx,hd ▸ hux⟩
    · exact ⟨hs ▸ hux,hd ▸ hyx⟩
  let M := N.sub (N.outside (fun v => v=x))
  let f' : {q // N.outside (fun v => v=x) q} := ⟨f,hfo⟩
  have hf' : M.Joins f' y (entryVertex T p true) := hf
  have hyf' (q : {q // N.outside (fun v => v=x) q}) (hq : M.src q=y ∨ M.dst q=y) : q=f' :=
    Subtype.ext (hyf q.val hq)
  have h₁ := rank_delete_leaf N he hxe
  have h₂ := rank_delete_leaf M hf' hyf'
  have h₃ := (twoOutsideIso (capped T) (stem T p) ((capped T).inside (before T p)) x y
    (remove_entries T p)).networkRank_eq
  have hp := MixedCappedPrefixEmbed.inside_rank_sum T p
  change networkRank N=precedingWeight T p
  exact h₁.trans (h₂.trans (h₃.symm.trans hp))

/-- Every actual path count in this stem obeys the preceding-weight bound. -/
theorem numPaths_le (T : Fin (k+1) → Kind) (p : Fin (k+1)) (a b : CappedVertex T) :
    ((capped T).sub (stem T p)).numPaths a b≤2^precedingWeight T p := by
  have h := ((capped T).sub (stem T p)).numPaths_le_two_pow a b
  rw [rank] at h
  exact h

end Erdos1016.ExactMaximumSupport.MixedCappedStem
