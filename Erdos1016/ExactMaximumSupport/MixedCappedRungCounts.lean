import Erdos1016.ExactMaximumSupport.MixedCappedTileCut
import Erdos1016.ExactMaximumSupport.MixedCappedStem
import Erdos1016.ExactMaximumSupport.MarkedRungCount

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option pp.maxSteps 3000

/-! # The actual marked rung in a capped mixed ladder

Deleting a rung leaves the literal preceding prefix with two pendant entry
labels. The suffix routes retain all physical labels and their exact counts.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.MixedCappedRungCounts
open BoundaryTrace BoundaryTrace.Network BoundaryDecay MixedTiles
open MixedCappedTailEmbed MixedCappedTileCut
local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
variable {k : ℕ}

private def stemLabels (T : Fin (k+1) → Kind) (p : Fin (k+1)) : CappedEdge T → Prop
  | Sum.inl (Sum.inl ⟨i,_⟩) => i.val<p.val
  | Sum.inl (Sum.inr (i,_)) => i.val<p.val
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

/-- A local rung joins its two rail vertices in the original physical model. -/
theorem rung_joins (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) :
    (capped T).Joins (Sum.inl (MixedTiles.inner T p e))
      (Sum.inl (right T p false)) (Sum.inl (right T p true)) := by
  left
  constructor
  · apply congrArg Sum.inl
    change (⟨p,(T p).src e⟩ : Vertex T)=⟨p,(T p).right false⟩
    have hh : (T p).src e=(T p).right false := by
      generalize ht : T p=t at e ⊢
      cases t with
      | rung => rfl
      | square => exact Kind.noConfusion (ht.symm.trans hT)
    exact congrArg (fun v : (T p).Vertex => (⟨p,v⟩ : Vertex T)) hh
  · apply congrArg Sum.inl
    change (⟨p,(T p).dst e⟩ : Vertex T)=⟨p,(T p).right true⟩
    have hh : (T p).dst e=(T p).right true := by
      generalize ht : T p=t at e ⊢
      cases t with
      | rung => rfl
      | square => exact Kind.noConfusion (ht.symm.trans hT)
    exact congrArg (fun v : (T p).Vertex => (⟨p,v⟩ : Vertex T)) hh

private theorem deleted_after_iff (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) (g : CappedEdge T) :
    g≠Sum.inl (MixedTiles.inner T p e) ∧ (capped T).inside (after T p) g ↔ stemLabels T p g := by
  rcases g with (⟨i,f⟩ | ⟨i,b⟩) | (b | b)
  · by_cases hi : i=p
    · subst i
      haveI : Subsingleton (T p).Edge := by rw [hT]; infer_instance
      have hf : f=e := Subsingleton.elim f e
      subst f
      simp [MixedTiles.inner,stemLabels]
    · have hne : (Sum.inl (Sum.inl ⟨i,f⟩) : CappedEdge T)≠Sum.inl (MixedTiles.inner T p e) := by
        intro h
        exact hi (congrArg Sigma.fst (Sum.inl.inj (Sum.inl.inj h)))
      constructor
      · rintro ⟨_,h⟩
        change i.val≤p.val ∧ i.val≤p.val at h
        change i.val<p.val
        have hv : i.val≠p.val := fun h => hi (Fin.ext h)
        omega
      · intro h
        refine ⟨hne,?_⟩
        change i.val≤p.val ∧ i.val≤p.val
        change i.val<p.val at h
        omega
  · constructor
    · rintro ⟨_,h⟩
      change i.val≤p.val ∧ i.val+1≤p.val at h
      change i.val<p.val
      omega
    · intro h
      refine ⟨?_,?_⟩
      · intro heq
        exact Sum.noConfusion (Sum.inl.inj heq)
      · change i.val≤p.val ∧ i.val+1≤p.val
        change i.val<p.val at h
        omega
  · simp [MixedTiles.inner,Network.inside,after,capped,cappedSrc,cappedDst,left,stemLabels]
  · simp [MixedTiles.inner,Network.inside,after,capped,cappedSrc,cappedDst,right,stemLabels]

private theorem numPaths_instances {A B : Type*} (N : Network A B)
    (i j : Fintype B) (a b : A) :
    @Network.numPaths A B i N a b = @Network.numPaths A B j N a b := by
  rw [Subsingleton.elim i j]

/-- The suffix count is unchanged by removal of the internal marked rung. -/
theorem deleted_exterior_route (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (e : (T p).Edge) (b : Bool) :
    (if exitVertex T p b=Sum.inr true then 1 else
      ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
        ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).outside (after T p))).numPaths
          (exitVertex T p b) (Sum.inr true))=2^remainingWeight T p := by
  have hnot : ¬(capped T).outside (after T p) (Sum.inl (MixedTiles.inner T p e)) := by
    simp [Network.outside,after,capped,cappedSrc,cappedDst,MixedTiles.inner,chain,chainSrc,chainDst]
  have hh := NetworkSubnetworkPaths.numPaths_delete_outside (capped T)
    ((capped T).outside (after T p)) (Sum.inl (MixedTiles.inner T p e)) hnot
    (exitVertex T p b) (Sum.inr true)
  by_cases hb : exitVertex T p b=Sum.inr true
  · simpa only [if_pos hb] using exterior_route_count T p b
  · rw [if_neg hb]
    have heq : ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
        ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).outside (after T p))).numPaths
          (exitVertex T p b) (Sum.inr true) =
        ((capped T).sub ((capped T).outside (after T p))).numPaths
          (exitVertex T p b) (Sum.inr true) := by
      exact (numPaths_instances _ _ _ _ _).trans hh
    rw [heq]
    simpa only [if_neg hb] using exterior_route_count T p b

/-- The exact marked-rung formula uses the actual deleted prefix path count. -/
theorem count_eq (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) :
    MarkedPathCount.count (capped T) (Sum.inl (MixedTiles.inner T p e)) (Sum.inr true)=
      2*(1+((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
        ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).inside (after T p))).numPaths
          (Sum.inl (right T p false)) (Sum.inl (right T p true)))*2^remainingWeight T p := by
  have hc := MarkedRungCount.count_eq (capped T) (after T p)
    (e:=Sum.inl (MixedTiles.inner T p e))
    (f:=exitEdge T p false) (g:=exitEdge T p true)
    (x:=Sum.inl (right T p false)) (u:=Sum.inl (right T p true))
    (y:=exitVertex T p false) (v:=exitVertex T p true) (t:=Sum.inr true)
    (rung_joins T p hT e)
    (after_right T p false) (after_right T p true)
    (exit_joins T p false) (not_after_exit T p false)
    (exit_joins T p true) (not_after_exit T p true)
    (exit_ne T p false) (crossing_labels T p false) (not_after_cap T p)
    (2^remainingWeight T p)
    (by
      by_cases hb : exitVertex T p false=Sum.inr true
      · simpa only [if_pos hb] using deleted_exterior_route T p e false
      · rw [if_neg hb]
        have hh := deleted_exterior_route T p e false
        rw [if_neg hb] at hh
        exact (numPaths_instances _ _ _ _ _).trans hh)
    (by
      by_cases hb : exitVertex T p true=Sum.inr true
      · simpa only [if_pos hb] using deleted_exterior_route T p e true
      · rw [if_neg hb]
        have hh := deleted_exterior_route T p e true
        rw [if_neg hb] at hh
        exact (numPaths_instances _ _ _ _ _).trans hh)
  calc
    _ = _ := hc
    _ = _ := by
      apply congrArg (fun A : ℕ => 2*(1+A)*2^remainingWeight T p)
      exact numPaths_instances _ _ _ _ _

/-- Deleting the rung identifies its prefix shore with the literal physical stem. -/
def deletedPrefixIso (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) :
    NetworkIso ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
      ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).inside (after T p)))
      ((capped T).sub (MixedCappedStem.stem T p)) :=
  NetworkLeafRank.restrictionIso (capped T) (fun g => g≠Sum.inl (MixedTiles.inner T p e))
    ((capped T).inside (after T p)) (MixedCappedStem.stem T p)
    (fun g => by
      have hh := deleted_after_iff T p hT e g
      rcases g with (⟨i,f⟩ | ⟨i,b⟩) | (b | b) <;> exact hh)

/-- The actual deleted-prefix path count has the preceding-weight capacity. -/
theorem prefix_le (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) :
    ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
      ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).inside (after T p))).numPaths
        (Sum.inl (right T p false)) (Sum.inl (right T p true)) ≤ 2^precedingWeight T p := by
  have heq := (deletedPrefixIso T p hT e).numPaths_eq
    (Sum.inl (right T p false)) (Sum.inl (right T p true))
  have hh := MixedCappedStem.numPaths_le T p
    (Sum.inl (right T p false)) (Sum.inl (right T p true))
  have heq' : ((capped T).sub (MixedCappedStem.stem T p)).numPaths
        (Sum.inl (right T p false)) (Sum.inl (right T p true)) =
      ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).sub
        ((MarkedRungCount.deleted (capped T) (Sum.inl (MixedTiles.inner T p e))).inside (after T p))).numPaths
          (Sum.inl (right T p false)) (Sum.inl (right T p true)) := by
    exact (numPaths_instances _ _ _ _ _).trans heq
  exact heq'.symm.le.trans hh

/-- Every actual marked rung gives a full count or a seven-eighths bound. -/
theorem rung_gap (T : Fin (k+1) → Kind) (p : Fin (k+1))
    (hT : T p=Kind.rung) (e : (T p).Edge) :
    MarkedPathCount.count (capped T) (Sum.inl (MixedTiles.inner T p e)) (Sum.inr true)=2^(weight T+1) ∨
      8*MarkedPathCount.count (capped T) (Sum.inl (MixedTiles.inner T p e)) (Sum.inr true)≤
        7*2^(weight T+1) := by
  have hw : precedingWeight T p+remainingWeight T p+2=weight T+1 := by
    have hh := weight_split T p
    rw [hT] at hh
    change precedingWeight T p+1+remainingWeight T p=weight T at hh
    omega
  rw [count_eq T p hT e]
  have hh := ThirdPortArithmetic.rung_gap (precedingWeight T p) (remainingWeight T p) _
    (prefix_le T p hT e)
  rw [hw] at hh
  exact hh

end Erdos1016.ExactMaximumSupport.MixedCappedRungCounts
