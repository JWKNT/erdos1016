import Erdos1016.ExactMaximumSupport.SuppressedCyclicShore

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Short-cycle transversals under one actual port suppression

Avoiding the three thread vertices forces the replacement physical label to be
zero. Growing the cycle then preserves its size exactly. This is a local
ingredient only; no global bounded-port or bridge-decomposition theorem is
asserted here.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.ShortCycleTransversal
open BoundaryTrace BoundaryTrace.Network

local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- An actual set of vertices meeting every cycle of at most four physical labels. -/
def Hits {V E : Type*} [Fintype E] (N : Network V E) (X : Finset V) : Prop :=
  ∀ z : N.Word, N.IsCycleWord z → size z ≤ 4 →
    ∃ v, 0 < N.deg z v ∧ v ∈ X

/-- If the replacement label is unused, growth adds no selected physical label. -/
theorem size_grow_of_replacement_zero {E : Type*} [Fintype E]
    {e f : E} (hef : e≠f) (y : {g : E // g≠f} → Bit) (he : y ⟨e,hef⟩=0) :
    size (grow e f hef y)=size y := by
  classical
  let φ : {g : {g : E // g≠f} // y g≠0} ≃ {g : E // grow e f hef y g≠0} :=
    { toFun := fun g => ⟨g.val.val,by
        rw [grow_apply_of_ne hef y g.val.property]
        exact g.property⟩
      invFun := fun g =>
        let hgf : g.val≠f := by
          intro h
          have hh := g.property
          rw [h,grow_apply_f,he] at hh
          exact hh rfl
        ⟨⟨g.val,hgf⟩,by
          have hh := g.property
          rwa [grow_apply_of_ne hef y hgf] at hh⟩
      left_inv := fun g => by apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := fun g => by apply Subtype.ext; rfl }
  have hh := Nat.card_congr φ.symm
  simpa only [size,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh

variable {V E : Type*} [Fintype V] [Fintype E]
variable {N : Network V E} {e f : E} {u v w : V} (T : N.Thread e f u v w)

/-- One suppression increases the short-cycle transversal by at most its three thread vertices. -/
theorem hits_suppress (X : Finset V) (hX : Hits N X) :
    Hits (N.suppress e f u w T.huw) (insert u (insert v (insert w X))) := by
  intro z hz hsize
  classical
  let M := N.suppress e f u w T.huw
  let Y := insert u (insert v (insert w X))
  by_contra hno
  have havoid (x : V) (hx : 0<M.deg z x) : x∉Y := by
    intro hmem
    exact hno ⟨x,hx,hmem⟩
  have hezero : z ⟨e,T.hef⟩=0 := by
    by_contra hne
    have hu := M.deg_src_pos hne
    change 0<(N.suppress e f u w T.huw).deg z
      ((N.suppress e f u w T.huw).src ⟨e,T.hef⟩) at hu
    rw [N.suppress_src_of_eq T.huw ⟨e,T.hef⟩ rfl] at hu
    exact havoid u hu (by simp [Y])
  have hwithin : Within z (M.inside fun x => x∉Y) := by
    intro g hg
    exact ⟨havoid _ (M.deg_src_pos hg),havoid _ (M.deg_dst_pos hg)⟩
  have hgrowWithin := SuppressedCyclicShore.within_grow_inside T (fun x => x∉Y)
    (fun hu _ => False.elim (hu (by simp [Y]))) z hwithin
  have hgrow : N.IsCycleWord (grow e f T.hef z) := (T.isCycleWord_grow_iff z).mpr hz
  have hsmall : size (grow e f T.hef z)≤4 := by
    rw [size_grow_of_replacement_zero T.hef z hezero]
    exact hsize
  obtain ⟨x,hx,hmem⟩ := hX _ hgrow hsmall
  exact N.mem_of_within_inside hgrowWithin hx (by simp [Y,hmem])

omit [Fintype V] in
/-- The mark increase is independent of coincidences with earlier marked vertices. -/
theorem marks_card_le (X : Finset V) :
    (insert u (insert v (insert w X))).card ≤ X.card+3 := by
  classical
  have h1 := Finset.card_insert_le u (insert v (insert w X))
  have h2 := Finset.card_insert_le v (insert w X)
  have h3 := Finset.card_insert_le w X
  omega

end Erdos1016.ExactMaximumSupport.Shortening.ShortCycleTransversal
