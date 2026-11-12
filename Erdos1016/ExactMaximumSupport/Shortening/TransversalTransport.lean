import Erdos1016.ExactMaximumSupport.Shortening.ShortCycleTransversal
import Erdos1016.ExactMaximum.PoleBridges

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! # Actual short-cycle transversals under physical embeddings and restrictions

Physical labels remain distinct. The word size is preserved by an embedding;
the transversal pulls back to its actual vertex preimage. Literal bridge shores
and the positive-support induced network are special cases.
-/
noncomputable section
namespace Erdos1016.ExactMaximumSupport.Shortening.TransversalTransport
open BoundaryTrace BoundaryTrace.Network BoundaryDecay ShortCycleTransversal

local instance (priority := 100) propDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]

omit [Fintype V] [Fintype W] in
/-- Extending along an injective physical-label map preserves the selected size. -/
theorem size_push {N : Network V E} {M : Network W F} (R : N.Embed M)
    (z : N.Word) : size (R.push z)=size z := by
  classical
  let f : {e : E // z e≠0} → {e : F // R.push z e≠0} :=
    fun e => ⟨R.ψ e.val,by simpa only [R.push_apply] using e.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (R.ψ_inj (congrArg Subtype.val h))
    · intro b
      obtain ⟨e,he⟩ := R.within_push z b.val b.property
      have hz : z e≠0 := by
        have hh := b.property
        rw [←he,R.push_apply] at hh
        exact hh
      exact ⟨⟨e,hz⟩,Subtype.ext he⟩
  have hh := (Nat.card_eq_of_bijective f hf).symm
  simpa only [size,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh

/-- Pull back the actual marked vertices through a physical embedding. -/
theorem hits_of_embed {N : Network V E} {M : Network W F} (R : N.Embed M)
    (X : Finset W) (hX : Hits M X) :
    Hits N (Finset.univ.filter fun v => R.φ v∈X) := by
  intro z hz hsize
  have hcycle := (R.isCycleWord_push_iff z).mpr hz
  have hs : size (R.push z)≤4 := by rw [size_push]; exact hsize
  obtain ⟨v,hv,hmem⟩ := hX (R.push z) hcycle hs
  obtain ⟨e,he,hat⟩ := M.exists_edge_of_deg_pos hv
  obtain ⟨g,hg⟩ := R.within_push z e he
  have hzg : z g≠0 := by rw [←hg,R.push_apply] at he; exact he
  rcases hat with hsrc | hdst
  · have hφ : R.φ (N.src g)=v := by rw [←R.src,hg]; exact hsrc
    exact ⟨N.src g,N.deg_src_pos hzg,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hφ.symm ▸ hmem⟩⟩
  · have hφ : R.φ (N.dst g)=v := by rw [←R.dst,hg]; exact hdst
    exact ⟨N.dst g,N.deg_dst_pos hzg,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hφ.symm ▸ hmem⟩⟩

omit [Fintype V] [Fintype E] [Fintype W] [Fintype F] in
/-- Literal edge restriction, retaining every vertex and every selected label. -/
def subEmbed (N : Network V E) (p : E → Prop) : (N.sub p).Embed N where
  φ := id
  ψ := Subtype.val
  φ_inj := Function.injective_id
  ψ_inj := Subtype.val_injective
  src _ := rfl
  dst _ := rfl

omit [Fintype W] [Fintype F] in
/-- A literal edge subnetwork inherits the original short-cycle transversal. -/
theorem hits_sub (N : Network V E) (p : E → Prop) (X : Finset V) (hX : Hits N X) :
    Hits (N.sub p) X := by
  have hh := hits_of_embed (subEmbed N p) X hX
  have heq : (Finset.univ.filter fun v => (subEmbed N p).φ v∈X)=X := by
    ext v
    simp [subEmbed]
  rwa [heq] at hh

omit [Fintype W] [Fintype F] in
/-- The marks on the opposite shore are irrelevant to cycles inside this shore. -/
theorem hits_inside (N : Network V E) (S : V → Prop) (X : Finset V) (hX : Hits N X) :
    Hits (N.sub (N.inside S)) (X.filter S) := by
  intro z hz hsize
  obtain ⟨v,hv,hmem⟩ := hits_sub N (N.inside S) X hX z hz hsize
  have hwithin : Within (extend (N.inside S) z) (N.inside S) :=
    fun e he => prop_of_extend_ne_zero _ z he
  have hvN : 0<N.deg (extend (N.inside S) z) v := by rw [N.deg_extend]; exact hv
  exact ⟨v,hv,Finset.mem_filter.mpr ⟨hmem,N.mem_of_within_inside hwithin hvN⟩⟩

omit [Fintype W] [Fintype F] in
/-- The complementary physical shore has the complementary marked subset. -/
theorem hits_outside (N : Network V E) (S : V → Prop) (X : Finset V) (hX : Hits N X) :
    Hits (N.sub (N.outside S)) (X.filter fun v => ¬S v) := by
  convert hits_inside N (fun v => ¬S v) X hX using 1
  ext v
  simp

omit [Fintype W] [Fintype F] in
/-- Actual induced-vertex restriction pulls back marks to the subtype. -/
theorem hits_induce (N : Network V E) (S : V → Prop) (X : Finset V) (hX : Hits N X) :
    Hits (N.induce S) (X.subtype S) := by
  have hh := hits_of_embed (N.induceEmbed S) X hX
  have heq : (Finset.univ.filter fun v : {v // S v} => (N.induceEmbed S).φ v∈X)=
      X.subtype S := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_subtype,induceEmbed]
  rwa [heq] at hh

omit [Fintype W] [Fintype F] in
/-- The positive-support normalization used by weak poles inherits all marks. -/
theorem hits_positive (N : Network V E) (X : Finset V) (hX : Hits N X) :
    Hits (N.induce fun v => 0<N.deg (fun _ => 1) v)
      (X.subtype fun v => 0<N.deg (fun _ => 1) v) := by
  convert hits_induce N (fun v => 0<N.deg (fun _ => 1) v) X hX using 1
  ext v
  simp

end Erdos1016.ExactMaximumSupport.Shortening.TransversalTransport
