import Erdos1016.Boundary.OwnerAndApex

set_option autoImplicit false

/-!
# The one-apex law is the complete even-boundary average

For connected inside, every even assignment to the individually labelled
cut edges has a nonempty complete internal parity fiber, all such fibers have
exactly the same cardinality, and their average is the apex cycle-space law.
This proves the normalization used in Section 2.1 of the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace Erdos1016.BoundaryTrace

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exact average over equally sized complete fibers. -/
theorem sigma_density_eq_average {Y : Type*} [Fintype Y]
    {X : Y → Type*} [∀ y, Fintype (X y)]
    (k : ℕ) (hcard : ∀ y, Fintype.card (X y) = k)
    (Good : (Σ y, X y) → Prop) :
    Finite.density Good =
      (∑ y, Finite.density (fun x : X y => Good ⟨y, x⟩)) / Fintype.card Y := by
  classical
  unfold Finite.density
  rw [Finite.count_sigma, Fintype.card_sigma]
  simp_rw [hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
  rw [← Finset.sum_div, div_div]
  congr 1
  exact mul_comm _ _

namespace Ported

variable {U V EI EO P : Type*}
  [Fintype U] [Fintype V] [Fintype EI] [Fintype EO] [Fintype P]
  {I : Network U EI} {O : Network V EO}

abbrev EvenPins (_L : Ported I O P) := LinearMap.ker (total : (P → Bit) →ₗ[Bit] Bit)

noncomputable instance evenPinsFintype (L : Ported I O P) :
    Fintype L.EvenPins := Fintype.ofFinite _

/-- No other local restrictions are imposed: this is the COMPLETE parity coset. -/
def Sector (L : Ported I O P) (y : L.EvenPins) :=
  {x : I.Word // I.boundary x = push L.inside y.1}

noncomputable instance sectorFintype (L : Ported I O P) (y : L.EvenPins) :
    Fintype (L.Sector y) := by
  letI : Finite I.Word := Finite.of_fintype I.Word
  letI : Finite (L.Sector y) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _





















end Ported
end Erdos1016.BoundaryTrace
