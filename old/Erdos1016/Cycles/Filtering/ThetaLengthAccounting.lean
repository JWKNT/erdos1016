import Erdos1016.Cycles.Filtering.ReturnTheta

set_option autoImplicit false

/-!
# Exact length accounting for the selected theta pair

The theta selected from a source cycle and a short return has three branches.
Every choice of its two-branch base plus the omitted branch has the same total
length. This is the elementary geometry behind the weighted external-return
charge.
-/

namespace Erdos1016.Proof.ThetaLengthAccounting

open Erdos1016.Proof.ExternalReturnTheta

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V}

/-- A pair-cycle and its omitted branch partition the three theta branches. -/
theorem pair_plus_omitted_eq_all_branches {u v : V}
    (t : ThetaPaths H u v) (p : ThetaPair) :
    pairLength H t p + omittedBranchLength H t p =
      t.left.length + t.right.length + t.external.length := by
  cases p <;> simp [pairLength, omittedBranchLength] <;> omega

/-- Choosing any minimum pair as candidate base preserves the total
base-plus-return length: it equals the original left-right source cycle plus
the external return branch. -/
theorem minimum_pair_plus_omitted_eq_source_plus_return {u v : V}
    (t : ThetaPaths H u v) :
    pairLength H t (minimumPair H t) +
        omittedBranchLength H t (minimumPair H t) =
      pairLength H t .leftRight + t.external.length := by
  rw [pair_plus_omitted_eq_all_branches]
  simp [pairLength]

/-- If the source theta's external branch is the selected short return, the
base-plus-branch exponent in the candidate weight is at most the source
cycle length plus the return cutoff. -/
theorem minimum_pair_charge_bound {u v : V}
    (t : ThetaPaths H u v) (q : ℕ)
    (hreturn : t.external.length ≤ q) :
    pairLength H t (minimumPair H t) +
        omittedBranchLength H t (minimumPair H t) ≤
      pairLength H t .leftRight + q := by
  rw [minimum_pair_plus_omitted_eq_source_plus_return]
  omega

end Erdos1016.Proof.ThetaLengthAccounting
