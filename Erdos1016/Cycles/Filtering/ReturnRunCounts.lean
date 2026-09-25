import Erdos1016.Nonbacktracking.Walks.SplitRunCoordinates

set_option autoImplicit false

noncomputable section
namespace Erdos1016.Proof.ExternalReturnFilter

open Erdos1016.Nonbacktracking
open Erdos1016.Proof.WalkPrefix
open Erdos1016.Proof.CollisionSliceInstantiation

variable (G : PhysicalGraph)

private theorem runDarts_cast_len {m n : ℕ} (hmn : m = n) {d e : Dart G}
    (r : Run G m d e) : runDarts G n (hmn ▸ r) = runDarts G m r := by
  cases hmn
  rfl

private theorem runDarts_cast_end {s : ℕ} {d e₁ e₂ : Dart G}
    (he : e₁ = e₂) (r : Run G s d e₁) :
    runDarts G s (he ▸ r) =
      runDarts G s r := by
  cases he
  rfl

private theorem runDarts_cast_start {s : ℕ} {d₁ d₂ e : Dart G}
    (hd : d₁ = d₂) (r : Run G s d₁ e) :
    runDarts G s (hd ▸ r) = runDarts G s r := by
  cases hd
  rfl

/-- Girth makes the short final segment uniquely recoverable from its
boundary dart and endpoint. This injectivity needs no degree bound. -/
theorem fixedEndpointPrefix_injective_of_girth
    (D a s : ℕ) (u v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsa : s < a) (hshort : 2 * s ≤ D) :
    Function.Injective (fixedEndpointPrefix G
      (show a - s - 1 ≤ a - 1 by omega) u v) := by
  classical
  let j : ℕ := a - s - 1
  let k : ℕ := a - 1
  have hjk : j ≤ k := by dsimp [j, k]; omega
  have hks : k - j = s := by dsimp [j, k]; omega
  let takePrefix : EndpointRuns G k u v → StartingRuns G j u :=
    fixedEndpointPrefix G hjk u v
  change Function.Injective takePrefix
  intro p q hpq
  let pz := splitRun G hjk p.1.2.2
  let qz := splitRun G hjk q.1.2.2
  have hb : pz.1 = qz.1 := by
    have hh := congrArg (fun z : StartingRuns G j u => z.2.1) hpq
    simpa [takePrefix, pz, qz, fixedEndpointPrefix] using hh
  have hpref : runDarts G j pz.2.1 = runDarts G j qz.2.1 := by
    have hh := congrArg (fun z : StartingRuns G j u => runDarts G j z.2.2) hpq
    simpa [takePrefix, pz, qz, fixedEndpointPrefix] using hh
  have hterminalP : head G p.1.2.1 = v := by
    have hv := congrArg Prod.snd p.2
    exact hv
  have hterminalQ : head G q.1.2.1 = v := by
    have hv := congrArg Prod.snd q.2
    exact hv
  let rp : Run G s pz.1 p.1.2.1 := hks ▸ pz.2.2
  let rq0 : Run G (k - j) qz.1 q.1.2.1 := qz.2.2
  let rq : Run G s qz.1 q.1.2.1 := hks ▸ rq0
  let rq' : Run G s pz.1 q.1.2.1 := hb.symm ▸ rq
  have hlistSuffix : runDarts G s rp = runDarts G s rq := by
    have hterm := hterminalP.trans hterminalQ.symm
    obtain ⟨he, hsuf⟩ := continuation_eq_of_boundary_and_endpoint
      G s D hs hg hshort rp rq' hterm
    have hlistCast := congrArg (runDarts G s) hsuf
    have hleft := (runDarts_cast_end G he rp).symm
    have hright : runDarts G s rq' = runDarts G s rq := by
      change runDarts G s (hb.symm ▸ rq) = runDarts G s rq
      exact runDarts_cast_start G hb.symm rq
    exact hleft.trans (hlistCast.trans hright)
  have hfullDarts : runDarts G k p.1.2.2 = runDarts G k q.1.2.2 := by
    have hpSplit := runDarts_splitRun G hjk p.1.2.2
    have hqSplit := runDarts_splitRun G hjk q.1.2.2
    have hlistOrig : runDarts G (k - j) pz.2.2 =
        runDarts G (k - j) qz.2.2 := by
      have hleft := runDarts_cast_len G hks pz.2.2
      have hright := runDarts_cast_len G hks qz.2.2
      dsimp [rp, rq] at hlistSuffix
      exact hleft.symm.trans (hlistSuffix.trans hright)
    calc
      runDarts G k p.1.2.2 =
          runDarts G j pz.2.1 ++ (runDarts G (k - j) pz.2.2).tail := by
        simpa [pz] using hpSplit
      _ = runDarts G j qz.2.1 ++ (runDarts G (k - j) qz.2.2).tail := by
        rw [hpref, hlistOrig]
      _ = runDarts G k q.1.2.2 := by
        simpa [qz] using hqSplit.symm
  have hval : p.1 = q.1 := by
    apply allRuns_darts_injective G k
    exact hfullDarts
  exact Subtype.ext hval

/-- Fixed-endpoint nonbacktracking runs of `a` edges inject into their
`a-s`-edge prefixes when `2s` is below the girth. This is the graph-specific
unique-suffix input to the path-mass arithmetic. -/
theorem endpointRuns_card_le_suffix_budget_of_max_degree
    (hmax : ∀ v, G.degree v ≤ 3)
    (D a s : ℕ) (u v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsa : s < a) (hshort : 2 * s ≤ D) :
    Fintype.card (EndpointRuns G (a - 1) u v) ≤
      3 * 2 ^ (a - s - 1) := by
  classical
  let j := a - s - 1
  have hinj := fixedEndpointPrefix_injective_of_girth G D a s u v hg hs hsa hshort
  calc
    Fintype.card (EndpointRuns G (a - 1) u v) ≤
        Fintype.card (StartingRuns G j u) := Fintype.card_le_of_injective _ hinj
    _ ≤ 3 * 2 ^ (a - s - 1) := by
      simpa [j] using startingRuns_card_le_of_max_degree G hmax (a - s - 1) u


/-- Compatibility form of the stronger maximum-degree-only bound. -/
theorem endpointRuns_card_le_suffix_budget
    (_hmin : ∀ v, 2 ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ 3)
    (D a s : ℕ) (u v : G.Vertex)
    (hg : ShortWalks.GirthGreater G.toSimpleGraph D)
    (hs : 0 < s) (hsa : s < a) (hshort : 2 * s ≤ D) :
    Fintype.card (EndpointRuns G (a - 1) u v) ≤
      3 * 2 ^ (a - s - 1)  := by
  exact endpointRuns_card_le_suffix_budget_of_max_degree G hmax D a s u v hg hs hsa hshort

end Erdos1016.Proof.ExternalReturnFilter
end
