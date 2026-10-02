# Theorem verification

Install the pinned Lean 4.19.0 toolchain and Mathlib dependency artifacts. Then run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --fresh --jobs 2
```

The verifier rebuilds every active library module from source with at most two concurrent local builds. It requires the library to equal the umbrella's import closure. It checks source files for proof admissions and unsafe evaluation. Before compilation, it checks the pinned dependency environment. It reuses dependency artifacts. For a fresh run, it moves the project's previous build to a separate location.

`audits/TheoremAudit.lean` verifies more than an axiom list. It independently states the conclusion for every natural number `n ≥ 3`. This check covers natural excess and the integer minimum-edge count minus `n`. Lean metaprogramming requires `Erdos1016.mainTheorem` to have exactly the type `Problem1016.MainTheorem`. It requires the integer theorem to have the independently expanded type. It requires `ShortProof.fewComponentForestEstimate` to have exactly its unconditional target type.

A theorem with an additional mathematical premise cannot pass these checks.

The audit reports kernel axioms for the public endpoints and the main steps of the shorter proof. These steps include actual retained-cycle supply, the link bound, and the weighted forest estimate. They also include the contraction law, the small-cut bound, and descent. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. The log checker requires every named report and all three checked statement markers. It rejects conditional development logs, Lean errors, proof admissions, and compiler-trust axioms.

The schema-version-3 report is `.verification/verification.json`. The same directory contains detailed rebuild logs and `theorem-audit.log`. The report binds the result to hashes of the library source set and verification inputs. These inputs are source, audits, scripts, toolchain, dependency manifest, and workflow. If an input changes during the check, verification fails.

- `status: passed`, `kernel_checks_status: passed`, `formalization_status: complete`, and `unconditional_main_theorem_proved: true` appear together only if all required checks pass. The input hash must also remain unchanged.
- Running or failed checks use `formalization_status: unverified` and `unconditional_main_theorem_proved: false`. They provide no completed certificate. This does not assert that the mathematics is false or that a particular premise remains open.
- `fresh_project_build` records whether project artifacts were rebuilt from scratch. Use `--fresh` for release evidence.

The GitHub workflow runs these same commands on Ubuntu with pinned action revisions and a checksum-verified Elan download. It uploads only `.verification/` as an artifact retained for 90 days. Its summary reports success only if the theorem-verification step succeeds. The workflow does not publish the manuscript or deploy a site.

Local evidence certifies only the exact checked local inputs. Archived reports and older workflow runs do not certify this revision. A remote certificate exists only after publication of the relevant revision and a successful workflow run for that revision.
