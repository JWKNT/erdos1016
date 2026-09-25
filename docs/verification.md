# Theorem verification

Install the pinned Lean 4.19.0 toolchain and Mathlib dependency artifacts, then run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py --fresh --jobs 2
```

The verifier rebuilds every active library module from source with at most two concurrent local builds. It requires the library to equal the umbrella's import closure, screens source files for proof admissions and unsafe evaluation, and checks the pinned dependency environment before compiling. Dependency artifacts are reused; the project's previous build is moved aside for a fresh run.

`audits/TheoremAudit.lean` verifies more than an axiom list. It independently spells out the conclusion for every natural number `n ≥ 3`, both with the natural excess and with the integer minimum-edge count minus `n`. Lean metaprogramming requires `Erdos1016.mainTheorem` to have exactly the type `Problem1016.MainTheorem`, requires the integer theorem to have the independently expanded type, and requires `ShortProof.fewComponentForestEstimate` to have exactly its unconditional target type. A theorem with an additional mathematical premise cannot pass these checks.

The audit reports kernel axioms for the public endpoints and the principal ingredients of the shorter proof, including the actual retained-cycle supply, link bound, weighted forest estimate, contraction law, small-cut bound, and descent. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. The log checker requires every named report and all three checked statement markers, and rejects conditional development logs, Lean errors, proof admissions, and compiler-trust axioms.

The schema-version-3 report is `.verification/verification.json`; detailed rebuild logs and `theorem-audit.log` are alongside it. The report binds the result to hashes of the library source set and the verification inputs: source, audits, scripts, toolchain, dependency manifest, and workflow. A change during checking fails verification.

- `status: passed`, `kernel_checks_status: passed`, `formalization_status: complete`, and `unconditional_main_theorem_proved: true` appear together only after every required check succeeds and the input hash is unchanged.
- Running or failed checks use `formalization_status: unverified` and `unconditional_main_theorem_proved: false`. They provide no completed certificate. This does not assert that the mathematics is false or that a particular premise remains open.
- `fresh_project_build` records whether project artifacts were rebuilt from scratch. Use `--fresh` for release evidence.

The GitHub workflow runs these same commands on Ubuntu with pinned action revisions and a checksum-verified Elan download. It uploads only `.verification/` as an artifact retained for 90 days. Its summary claims success only if the theorem-verification step succeeds. It neither publishes the manuscript nor deploys a site.

Local evidence certifies only the exact checked local inputs. Archived reports and older workflow runs do not certify this revision; a remote certificate exists only after the relevant revision is published and its own workflow succeeds.
