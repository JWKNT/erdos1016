# Verification

Run the commands in the [README](../README.md) from the repository root. Use the committed `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` without updating dependency revisions.

## What the verifier checks

`python3 scripts/verify.py --fresh --jobs 2` performs these checks in order:

1. **Source inventory.** Every library module must belong to the final theorem's import closure. The inventory rejects missing imports, import cycles, duplicate imports, identical source files, and prohibited proof shortcuts. It also checks descriptive module names.
2. **Pinned environment.** Dependency checkouts must match the revisions in `lake-manifest.json` and have no changes to tracked files. The mathlib pin must agree with `lakefile.lean`, and the selected Lean toolchain must be installed. Missing or stale dependency caches cause failure; verification does not update pins.
3. **Fresh project build.** `--fresh` moves the previous project build aside and rebuilds all project modules in dependency order. `--jobs 2` bounds concurrent builds. The pinned dependency cache is reused.
4. **Statement and axiom audit.** [MainTheoremAudit.lean](../audits/MainTheoremAudit.lean) checks both public theorems against their expanded inequalities. It independently checks that `Erdos1016.mainTheorem` has exactly type `Erdos1016.Problem1016.MainTheorem`, with no additional hypotheses. Nine axiom reports cover the two public statements and key intermediate results. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; admissions and compiler-trust axioms are rejected.
5. **Stable verification inputs.** The proof sources, audit, dependency configuration, verification scripts, and workflow must not change during verification.

Source screening is a lexical and import-graph check; it cannot establish mathematical correctness. The fresh Lean build checks the elaborated proof terms, while the separate statement audit checks what was proved and the axioms on which it depends. The allowed axioms are Lean's standard propositional extensionality, classical choice, and quotient soundness axioms.

The public natural-number formulation minimizes `|E| − n` over pancyclic simple graphs on `Fin n`. The integer formulation first minimizes `|E|` and then subtracts `n` in the integers. Their equality for `n ≥ 3` is proved in [MinimumEdgesStatement.lean](../Erdos1016/Extremal/MinimumEdgesStatement.lean). The binary iterated logarithm is defined in [LogStarTowers.lean](../Erdos1016/Extremal/Recurrence/LogStarTowers.lean).

## Verification record

The main result is `.verification/verification.json`. It records:

- `status` and any errors, the check list, and whether a fresh build was requested;
- the Git commit, working-tree cleanliness, and CI run URL when available;
- the Lean version, pinned dependency revisions, and source counts;
- a source-set hash and a hash of the verification inputs;
- the reported axiom dependencies of the audited declarations.

Supporting files include `inventory.json`, `main-theorem-audit.log`, and the build status and per-module logs under `build/`. A failed run can also produce a report: check `status`, the command's exit status, and the logs. A report left by an earlier run is not evidence for changed sources.

The hashes bind the record to the checked source and verification configuration. They do not replace Lean verification or establish that the definitions express the intended mathematical problem; the statement files and audit remain available for inspection.

## GitHub Actions evidence

[The verification workflow](https://github.com/JWKNT/erdos1016/actions/workflows/verify.yml) runs on pushes to `main`, pull requests, and manual dispatches. It installs the pinned Lean toolchain, retrieves the pinned dependency cache, tests the verification tools, and runs the same fresh verification command. Setup rejects changes to the dependency manifest.

For a specific result, use the workflow run's permalink, of the form `https://github.com/JWKNT/erdos1016/actions/runs/<run-id>`, and inspect its commit and job outcome. The README badge follows the workflow's current status; it is not a permanent reference to a particular checked revision.

Each run uploads the available `.verification/` directory as an artifact named `verification-<run-id>-<attempt>`, including when verification fails. Download it to inspect the JSON record and logs alongside the run's commit and source. Artifacts are retained for 90 days; save them separately when a durable copy is needed. A successful run and its matching record provide reproducible evidence for that revision, not for later edits.

## Re-running after changes

Use the fresh verification command before relying on a changed proof. If the verifier reports missing dependency caches, repeat `lake exe cache get` with the committed manifest intact. Do not use `lake update` as a repair step. For build failures, inspect `.verification/build/status.json` and the corresponding module log; for statement or axiom failures, inspect `.verification/main-theorem-audit.log`.
