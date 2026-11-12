# Verification and reproduction

## Completed development verification

The verified development version is `63e4377a3f62cdf4a989b2559d8f9c7341c78789`. The complete source compiled under Lean 4.34.0 with the exact dependency revisions in `lake-manifest.json`. The axiom audit covered 2,602 exact declarations, including all four closed target theorems. Every reported dependency belongs to `propext`, `Classical.choice`, and `Quot.sound`.

The final `leanchecker --fresh -v Challenge` run exited successfully after 1,460.406 seconds at 2026-11-12 21:31:42 UTC. It started with an empty kernel environment and replayed the complete imported proof closure. The record bound 890 project object files and checked that project sources, object files, and runtime hashes stayed fixed throughout the run.

The integrated build resumed source-matched completed modules after an earlier output-writing failure. The final compilation, axiom audit, and full fresh replay all exited successfully. These records are contributor-run technical checks. Mathematical review and the prize organizer's independent reproduction remain separate review steps.

## Public source snapshot

All 892 canonical Lean source files and the three toolchain/dependency configuration files were compared byte-for-byte against both the before-run and after-run source hashes. This public repository is a clean source snapshot with accompanying mathematical notes and verification evidence. Its new Git commit has a later publication timestamp than the development commit. The preserved development timestamps are submitted as evidence for review.

- [Source hashes](source-snapshot.json)
- [Original final audit](original-run/periodic-refinement-combined-01/audit_summary.json)
- [Original integrated build receipt](original-run/periodic-refinement-combined-01/result.json)
- [Original axiom output](original-run/periodic-refinement-combined-01/axiom-audit.log)
- [Original fresh replay receipt](original-run/periodic-refinement-fresh-01/result.json)
- [Fresh replay output](original-run/periodic-refinement-fresh-01/kernel-fresh.log)
- [Evidence hashes](evidence-hashes.json)

The raw run records retain the original local paths and the stage statuses recorded at each step. The final audit gives the completed outcome. Reproduction on a new machine uses the public repository layout and commands below.

## Reproduction commands

Install the pinned Lean toolchain, then run these commands from the repository root.

```sh
python scripts/check_sources.py
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean verification/CheckAxioms.lean
lake env leanchecker --fresh -v Challenge
```

`lake build` builds the complete root library. `Challenge.lean` includes the closed stronger classification and explicitly checks the original positive-prefix counting interpretation. `verification/CheckAxioms.lean` prints the type and complete axiom dependencies of every audited declaration. The full manifest is in `verification/axioms.json`.

The public-snapshot check records reuse of the exact verified dependency and project outputs. It checks source identity before re-elaborating the public entry point. It does not represent a second complete fresh replay. [Public-snapshot check](publication-check.json)
