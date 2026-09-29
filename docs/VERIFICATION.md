# Verification — version 1.7.1

This release addresses the module-format rejection of the submitted 1.7.0 commit
`4c99efadab83bde22a17dee28118c67cf17c2ae8`. All 1,385 tracked Lean files now
pass the module-header check. 1,191 files were
ported from the legacy format, with public imports and exposed definitions;
additional visibility adjustments are recorded in
`verification/module-system-migration.json`. Mathematical statement and proof
bodies are unchanged. The user's README is preserved, and the public abstract
retains the edited background with precise wandering-set and escape wording.

The full configured verification build passed (4,334 Lake jobs), including
the current submission, retained proof modules and research entry points. All
sixteen selected theorem declarations and 41 supporting declarations agree
between independent Challenge and Solution and exactly match version 1.7.0.
This includes the entire, meromorphic, local-surface, BKL, positive-area,
almost-everywhere and finite-type result families. No theorem was weakened.

Every selected proof uses only `propext`, `Classical.choice` and `Quot.sound`.
The active proof closure contains 789 local
modules; the full retained proof closure contains
810. Both passed the scan for proof
holes, custom axioms, `native_decide`, and imports of independent challenges.
Checking every source header does not claim that every unused vendored module
was compiled. The standalone dependency checks were attempted but their
separate Mathlib fetch failed certificate validation before compilation;
the root proof closure uses the existing pinned cache. Dependency STATUS files
distinguish this scope from historical standalone audits.

The configured verification build has zero ordinary compiler or linter warnings.
Its 16 warnings are intentional placeholders in the sole project specification,
`Challenge.lean`, which is never imported by proofs. The two obsolete specifications
under `Legacy/` and their four exporters have been removed. The corresponding
proved library results remain available. No linter was disabled.
The verification script now rejects all other build warnings.

The pinned metadata contract, attribution and source-structure checks passed.
The Lean and Mathlib pins remain `leanprover/lean4:v4.35.0-rc2` and
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Reproduce the checks

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The first command includes the module-header check. The metadata checker needs
PyYAML. For a fresh checkout run `python3 scripts/fetch_cache.py` first. Preserve
existing `.lake` directories when updating. The module-format change requires
one substantial rebuild of changed project modules; the final cached recheck
timings are not an estimate for that rebuild or for a fresh machine.

Evidence is in `verification/module-system-release.json`,
`verification/module-system-migration.json`, `verification/module-headers.json`,
`verification/paper-submission.json`, the paper build/declaration/axiom logs,
`verification/paper-check-timings.json`, `verification/metadata.json`,
`verification/attribution.json` and `verification/structure-audit.json`.
Earlier release reports are historical.

## External verification

The official sandboxed Palomar Comparator and NanoDa/con-ron replay were not run
locally for this version. The included Linux workflow runs them after upload.
Local declaration comparison, Lean kernel checks and axiom audits are distinct
from those external checks and from registry review or acceptance.
