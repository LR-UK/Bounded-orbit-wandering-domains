# Verification - version 1.8.0, 29 September 2026

## Comparator configuration correction

The first v1.8.0 CI run completed both Lean builds but rejected
`SurfaceDynamics.EmbeddedDisc` in Comparator's `definition_names`: it is an
inductive structure, not a definition hole. This entry has been removed.
The structure remains checked transitively by Comparator and explicitly by
the local supporting-declaration comparison; its carrier definition stays
in `definition_names`. No mathematical statement or proof was changed.

Both declaration exporters now validate configured constant kinds against
the Lean environment. The local audit runs the Challenge check before the
Solution build, so this class of configuration error fails earlier.
See `verification/comparator-kind-fix.json` for the correction's checks.

## Mathematical verification

The full configured Lean build passed (4,301 Lake jobs), including
`Solution`, the sole independent `Challenge`, and `BoundedWanderingDomains.All`.
All nineteen selected theorem declarations and 51 supporting declarations match
between Challenge and Solution. All 57 declaration records exported by version
1.7.1 are unchanged, including the exact original entire-function bounded-orbit
statement. The three additions are the combined wandering-domain theorem, its
almost-everywhere counterpart, and explicit meromorphic derived-singular accumulation.

The main bounded-source, derived-singular and area statements now follow from
the combined componentwise encounter proof. Finite-type and classical
no-wandering corollaries follow through derived-singular accumulation. The
meromorphic model has the compact sphere as its target, so ambient escape is
impossible; its new selected theorem states derived-singular accumulation
without that alternative. See [statement alignment](PAPER_STATEMENT_ALIGNMENT.md)
and the [proof guide](PAPER_PROOF_GUIDE.md).

The cleanup removed 118 obsolete first-party, legacy and research Lean files,
including earlier independent main proofs. Attributed supporting libraries,
their source snapshots and licence texts are retained. The selected solution
closure contains 778 local modules; the current
proof-library entry point adds one. These 779
proof modules passed the scan for proof holes, custom axioms, `native_decide`
and imports of independent challenges. All 1,336
retained Lean sources pass the module-header check. This does not claim that
unused vendored modules were compiled.

Every selected proof uses only `propext`, `Classical.choice` and `Quot.sound`.
The configured build has zero ordinary compiler or linter warnings. Its nineteen
warnings are intentional statement placeholders in `Challenge.lean`, which the
proofs never import. No linter was disabled.

The pinned metadata contract, attribution and source-structure checks passed.
The attribution audit covers 12 licence texts, 51 attribution files and 274
vendored headers. The abstract explicitly includes the combined, positive-area,
almost-everywhere and classical no-wandering results, and explains the compact
sphere target for entire and meromorphic functions.

## Reproduce the checks

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The metadata checker needs PyYAML. For a fresh checkout run
`python3 scripts/fetch_cache.py` first. Preserve existing `.lake` directories
when updating. The Lean and Mathlib pins are unchanged:
`leanprover/lean4:v4.35.0-rc2` and
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Changed project modules need rebuilding; unchanged dependencies remain cached.
Recorded recheck timings use existing compiled artifacts and are not estimates
for a fresh build or another computer.

Evidence is in `verification/combined-release.json`,
`verification/paper-submission.json`, the paper build/declaration/axiom logs,
`verification/paper-check-timings.json`, `verification/module-headers.json`,
`verification/metadata.json`, `verification/attribution.json` and
`verification/structure-audit.json`. The source manifest records the exact
released files. Obsolete release reports, handoffs and diagnostic logs are removed.

## External verification

The official sandboxed Palomar Comparator and NanoDa/con-ron replay were not run
locally for this version. The included Linux workflow runs them after upload.
Local declaration comparison, Lean kernel checks and axiom audits are distinct
from those external checks and registry review or acceptance.
