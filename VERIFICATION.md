# Verification - consolidated submission 1.4.3, 27 September 2026

The complete retained local build passed (4,320 Lake jobs; 796 local modules).
Lean is pinned to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The current `Challenge` / `Solution` pair passed the local independent comparison
of seven theorem types and 36 supporting declarations. These comprise all six
revised-paper targets and the unchanged original entire-function bounded-orbit
statement. Every one of the previous 42 paper declaration records is identical
to the preceding release. The newly selected original theorem's compiled type
is identical to its earlier legacy-solution record; its challenge statement
was copied verbatim, including its original declaration name and hypotheses.

The original proof was moved verbatim to a shared library module. Both current
and legacy solutions can be imported together without a name collision. The
expanded statement review file also compiled successfully.

All seven target proofs use only `propext`, `Classical.choice` and `Quot.sound`.
The main proof closure has 771 local modules; the full retained proof closure
has 793. Both passed the source check for holes, custom axioms, native_decide
and challenge imports. The additional module contains the shared original
entire-function theorem; no duplicate proof or extra heavy dependency was added.

Reproduce with `python3 scripts/verify_paper.py --all`.
Current evidence: `verification/paper-submission.json`,
`verification/submission-consolidation.json`, `verification/paper-build.log`,
the paper declaration and axiom logs, and `verification/unified-*.log`.
The attribution audit is `scripts/audit_attribution.py`.
Ordinary style warnings and deliberate challenge-placeholder warnings are allowed.
Saved logs have trailing whitespace normalized.

## Historical evidence and external checks

The preceding version's two legacy comparisons and library-umbrella build are
recorded in `verification/layout-legacy-comparison.json` and layout logs.
`verification/layout-audit.json` describes version 1.4.2; BUILD_AUDIT.md and
`verification/build-audit.json` describe the version 1.4.1 performance audit.
Those historical reports use the module names current at their respective dates.

Official sandboxed Comparator and NanoDa/con-ron replay were not run in this
Windows session. The supplied Linux CI performs those checks after upload.
The metadata checker requires PyYAML, absent from the local Python runtime;
the older metadata report is not a validation of this updated metadata.
No public upload, registry acceptance or independent human review is claimed.
