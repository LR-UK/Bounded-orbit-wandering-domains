# Verification — version 1.4.4, 27 September 2026

The full retained Lean build passed (4,321 Lake jobs; 797 local modules).
Lean is pinned to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The independent Challenge/Solution comparison passed for all ten selected
theorem types and 36 supporting declarations. The six revised-paper statements
and the unchanged original entire-function theorem are joined by three proved
corollaries: no wandering components for compact surface self-maps, its
Riemann-sphere specialisation, and no wandering domains for finite-type
transcendental entire functions.

All 43 declaration records from the preceding consolidated submission are
identical. Its proof-library source hashes are also unchanged; Solution adds
one import, and the new corollaries occupy one small additional module.
The original entire theorem still has its exact earlier name and compiled type.
The expanded ten-statement review compiled, including a specialisation of the
sphere corollary using the standard sphere atlas without an atlas hypothesis.

The ten proofs use only `propext`, `Classical.choice` and `Quot.sound`.
The current proof closure has 772 local modules; the full retained proof closure
has 794. Both passed the source check for holes, custom axioms, native_decide
and challenge imports. Challenge proof placeholders are intentional and occur
only in independent specifications. The attribution audit passed: 12 licence
texts, 51 attribution files and 274 vendored headers.

Reproduce with `python3 scripts/verify_paper.py --all`,
`python3 scripts/audit_structure.py` and
`python3 -X utf8 scripts/audit_attribution.py`.
Evidence: `verification/paper-submission.json`,
`verification/no-wandering-release.json`, the current paper build, declaration
and axiom logs, and `verification/no-wandering-currentstatements.log`.
Ordinary style warnings and challenge-placeholder warnings are allowed.
Saved logs have trailing whitespace normalised.

## Scope of the added corollaries

The rational statement uses open holomorphic self-maps of the whole compact
sphere, including infinity. Its intrinsic formulation does not introduce
polynomial quotients or assert a new equivalence theorem with that encoding.
The finite-singular-value entire statement explicitly assumes transcendence;
polynomial dynamics is included among rational maps. No finite-type meromorphic
no-wandering corollary or Baker–Kotus–Lü generalisation is claimed.

The README and metadata incorporate Lasse Rempe's revised paper background.
The positive-area paragraph records the exact existing Lean hypotheses.

## Historical evidence and external checks

`verification/submission-consolidation.json` records version 1.4.3, including
the exact preservation of the original theorem and simultaneous current/legacy
imports. `verification/layout-audit.json` and the layout comparison logs record
version 1.4.2. BUILD_AUDIT.md and `verification/build-audit.json` describe the
version 1.4.1 performance audit. Their timings are not cold-build measurements.

Official sandboxed Comparator and NanoDa/con-ron replay were not run in this
Windows session. The supplied Linux CI performs those checks after upload.
The pinned metadata checker requires PyYAML, absent from the local runtime;
verification/metadata.json explicitly records that validation was not run.
The older report is preserved in history/metadata-before-1.4.4.json.
No public upload, acceptance of this new package or independent human review
is claimed. The first registered version is linked in README.md.
