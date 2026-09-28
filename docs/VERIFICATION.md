# Verification — version 1.7.0, 28 September 2026

The full retained Lean build passed: 4,336 Lake jobs, including the current
submission, earlier statements and research entry points. The Lean and Mathlib
pins are unchanged (`leanprover/lean4:v4.35.0-rc2` and
`065356127b1dc0016f66b7283ce0ce2c4055aa55`).

All sixteen selected theorem declarations and 41 supporting declarations match
between the independent Challenge and Solution. All 52 compiled declaration
records from version 1.6.0 are unchanged. The five additions comprise the general
finite-type theorem, the meromorphic class S corollary and three definitions
for the genuine sphere-valued map and its singular values. The original entire
bounded-orbit statement retains its exact name and compiled type.

The finite-type theorem applies to an open holomorphic map from any open subset
of a compact Riemann surface to that surface. Removable punctures are permitted.
It is deduced directly from derived-singular accumulation. Every classical
no-wandering corollary now uses this theorem: global compact surfaces, rational
maps, and class S transcendental entire and meromorphic functions. The completed
BKL proof and all compact-set, positive-area and almost-everywhere results remain.

Every selected proof uses only `propext`, `Classical.choice` and `Quot.sound`.
The active proof closure contains 789 local modules; the full retained closure
contains 810. Both passed the scan for proof holes, custom axioms,
`native_decide`, and imports of independent challenges.

## Warnings and supporting checks

The complete build has zero ordinary linter warnings. Its 24 warnings are
intentional `sorry` placeholders in the independent Challenge specifications,
which are never imported by proofs. No linter was disabled.

The pinned Palomar metadata contract passed. The public abstract includes the
positive-area, almost-everywhere and finite-type no-wandering result families,
with rational, entire and meromorphic corollaries. Attribution checks passed
for 12 licence texts, 51 attribution files and 274 vendored headers. The source
structure audit passed; its historical auxiliary tooling records remain.

Reproduce the checks with:

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The metadata checker needs PyYAML. For a fresh checkout run
`python3 scripts/fetch_cache.py` first. Preserve `.lake` when updating. The final
local build and declaration audit took 3.9 minutes with an existing dependency
cache; this is not a cold-build estimate for another machine.

Evidence is in `verification/finite-type-release.json`,
`verification/paper-submission.json`, the paper build/declaration/axiom logs,
`verification/paper-check-timings.json`, `verification/metadata.json`,
`verification/attribution.json` and `verification/structure-audit.json`.
Earlier release reports are historical.

## External verification

The official sandboxed Palomar Comparator and NanoDa/con-ron replay were not run
locally for this version. The included Linux workflow runs them after upload.
Local declaration comparison, Lean kernel checks and axiom audits are distinct
from those external checks and from registry review or acceptance.
