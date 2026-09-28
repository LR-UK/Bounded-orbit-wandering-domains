# Verification — version 1.6.0, 28 September 2026

The full retained Lean build passed: 4,333 Lake jobs, including the current
submission, earlier statements and research entry points. Lean remains pinned
to `leanprover/lean4:v4.35.0-rc2`; Mathlib remains pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

All fourteen selected theorem declarations and 38 supporting declarations match
between the independent Challenge and Solution. The seven new records comprise
four theorem statements and three definitions. All 45 records from version 1.5.0
are unchanged except for the requested descriptive theorem names. The original
entire-function theorem retains its exact name and compiled statement.

The new results are compact wandering-orbit derived-singular accumulation,
almost-everywhere source escape, positive-area ambient compact exclusion away
from derived singular values, and almost-everywhere ambient escape or
derived-singular accumulation. The completed BKL proof without simple
connectivity remains included. Measurable wandering sets lie in the
infinite-iteration locus outside normality; every iterate is injective on the
starting set. Nullity is expressed in every chart, and escape concerns a chosen
subsequence rather than permanent escape of the full orbit.

Every selected proof uses only `propext`, `Classical.choice` and `Quot.sound`.
The active proof closure contains 786 local modules; the full retained closure
contains 807. Both passed the scan for proof holes, custom axioms,
`native_decide`, and imports of independent challenges.

## Warnings and supporting checks

The full build has zero ordinary linter warnings. Its 22 warnings are intentional
`sorry` placeholders in the three independent Challenge specifications, which
are never imported by proofs. No linter was disabled. The earlier linter fixes
and the warning-free BKL modules are retained, and all new modules were checked.

The pinned Palomar metadata contract passed with PyYAML 6.0.3. The public abstract
now mentions positive-area wandering sets, almost-everywhere conclusions, and
the classical no-wandering corollaries. The attribution audit passed for all
12 licence texts, 51 attribution files and 274 vendored headers. The structure
audit passed for active import closures; auxiliary audit modules with identical
names outside those closures remain recorded as historical tooling.

Reproduce the checks with:

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The metadata checker needs PyYAML. A fresh checkout should first run
`python3 scripts/fetch_cache.py`. Preserve `.lake` when updating. The final local
build and declaration audit took 3.9 minutes with an existing dependency
cache; this is not a cold-build estimate for another machine.

Evidence is in `verification/ae-release.json`, `verification/paper-submission.json`,
the paper build/declaration/axiom logs, `verification/paper-check-timings.json`,
`verification/metadata.json`, `verification/attribution.json` and
`verification/structure-audit.json`. Earlier release reports are historical.

## External verification

The official sandboxed Palomar Comparator and NanoDa/con-ron replay were not run
locally for this version. The included Linux workflow runs these checks after
upload. The local declaration comparison, Lean kernel checks and axiom audit
are distinct from those external checks and from registry review or acceptance.
