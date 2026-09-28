# Verification — version 1.5.0, 28 September 2026

The full retained Lean build passed: 4,324 Lake jobs, including the current
submission, retained earlier statements and research entry points. Lean is
pinned to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The independent Challenge/Solution comparison passed for all ten selected
theorem declarations and 35 supporting declarations. Theorem 1.5 now applies
to arbitrary wandering normality components, including multiply connected
ones. Its simple-connectivity hypothesis was removed without adding a
replacement hypothesis. The proof formalises the covering and removable-filling
argument in the six modules under `BoundedWanderingDomains/Surfaces/BKL/`.

Compared with the preceding linter update, 44 of the 45 current declaration
records are identical. The changed record is
`SurfaceDynamics.WanderingDerivedSingularLimitClaim`; the unused supporting
definition `SurfaceDynamics.LocalMap.HasSimplyConnectedComponentOrbit` is no longer a
comparison target. In particular, the original entire-function theorem retains
its exact compiled statement. The other selected statements are unchanged.

All ten proofs depend only on `propext`, `Classical.choice` and `Quot.sound`.
The current proof closure has 777 local modules; the full retained proof closure
has 798. Both passed the source audit for `sorry`, `admit`, custom axioms,
`native_decide` and imports of independent challenges.

## Warnings and supporting checks

There are no ordinary linter warnings in the full build. The 18 remaining
warnings are intentional proof placeholders in the three independent Challenge
files. These specifications are never imported by the solutions. No linter was
disabled. The preceding linter update fixed 385 ordinary warnings, and the new
BKL modules have also been checked and corrected.

The pinned Palomar metadata contract passed using PyYAML 6.0.3. The attribution
audit passed: 12 licence texts, 51 attribution files and 274 vendored headers.
The source-structure audit passed for the active import closures. Existing
auxiliary audit-module name collisions outside those closures are recorded in
its report.

Reproduce the local checks with:

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

Install PyYAML for the metadata checker. Fetch the pinned Mathlib cache first
with `python3 scripts/fetch_cache.py`, and preserve `.lake` when updating.
The final changed-source build took 10.7 minutes;
the complete local build/declaration audit took
13.1 minutes. These measurements used
an existing dependency cache and are not cold-build estimates for other machines.

Evidence is in `verification/paper-submission.json`, `verification/bkl-release.json`,
the paper build/declaration/axiom logs, `verification/paper-check-timings.json`,
`verification/metadata.json`, `verification/attribution.json` and
`verification/structure-audit.json`. Older reports remain historical evidence.

## Statement scope and external verification

The rational corollary uses open holomorphic self-maps of the whole compact
sphere, including infinity. The finite-singular-value entire corollary assumes
transcendence; polynomial dynamics is included in the rational case. A separate
finite-type meromorphic no-wandering corollary is not selected, although the
local derived-set theorem now includes multiply connected components.

The official sandboxed Palomar Comparator and NanoDa/con-ron replay were not
run in this Windows session. The supplied Linux CI runs those checks after
upload; local independent declaration comparison is a separate check.
The standalone FunctionTheory verifier encountered a certificate error in its
separate Mathlib fetch before compilation. All dependency modules imported by
the submitted and retained proofs were checked by the main pinned build.

The README and metadata preserve the author's revised paper background,
including the independent-proof attribution and the planned joint preprint.
