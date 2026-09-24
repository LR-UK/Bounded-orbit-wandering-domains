# Verification of completed formalisation — 24 September 2026

The combined Lean build passed: **4,459 Lake jobs**. The three new results,
the local theorem without simple connectivity, and the existing bounded-orbit
theorem are checked together. Toolchain: Lean 4.35.0-rc2; Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

| Check | Result |
| --- | --- |
| Full supporting library, Submission, Challenge, CoveringSolution, NewResults | Passed |
| Final declarations audited transitively | 7; only propext, Classical.choice, Quot.sound |
| Independent Challenge/Solution theorem types | 2 matched |
| Supporting definition types and bodies | 7 matched |
| Main project and imported EL/Ray source scan | 283 Lean files; no holes or extra axioms outside Challenge |
| Challenge placeholders | Exactly 2, intentional; not imported by Solution |
| Metadata contract | Passed |
| Existing attribution packaging check | Passed; EL/Ray provenance also retained separately |
| Official Comparator and independent-kernel replay | Not run for this snapshot |

The machine-readable report is `verification/completion.json`; corresponding
build, declaration-export and axiom logs have the `completion-` prefix.

There are 83 dependency deprecation/linter warnings in the build, in addition
to the two expected Challenge warnings. These do not represent proof holes.
The historical `verify_submission.py` demands a warning-free dependency build
and is not claimed to pass for this snapshot. It remains unchanged.
`verify_completion.py` records all warnings explicitly, while treating build
errors, proof holes, additional axioms and declaration mismatches as failures.

Reproduce:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify_completion.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

All seven final axiom reports use only Lean's three standard axioms. The source
scan includes the project, RiemannDynamics, RMT4, EremenkoLyubichConstant and Ray.
Transitive axiom checking also covers imported proof dependencies.

The three new results are proved but are not yet included in the independent
Palomar Challenge/comparator configuration. No official registry replay,
publication, acceptance or independent human review is claimed. The earlier
verification narrative is preserved in `history/verification-before-singular-limits.md`;
older JSON/log reports describe their historical snapshots, not this update.
