# Verification — prepared GitHub update 1.2.0

The strict submission audit passed on 24 September 2026. The full build completed
**4,463 Lake jobs**, including NewResults and both independent Challenge/proof
configurations. Lean is pinned to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

| Check | Result |
| --- | --- |
| Combined library and both Challenge/proof pairs | Passed |
| Independent theorem-type comparisons | 3 passed across two configurations |
| Definition types and bodies | 7 in bounded-orbit configuration; 9 in singular-limit configuration; all matched |
| Transitive axiom reports | 56 distinct declarations; only propext, Classical.choice, Quot.sound |
| Project, RiemannDynamics, RMT4, Eremenko–Lyubich and Ray source scan | 285 Lean files; no holes or extra axioms outside Challenges |
| Unexpected warnings | None |
| Intentional statement placeholders | 2 in Challenge; 1 in SingularLimitsChallenge |
| Metadata contract | Passed |
| Attribution packaging | Passed; 12 licence texts, 51 attribution records |
| Official Comparator and independent-kernel replay | Pending in a supported environment; both configurations included in CI |

The authoritative report is `verification/submission.json`, with `build.log`,
axiom logs and four declaration-export logs in the same directory. Both
Challenge files remain below the preferred 300-line / 32 KiB size and import
only pinned Mathlib modules. Their supporting definitions are compared exactly,
including singular values, Fatou normality and the compact sphere uniformity.
The singular-limit Challenge controls a Mathlib instance during definition
elaboration to reproduce the original definitions' elaborated expressions;
its theorem uses the same standard complex structures as the proved theorem.

Reproduce the strict checks:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify_submission.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

`verify_completion.py` is now an alias for this strict audit. Earlier completion
reports and historical logs describe their earlier snapshots; they are not the
current authority. The eight dependency warning fixes retain theorem statements,
proof meaning and original authorship; their exact diff is recorded in
`verification/update-warning-compatibility.patch`.

## Remaining official replay

The current environment rejects bubblewrap's user-namespace setup with
`Operation not permitted`. See `verification/comparator-environment-check.log`.
No sandbox restriction or independent-kernel requirement was disabled. The CI
workflow runs the bundled Comparator, NanoDa and con-ron for both configurations.
No official replay pass, publication, registry submission or acceptance is claimed.

A separate full standalone FunctionTheory audit was attempted after its source
cleanup but its separate dependency fetch was blocked by network access. That
attempt is not a standalone-audit pass; the complete dependency closure used by
this project was built successfully from the root project. Dependency status
notes distinguish these scopes. No additional mathematical dependency assumptions
are introduced by this distinction.

The entire singular-limit theorem has its own independent Challenge. The two
sphere area bounds are proved and audited supporting results, without separate
registry configurations. No local-map or meromorphic singular-limit extension
is claimed.
