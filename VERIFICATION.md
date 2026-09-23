# Verification of the unconditional submission

This file records checks of version 1.0.0, prepared 23 September 2026.
The submission uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The original Lean 4.34 development and conditional submission were preserved
separately. Logs under history are historical, not evidence for this toolchain.

The current-toolchain build and diagnostic audit **passed**. The authoritative
local report is `verification/submission.json`; the final Lake output is
`verification/build.log`.

| Check | Actual result |
| --- | --- |
| Submission, Challenge, supporting library and covering entry point | Build passed |
| Public theorem types | 2 matched in independent environments |
| Supporting definition types and bodies | 8 matched |
| Transitive axiom reports | 50 checked; only the three standard axioms |
| Main project Lean source scan | 141 files; no extra axioms, native_decide or proof holes outside Challenge |
| Challenge | 141 lines; two intentional placeholders; Mathlib-only direct imports |
| Unexpected build warnings | None |
| Current Palomar metadata contract | Passed |
| Current Palomar Comparator configuration validation | Passed |
| Official Comparator, NanoDa and con-ron replay | Blocked locally by bubblewrap user-namespace restriction; CI check supplied |

The six core unconditional axiom reports include covering existence, total
area, the resulting classical metric facts and both final dynamical theorems.
The two public Solution aliases are also audited. All use only `propext`,
`Classical.choice` and `Quot.sound`. The new-toolchain port required no Lean
proof-source changes relative to the assembled unconditional Lean 4.34 baseline;
see `verification/toolchain435-changes.json` and its patch.

## Checks and their scope

- `scripts/verify_submission.py` builds the submitted development, compares
  the two theorem types and eight supporting definition types/bodies in
  separate environments, scans project proof source, and checks transitive
  axiom reports. Its local expression comparison is diagnostic, not the
  official Comparator. Only binder display names and metadata are erased.
- `scripts/verify_metadata.py` runs the unmodified mechanical metadata contract
  from PalomarSubmission commit `e48a86d0495356b5131a92c9406aa6e27cf99e56`.
  The report is verification/metadata.json. This does not constitute policy
  review, human mathematical review or registry acceptance.
- `scripts/audit_attribution.py` verifies included licence texts, retained
  source headers, attribution records and links. It is a packaging check.
- `scripts/verify-comparator.sh` follows the current PalomarTemplate runner,
  enabling the toolchain's bundled NanoDa and con-ron kernels in a temporary
  protected configuration. They are not controlled by the submitted JSON.

The current environment does not allow bubblewrap to create its user-namespace
mapping (`Operation not permitted`). Consequently no successful official
Comparator or independent-kernel replay is claimed here. The supplied GitHub
Actions workflow runs the same check on a Linux runner with bubblewrap.
This gate must pass before treating the package as fully checked for submission.
No sandbox check is disabled or bypassed.

## Reproduce

Run the commands in README.md from the repository root. Cache retrieval walks
local proof imports before requesting the required Mathlib caches. All active
path dependencies are contained in this package; external Git dependencies
are pinned in lake-manifest.json.

Challenge has two deliberate theorem placeholders and imports only Mathlib.
Solution does not import Challenge. The permitted axiom set is exactly
`propext`, `Classical.choice`, `Quot.sound`.

The archive's verification/package-sources.json records SHA-256 hashes of all
included files except itself. It detects changes to the prepared package;
it is not a public Git commit or a registry verification result.
