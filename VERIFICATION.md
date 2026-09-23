# Verification of the local point-orbit update

This file records checks of project version 1.1.0, prepared 23 September 2026.
The submission uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; the toolchain and dependency pins
are unchanged from version 1.0.0. The previous submission remains separate.

The build and diagnostic audit **passed**. The authoritative local report is
`verification/submission.json`; the final Lake output is `verification/build.log`.

| Check | Actual result |
| --- | --- |
| Submission, Challenge, supporting library and covering entry point | Build passed; 4,187 Lake jobs |
| Local modules in the submission dependency graph | 397 compiled |
| Public theorem types | 2 matched in independent environments |
| Supporting definition types and bodies | 7 matched |
| Transitive axiom reports | 51 checked; only the three standard axioms |
| Main project Lean source scan | 142 files; no extra axioms, native_decide or proof holes outside Challenge |
| Challenge | 135 lines; two intentional placeholders; Mathlib-only direct imports |
| Unexpected build warnings | None |
| Palomar metadata contract | Passed |
| Palomar Comparator configuration validation | Passed |
| Attribution audit | Passed |
| Official Comparator, NanoDa and con-ron replay | Pending for this version; required CI check supplied |

The new local point-orbit theorem and both final public theorems use only
`propext`, `Classical.choice` and `Quot.sound`. The local statement now assumes
only point-orbit containment in K; eventual injectivity is derived. Its exact
scope is described in `LOCAL_THEOREM_UPDATE.md` and `Challenge.lean`.

A comparison with version 1.0.0 confirms that the entire-function theorem's
elaborated type and all seven retained definition types/bodies are unchanged.
The new local type differs as intended. All dependency sources, licence texts
and third-party notices are unchanged. These checks are recorded in
`verification/local-orbit-regression.json`. The main Lean source changes are
also available as `verification/local-orbit-source.patch`.

## Checks and their scope

- `scripts/verify_submission.py` builds the submitted development, compares
  the two theorem types and seven supporting definition types/bodies in
  separate environments, scans project proof source, and checks transitive
  axiom reports. Its expression comparison is diagnostic, not the official
  Comparator. Only binder display names and nonsemantic metadata are erased.
- `scripts/verify_metadata.py` runs the unmodified mechanical metadata contract
  from PalomarSubmission commit `e48a86d0495356b5131a92c9406aa6e27cf99e56`.
- The current comparator.json passes that verifier's `load_comparator_config`
  validation. Configuration validation does not run Comparator.
- `scripts/audit_attribution.py` checks included licence texts, retained source
  headers and attribution records. It is a packaging check.
- `scripts/verify-comparator.sh` runs Palomar's bundled Comparator and the
  NanoDa and con-ron kernels through the protected configuration.

The version 1.0.0 Comparator attempt failed before comparison because this
environment does not allow bubblewrap to create its user-namespace mapping
(`Operation not permitted`). The original log is retained under
`history/version-1.0.0/comparator.log`. It was not rerun for version 1.1.0 in
this same environment. No successful official Comparator or independent-kernel
replay is claimed for the new version. The supplied GitHub Actions workflow
runs that check on a Linux runner with bubblewrap; this remains a required
gate for the final submission snapshot. No sandbox check is disabled.

## Reproduce

Run the commands in README.md from the repository root. Cache retrieval walks
local proof imports before requesting the required Mathlib caches. All active
path dependencies are contained in this package; external Git dependencies
are pinned in lake-manifest.json.

Challenge has two deliberate theorem placeholders and imports only Mathlib.
Solution does not import Challenge. No independent human review, public
submission or registry acceptance of this version is claimed.

The archive's verification/package-sources.json records SHA-256 hashes of all
included files except itself. It detects changes to the prepared package;
it is not a public Git commit or a registry verification result. Historical
logs and the earlier toolchain-port report describe their recorded baselines,
not an additional check of version 1.1.0.
