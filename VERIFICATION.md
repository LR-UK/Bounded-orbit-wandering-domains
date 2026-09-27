# Verification — completed formalisation, 27 September 2026

The complete local build passed (4,705 targets). The pinned compiler is
Lean 4.35.0-rc2; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The dedicated revised-paper audit passed:

- Six independent theorem types match.
- Thirty-six supporting declarations match, including definition bodies and
  the local-map constructor type. Only bound-variable display names and
  nonsemantic expression metadata are erased by the local comparison.
- Every target's transitive axioms are contained in
  `propext`, `Classical.choice`, and `Quot.sound`.
- 773 local modules in PaperSolution's import closure were scanned; no `sorry`,
  `admit`, `native_decide`, custom axioms or challenge imports occur there.
- The retained legacy entry points also compile. An old malformed finite-removal
  statement and an obsolete multiplication lemma were repaired during this check.

`verification/paper-submission.json` is the machine-readable audit report.
The corresponding build, axiom and independent declaration logs are in
`verification/paper-*.log` and `verification/paper*-declarations.log`.
`verification/full-build.log` records the broader build. Ordinary unused-variable
and style lints are permitted; challenge proof-placeholder warnings are expected.
Saved build logs have trailing whitespace normalized.

Reproduce the main audit with `python3 scripts/verify_paper.py`. The source
dependency inventory is also summarized in `verification/paper-dependencies.md`.
The attribution audit is supplied as `scripts/audit_attribution.py`.

## Separate external checks

Official sandboxed Comparator and NanoDa/con-ron replay were not run in this
Windows session. The toolchain requires Linux bubblewrap for that workflow;
no sandbox or kernel check was bypassed. The unchanged protected runner and
updated GitHub workflow run these checks after upload.

`formalization.yaml` was updated while preserving the attribution records.
The pinned metadata contract is supplied, but its current run requires PyYAML,
which is unavailable in the local Python runtime. CI installs it and invokes
`scripts/verify_metadata.py`. The older `verification/metadata.json` describes
the earlier metadata, not a fresh validation of this revision.

No independent human review, public upload, registry submission or acceptance
is claimed. Historical verification reports are retained separately and do not
replace this revision's report.
