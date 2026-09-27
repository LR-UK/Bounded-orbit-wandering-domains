# Verification - layout update 1.4.2, 27 September 2026

The complete retained local build passed (4,319 Lake jobs; 795 local modules).
The pinned compiler is Lean 4.35.0-rc2; Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The dedicated revised-paper audit passed:

- Six independent theorem types match.
- Thirty-six supporting declarations match, including definition bodies and
  the local-map constructor type. Only bound-variable display names and
  nonsemantic expression metadata are erased by the local comparison.
- Every target's transitive axioms are contained in
  `propext`, `Classical.choice`, and `Quot.sound`.
- 770 local modules in PaperSolution's import closure were scanned; no `sorry`,
  `admit`, `native_decide`, custom axioms or challenge imports occur there.
  With `--all`, all 792 local proof modules in the retained build passed this scan.
- The retained legacy entry points also compile. The earlier completion check
  repaired an old malformed finite-removal statement and an obsolete
  multiplication lemma. This layout update preserves every Lean statement and proof body.

`verification/paper-submission.json` is the machine-readable audit report.
The corresponding build, axiom and independent declaration logs are in
`verification/paper-*.log` and `verification/paper*-declarations.log`.
`verification/paper-build.log` records the fresh full retained build;
`verification/full-build.log` is the historical version 1.4.1 build log. Ordinary unused-variable
and style lints are permitted; challenge proof-placeholder warnings are expected.
Saved build logs have trailing whitespace normalized.

Reproduce the main audit with `python3 scripts/verify_paper.py`; use `--all`
to include the retained earlier and research entry points. LAYOUT_UPDATE.md records
the current file moves. BUILD_AUDIT.md records the earlier version 1.4.1 results:
the import and duplication audit, supplementary type checks and measured timings.
The source dependency inventory is also summarized in
`verification/paper-dependencies.md`.
The attribution audit is supplied as `scripts/audit_attribution.py`.

The layout comparison checked all 1,371 Lean source files against version 1.4.1.
After accounting for moves, only module import commands differ; no theorem,
definition or proof body changed. The two paper entry files and all vendored
sources are unchanged. Both moved legacy challenge/solution pairs also passed
fresh local elaborated-declaration comparisons (8 theorem comparisons and 26
supporting-declaration comparisons across the two pairs). The moved library
umbrella `BoundedWanderingDomains.All` compiled separately. These results are
in `verification/layout-audit.json`, `verification/layout-legacy-comparison.json`
and the corresponding `verification/layout-*.log` files.

## Separate external checks

Official sandboxed Comparator and NanoDa/con-ron replay were not run in this
Windows session. The toolchain requires Linux bubblewrap for that workflow;
no sandbox or kernel check was bypassed. The unchanged protected runner and
updated GitHub workflow run these checks after upload.

`formalization.yaml` retains the completed version's metadata and attribution
records; the layout update leaves it unchanged.
The pinned metadata contract is supplied, but its current run requires PyYAML,
which is unavailable in the local Python runtime. CI installs it and invokes
`scripts/verify_metadata.py`. The older `verification/metadata.json` describes
the earlier metadata, not a fresh validation of this revision.

No independent human review, public upload, registry submission or acceptance
is claimed. Historical verification reports are retained separately and do not
replace this revision's report.
