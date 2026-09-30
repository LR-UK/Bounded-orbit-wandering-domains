# Verification — version 1.8.1, 30 September 2026

The configured Lean build passed for `Solution`, the independent `Challenge`,
and `BoundedWanderingDomains.All`. All 19 selected theorem
declarations and 53 supporting declarations
match between Challenge and Solution. The build has zero ordinary compiler or
linter warnings. The nineteen Challenge `sorry` warnings are intentional statement
placeholders; the solution does not import Challenge.

This version corrects the definition of regular values: covering neighbourhoods
may have empty fibres, and need not be contained in the range. The general
definition applies to maps between different spaces. Lean proves that singular
values lie in the closure of the image. Regression checks verify that an empty
source has no singular values and that the omitted point of the punctured-plane
inclusion remains singular.

The public singular-encounter statement quantifies over full preimage components
U_n directly and uses the singular values of the actual restricted maps U_n → D_n.
Internal base-point constructions are connected to this formulation by a proved
equality. The author's explanatory comments and revised abstract are retained,
with eventual visit times, one-step preimages, and source escape made precise.
All dependent proofs were rebuilt with the corrected definition. In particular,
the general surface conclusions use the corrected singular set throughout.

The transitive proof audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. Metadata, attribution and source-structure checks passed.

## Reproduce the checks

```sh
python3 scripts/verify_paper.py --all
python3 scripts/verify_metadata.py
python3 scripts/audit_structure.py
python3 -X utf8 scripts/audit_attribution.py
```

The metadata checker needs PyYAML. Preserve existing `.lake` directories when
updating. Lean and Mathlib remain pinned to `leanprover/lean4:v4.35.0-rc2` and
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Changed project modules rebuild;
unchanged dependencies can retain their cached artifacts.

Evidence is recorded in `verification/paper-submission.json`, its build,
declaration and axiom logs, `verification/regular-values-regression.log`,
`verification/regular-values-update.json`, `verification/metadata.json`,
`verification/attribution.json`, and `verification/structure-audit.json`.

## External verification

The pinned Comparator declaration-comparison core passed on separately imported
compiled Challenge and Solution environments, including transitive checks.
The official sandboxed export and independent-kernel pipeline was not run locally
on Windows. GitHub must confirm that pipeline after upload. Local verification
does not claim registry acceptance or an independent human mathematical review.
