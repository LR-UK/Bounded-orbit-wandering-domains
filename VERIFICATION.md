# Verification — research checkpoint, 24 September 2026

The strict audit passed. The combined Lake build completed 4,487 jobs,
including `SurfaceResearch`. Lean is pinned to 4.35.0-rc2 and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

- Six main Challenge theorem types matched Solution exactly.
- Two legacy singular-limit Challenge theorem types also matched.
- Thirteen supporting definition types and bodies matched in each configuration.
- 78 distinct declarations were audited transitively; only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- 305 project Lean sources were scanned; no unexpected proof holes,
  custom axioms or native decision shortcuts were found.
- No unexpected warnings remain. The six main Challenge placeholders and two
  legacy Challenge placeholders are intentional and are not imported by proofs.
- Metadata contract and attribution audits passed.

`verification/submission.json` is the authoritative machine-readable report.
`verification/surface-axioms.log` includes the surface cutoff, compactification,
partial-iteration and intrinsic metric theorems. The named surface dynamical
propositions in `Surfaces/Statements.lean` are **unproved targets**, not theorems.
An audit pass does not establish those propositions.

Reproduce the checks:

```sh
LEAN_NUM_THREADS=4 python3 scripts/verify_submission.py
python3 scripts/verify_metadata.py
python3 scripts/audit_attribution.py
```

Official Comparator / independent-kernel replay has not been run for this
research checkpoint. The earlier environment rejected bubblewrap user-namespace
setup. No sandbox requirement or independent-kernel check has been weakened.
The protected replay scripts and CI configuration remain supplied. No public
push, registry submission or acceptance is claimed.

Stable 1.3.0 remains at `4a2c4b75c71541f569b7ae34bde616bcca66c07a`.
See `RIEMANN_SURFACE_RESEARCH.md` for exact completed and incomplete scope.
