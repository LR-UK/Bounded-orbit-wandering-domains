# Verification evidence

The prepared repository passed `scripts/verify.py` locally on Windows with
the pinned Lean 4.34.0 toolchain. There are 68 selected axiom reports.
`build.log` and `axioms.log` record the checks; `summary.json` records the
targets, time, allowed axioms, and proof-source hashes. Where present,
`targets.log` checks the original Runge challenge interfaces.

Hashes normalise CRLF line endings to LF to match portable Git checkouts.
The selected reports are not a claim that every individual declaration was
separately audited. The complete library build is also required and passed.
The GitHub workflow has been prepared but has not run on GitHub.
