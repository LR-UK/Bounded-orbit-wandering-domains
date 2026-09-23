# ComplexDynamics

**Start here:** [Main results](MAIN_RESULTS.md) · [Exact Lean statements](ComplexDynamics/MainTheorems.lean) · [Proof map](PROOF_MAP.md) · [Classical results](CLASSICAL_RESULTS.md) · [Module index](docs/MODULE_INDEX.md)

[Future dynamics for the Eremenko paper](docs/EREMENKO_FUTURE.md) records
the remaining Fatou-component, maverick and fast-escape foundations.
It is a plan, with no additional proved coverage.

Research version prepared for private review. See [PROVENANCE.md](PROVENANCE.md)
for development and review status.

A reusable Lean library for complex dynamics, beginning with entire functions,
escaping sets, spherical normality, Fatou sets, and Julia sets.

The normality and spherical foundations are adapted from
[LR-UK/exp-chaotic](https://github.com/LR-UK/exp-chaotic), by Lasse Rempe.
See `THIRD_PARTY_NOTICES.md`. The current library builds and passes 44 selected
axiom audits. `STATUS.md` records the checked coverage and the foundations that
remain for future development.

Uses Lean 4.34.0 and the same pinned Mathlib revision as ComplexApproximation.
Build with `lake build`. On Windows, `scripts/verify.ps1` also checks the source
integrity and theorem axioms. The sibling EremenkosConjecture project uses this
library for all results of Section 3 of the supplied paper.

For a portable complete check, run `python scripts/verify.py`. The project has
no dependency on the other two research repositories. Collaboration and
future Mathlib work are described in `CONTRIBUTING.md` and `ROADMAP.md`.
Apache 2.0; see `LICENSE` and `PROVENANCE.md`.
