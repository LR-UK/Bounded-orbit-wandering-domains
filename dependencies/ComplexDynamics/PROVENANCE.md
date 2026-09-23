# Provenance and review status

ComplexDynamics is a research formalisation developed with substantial AI assistance
under Lasse Rempe's direction. The source was prepared for private review in
September 2026. Lean builds and axiom audits establish the checked proof terms;
the mathematical statement interfaces, organisation, and maintainability still
need expert review before proposing material for Mathlib.

The original project code is distributed under Apache 2.0; see `LICENSE`.
Retain third-party authorship and licence notices when reusing source. Mathematical
references and imported developments are recorded in the source documentation.
No claim of priority over other formalisation projects is made.

`STATUS.md` distinguishes proved results from further work. `verification/`
contains local evidence, and `scripts/verify.py` regenerates the checks. A
prepared GitHub workflow is not evidence that GitHub-hosted verification ran.
