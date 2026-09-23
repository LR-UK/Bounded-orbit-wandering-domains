# Provenance and review status

EremenkosConjecture is a research formalisation developed with substantial AI assistance
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

## Shared univalence estimates

On 21 September 2026 the five existing univalence and derivative estimates
were moved, with their proofs unchanged apart from the namespace, to
[FunctionTheory](../FunctionTheory/FunctionTheory/Conformal/UnivalenceStability.lean).
The original module exports the former names for compatibility. Axiom audits
name the canonical FunctionTheory declarations because Lean reports aliases
under those canonical names. The full project verification passed after the
refactor, including Challenge and Solution and all 299 selected reports.

## Completed continuum theorem and comparison surface

Theorem 1.2 is now proved in ContinuumCounterexample. Lasse Rempe's guidance
included the large-modulus separation argument for uniform escape of the
whole continuum, the exterior-map construction at a free attached tip, and
using the Section 2 stability lemma once the required space around the sets
is verified. Codex supplied substantial Lean proof development and integration.
The paper's other authors are credited as mathematical source authors; no
independent review or endorsement by them is asserted.

The root Challenge/Solution pair selects four results. Challenge contains
documented dynamics definitions and four deliberate statement holes; Solution
and the proof library contain complete proofs. Lean checks and selected axiom
audits are recorded locally. Comparator, NanoDa and Palomar review have not
been run. See [formalization.yaml](formalization.yaml) and
[Palomar readiness](docs/PALOMAR.md). The repositories remain prepared for
private colleague review and manual upload by the maintainer.
