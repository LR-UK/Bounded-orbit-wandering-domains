# Contributing

Begin with `README.md`, `STATUS.md`, and `ROADMAP.md`. During private review,
use an issue or a small pull request in this repository to discuss scope.
Keep mathematical statement review distinct from proof refactoring.

## Proof and API standards

- State hypotheses and conclusions faithfully. Definitions and conditional
  lemmas must not conceal the existence theorem being requested.
- Keep the proof library free of placeholders, additional axioms, and unchecked
  native proofs. Selected axiom reports must use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Prefer the actual domain of a locally defined function in user-facing APIs.
  Explain any ambient extension used internally.
- Put reusable analysis and dynamics in the appropriate foundational project.
  Keep paper-specific constructions in EremenkosConjecture.
- Preserve existing imports and theorem names where practical. Discuss a
  breaking API change before undertaking a broad rename.
- Retain attribution, mathematical references, and third-party licence notices.
  Record substantial AI assistance and check its output as ordinary source.

## Validation

Use the pinned toolchain and dependencies. Run `python scripts/verify.py`
(`python3` on systems where appropriate), and include its result in the pull
request. This builds the libraries, scans their sources, and checks every
declaration listed in `scripts/Audit.lean`. Add relevant headline results to
that audit when introducing new mathematics. Update `STATUS.md` accurately.

Keep `.lake`, generated binaries, credentials, and copies of published papers
out of commits. Dependency upgrades should be separate, reviewable changes.

## Towards Mathlib

This library is not presented as a ready-made Mathlib submission. Extract small
general lemmas, check for existing equivalents, follow Mathlib's naming and
documentation conventions, reduce imports, and agree on suitable interfaces.
The goal is useful contributions, not merely moving the current source tree.

Contributions to the original project code are made under the Apache 2.0
licence in `LICENSE` unless explicitly agreed otherwise. The present private
review phase does not constitute a decision to publish the repositories.
